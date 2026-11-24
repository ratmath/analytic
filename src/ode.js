// Validated ODE steps with Taylor models (design note §2.4).
//
// For y' = F(t, y), y(t0) ∈ Y0 on the step T = [t0, t0 + h] (centre t0):
//
//   1. Picard-iterate polynomials to get P ≈ y on T (degree ≤ order).
//   2. Look for an interval I with  Φ(P + I) ⊂ P + I,  where
//        Φ(y)(t) = Y0 + ∫_{t0}^t F(s, y(s)) ds,
//      evaluated in Taylor-model arithmetic. Φ maps the closed convex set
//      { y : y(t) − P(t) ∈ I on T } into itself, so (Schauder; Picard–Lindelöf
//      for the smooth right-hand sides built here) the solution lies in it:
//      y(t) − P(t) ∈ I for every t in T. Then shrink I by re-applying Φ.
//   3. If no such I is found, halve h.
//
// Steps chain, and how they chain decides whether digits survive. Handing the
// box y(t0 + h) to the next step as its Y0 forgets that every solution in the
// box moves together: the width can then only grow, even for y′ = −y. So for
// formula right-hand sides each step also tracks the dependence on the initial
// value (the mean-value form used by Lohner's method):
//
//   y(t; y0) ∈ y(t; c) + J(t)·(y0 − c),    J(t) ⊇ ∂y(t)/∂y0 over the whole box,
//
// where y(t; c) is a validated step from the single point c (tight: only the
// truncation error) and J comes from the variational equation J′ = F_y(t, y)·J,
// J(t0) = I, solved together with y over the box. The set at t1 is kept as
// c′ + B′·r′ with a frame B′ from a QR factorisation of J(t1)·B, which keeps
// rotating systems from wrapping. Contracting problems now contract.
import { Rational } from "@ratmath/core";
import { Refinement } from "./refine.js";
import { Iv } from "./interval.js";
import { TaylorModel, Domain, DEFAULTS } from "./model.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ, lt, le, gt, max, roundDyadic } from "./rat.js";
import { toAst, compileFloat, floatEnv, modelOf, toRational, freeVariables, derivative as dAst } from "./expr.js";

const q = (v) => (typeof v === "string" || (typeof v === "number" && !Number.isInteger(v)) ? toRational(v) : toQ(v));

/**
 * Normalise a problem:
 *   f: "y^2 + t" | ["v", "-x"] | (t, y) => model(s)   (y: model, or array for systems)
 *   y0: value | interval | array of them
 *   vars: names of the unknowns (default "y", or y1..yn for systems)
 *   time: name of the independent variable (default "t")
 *   params: other names in string formulas
 *   float: (t, y) => number(s), preview for function right-hand sides
 */
function problem(spec) {
  const system = Array.isArray(spec.y0);
  const y0 = (system ? spec.y0 : [spec.y0]).map((v) => Iv.from(typeof v === "string" || typeof v === "number" ? q(v) : v));
  const n = y0.length;
  const time = spec.time ?? "t";
  const vars = spec.vars ?? (system ? y0.map((_, i) => `y${i + 1}`) : ["y"]);
  if (vars.length !== n) refuse("bad-ode", `vars has ${vars.length} names but y0 has ${n} values`);
  const params = {};
  for (const [k, val] of Object.entries(spec.params ?? {})) params[k] = typeof val === "string" || typeof val === "number" ? q(val) : val;

  let modelF;
  let floatF = null;
  let variational = null;
  if (typeof spec.f === "function") {
    modelF = (t, ys) => {
      const out = spec.f(t, system ? ys : ys[0]);
      return system ? out : [out];
    };
    if (spec.float) floatF = (t, ys) => (system ? spec.float(t, ys) : [spec.float(t, ys[0])]);
  } else {
    const fs = (system ? spec.f : [spec.f]).map(toAst);
    if (fs.length !== n) refuse("bad-ode", `f has ${fs.length} components but y0 has ${n} values`);
    for (const ast of fs) {
      for (const name of freeVariables(ast)) {
        if (name !== time && !vars.includes(name) && !(name in params)) refuse("unbound", `${name} has no value: pass it in params`);
      }
    }
    modelF = (t, ys) => {
      const env = { ...params, [time]: t };
      vars.forEach((name, i) => (env[name] = ys[i]));
      return fs.map((ast) => modelOf(ast, env, t));
    };
    // the variational system (y, J) with J′ = F_y(t, y)·J, when every partial derivative has a formula
    try {
      const dF = fs.map((ast) => vars.map((name) => dAst(ast, name)));
      variational = (t, all) => {
        const ys = all.slice(0, n);
        const env = { ...params, [time]: t };
        vars.forEach((name, i) => (env[name] = ys[i]));
        const A = dF.map((row) => row.map((ast) => modelOf(ast, env, t)));
        const out = fs.map((ast) => modelOf(ast, env, t));
        for (let i = 0; i < n; i++) {
          for (let k = 0; k < n; k++) {
            let acc = null;
            for (let j = 0; j < n; j++) {
              const term = lift(t.domain, A[i][j], { order: t.order, bits: t.bits }).multiply(all[n + j * n + k]);
              acc = acc ? acc.add(term) : term;
            }
            out.push(acc);
          }
        }
        return out;
      };
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
    }
    const compiled = fs.map(compileFloat);
    const fenv = floatEnv(spec.params ?? {});
    floatF = (t, ys) => {
      const env = { ...fenv, [time]: t };
      vars.forEach((name, i) => (env[name] = ys[i]));
      return compiled.map((g) => g(env));
    };
  }
  return { system, n, y0, vars, time, modelF, floatF, variational };
}

const lift = (D, val, s) => (val instanceof TaylorModel ? val : TaylorModel.constant(D, val, s));

/**
 * One validated step from t0 with initial enclosure Y0 (array of Iv). Returns
 * { t0, t1, models } or null when no enclosure was found for this h.
 */
function tryStep(pb, t0, h, Y0, { order, bits, attempts = 8 }) {
  const D = Domain(new Iv(t0, t0.add(h)), { centre: t0 });
  const s = { order, bits };
  const t = TaylorModel.x(D, s);
  const start = Y0.map((y) => TaylorModel.constant(D, y.toRationalInterval(), s));
  const F = (ys) => pb.modelF(t, ys).map((m) => lift(D, m, s));
  const phi = (ys) => F(ys).map((g, i) => start[i].add(g.integrate()));
  const strip = (m) => new TaylorModel({ domain: D, coeffs: m.coeffs, order, bits });
  try {
    // 1. polynomial approximation
    let P = Y0.map((y) => TaylorModel.constant(D, y.mid, s));
    for (let k = 0; k <= order; k++) P = phi(P).map(strip);
    // 2. find a self-mapping remainder
    const defect = (I) => {
      const Y = P.map((p, i) => new TaylorModel({ domain: D, coeffs: p.coeffs, rem: I[i], order, bits }));
      return phi(Y).map((T, i) => {
        const diff = new TaylorModel({ domain: D, coeffs: T.coeffs, order: 2 * order, bits }).subtract(P[i]);
        return diff.bound(2).add(T.rem);
      });
    };
    const tiny = new Rational(1n, 1n << BigInt(Math.min(bits, 200)));
    let I = defect(P.map(() => Iv.point(ZERO))).map((d) => inflate(d, TWO, tiny));
    for (let a = 0; a < attempts; a++) {
      const Dn = defect(I);
      if (Dn.every((d, i) => I[i].contains(d))) {
        // validated; tighten twice (each image still maps into itself)
        I = Dn;
        for (let k = 0; k < 2; k++) {
          const Dk = defect(I);
          if (!Dk.every((d, i) => I[i].contains(d))) break;
          I = Dk;
        }
        const models = P.map((p, i) => new TaylorModel({ domain: D, coeffs: p.coeffs, rem: I[i], order, bits, notes: ["ode step (Picard)"] }));
        return { t0, t1: t0.add(h), models };
      }
      I = I.map((iv, i) => inflate(iv.hull(Dn[i]), TWO, tiny));
      // a remainder far larger than the values themselves will not validate
      if (I.some((iv, i) => gt(iv.width, BIG.multiply(ONE.add(Y0[i].mag))))) return null;
    }
    return null;
  } catch (e) {
    if (e instanceof AnalyticError) return null; // a hypothesis failed on this step (range hit a singularity)
    throw e;
  }
}

function excessRate(step, Y) {
  let ex = ZERO;
  step.models.forEach((m, i) => (ex = max(ex, m.rem.width.subtract(Y[i].width))));
  step.excess = ex;
  return ex.divide(step.t1.subtract(step.t0));
}

const BIG = new Rational(1n << 10n);

function inflate(iv, factor, tiny) {
  const m = iv.mid;
  const r = iv.rad.multiply(factor).add(tiny);
  return new Iv(m.subtract(r), m.add(r));
}

// ---- sets as centre + frame·box (Lohner's representation) -----------------------

const ivZero = () => Iv.point(ZERO);
/** Hull of c + B·r, componentwise. */
function boxOf(set) {
  return set.c.map((ci, i) => set.B[i].reduce((acc, b, k) => acc.add(set.r[k].scale(b)), Iv.point(ci)));
}
/** Exact inverse of a rational matrix, or null when singular. */
function inverse(M) {
  const n = M.length;
  const A = M.map((row, i) => [...row, ...row.map((_, j) => (i === j ? ONE : ZERO))]);
  for (let c = 0; c < n; c++) {
    let p = c;
    for (let i = c + 1; i < n; i++) if (gt(A[i][c].abs(), A[p][c].abs())) p = i;
    if (A[p][c].numerator === 0n) return null;
    [A[c], A[p]] = [A[p], A[c]];
    const inv = A[c][c].reciprocal();
    A[c] = A[c].map((x) => x.multiply(inv));
    for (let i = 0; i < n; i++) {
      if (i === c || A[i][c].numerator === 0n) continue;
      const f = A[i][c];
      A[i] = A[i].map((x, j) => x.subtract(f.multiply(A[c][j])));
    }
  }
  return A.map((row) => row.slice(n));
}
const dyadic = (x) => new Rational(BigInt(Math.round(x * 2 ** 30)), 1n << 30n);
/**
 * A frame for the interval matrix M (≈ J·B): the orthogonal factor of a float
 * QR of its midpoint, longest column first. It is only a choice of
 * coordinates, so floats are fine here; everything proved with it is exact.
 */
function frameFor(M, r) {
  const n = M.length;
  if (n === 1) return [[ONE]];
  const cols = [];
  for (let k = 0; k < n; k++) {
    const v = M.map((row) => row[k].mid.toNumber() * Math.max(r[k].mag.toNumber(), 1e-300));
    cols.push(v);
  }
  cols.sort((a, b) => Math.hypot(...b) - Math.hypot(...a));
  const Q = [];
  for (const v0 of cols) {
    const v = v0.slice();
    for (const u of Q) {
      const d = u.reduce((acc, x, i) => acc + x * v[i], 0);
      for (let i = 0; i < n; i++) v[i] -= d * u[i];
    }
    const len = Math.hypot(...v);
    if (!(len > 1e-12 * Math.hypot(...v0)) || !Number.isFinite(len)) continue;
    Q.push(v.map((x) => x / len));
  }
  // complete with unit vectors if the columns were dependent
  for (let e = 0; Q.length < n && e < n; e++) {
    const v = Array.from({ length: n }, (_, i) => (i === e ? 1 : 0));
    for (const u of Q) {
      const d = u[e];
      for (let i = 0; i < n; i++) v[i] -= d * u[i];
    }
    const len = Math.hypot(...v);
    if (len > 1e-6) Q.push(v.map((x) => x / len));
  }
  if (Q.length < n) return null;
  // columns of the frame are the vectors of Q
  return Array.from({ length: n }, (_, i) => Q.map((u) => dyadic(u[i])));
}

/**
 * A step that tracks the dependence on the initial value. `set` is
 * { c, B, r }: the initial values c + B·r. Returns the step with its wide
 * models, the point solution, J, and the set at t1; or null.
 */
function tightStep(pb, t0, h, set, opts) {
  // the point solution is cheap and decides the step size; the wide solve
  // for J runs only once the step is accepted (complete())
  const n = pb.n;
  const point = tryStep(pb, t0, h, set.c.map((x) => Iv.point(x)), opts);
  if (!point) return null;
  const t1 = t0.add(h);
  let excess = ZERO;
  point.models.forEach((m) => (excess = max(excess, m.rem.width)));
  const complete = () => {
    const Y = boxOf(set);
    const eye = [];
    for (let i = 0; i < n; i++) for (let k = 0; k < n; k++) eye.push(Iv.point(i === k ? ONE : ZERO));
    const wide = tryStep({ modelF: pb.variational }, t0, h, [...Y, ...eye], opts);
    if (!wide) return null;
    const Jt = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, k) => Iv.from(wide.models[n + i * n + k].at(t1))));
    const yc = point.models.map((m) => Iv.from(m.at(t1)));
    const c1 = yc.map((v) => roundDyadic(v.mid, opts.bits));
    const z = yc.map((v, i) => v.sub(c1[i]));
    // M = J(t1)·B
    const M = Jt.map((row) => set.B[0].map((_, k) => row.reduce((acc, a, j) => acc.add(a.scale(set.B[j][k])), ivZero())));
    let B1 = frameFor(M, set.r);
    let inv = B1 && inverse(B1);
    if (!inv) {
      B1 = c1.map((_, i) => c1.map((_, k) => (i === k ? ONE : ZERO)));
      inv = B1;
    }
    // r′ = (B′⁻¹·M)·r + B′⁻¹·z
    const r1 = inv.map((row) => {
      let acc = ivZero();
      for (let k = 0; k < n; k++) {
        let m = ivZero();
        for (let j = 0; j < n; j++) m = m.add(M[j][k].scale(row[j]));
        acc = acc.add(m.mul(set.r[k]));
      }
      for (let j = 0; j < n; j++) acc = acc.add(z[j].scale(row[j]));
      return acc.roundOut(opts.bits);
    });
    return {
      t0, t1, models: wide.models.slice(0, n), excess,
      tight: { point: point.models, J: wide.models.slice(n), B: set.B, r: set.r },
      next: { c: c1, B: B1, r: r1 },
    };
  };
  return { t0, t1, excess, complete };
}

class ODESolution {
  constructor(pb, steps, complete, reason) {
    this.steps = steps; // [{ t0, t1, models }]
    this.complete = complete;
    this.reason = reason;
    this.system = pb.system;
    this.vars = pb.vars;
    // a backward solve runs in s = start − t; `steps` are then in s
    this.reversedFrom = pb.reverse ?? null;
    Object.freeze(this);
  }
  #time(sv) {
    return this.reversedFrom === null || sv === undefined ? sv : this.reversedFrom.subtract(sv);
  }
  /** Where the solve started. */
  get t0() {
    return this.#time(this.steps[0]?.t0);
  }
  /** How far it got (below t0 for a backward solve). */
  get t1() {
    return this.#time(this.steps.at(-1)?.t1);
  }
  /** Certified enclosure(s) of y(t) for t in the solved span. */
  at(t) {
    let T = Iv.from(typeof t === "string" || typeof t === "number" ? q(t) : t);
    if (this.reversedFrom !== null) T = new Iv(this.reversedFrom.subtract(T.hi), this.reversedFrom.subtract(T.lo));
    const parts = this.steps.filter((s) => le(s.t0, T.hi) && le(T.lo, s.t1));
    if (!parts.length) refuse("outside-domain", `t = ${typeof t === "object" ? Iv.from(t) : t} is outside the solved span`);
    let acc = null;
    for (const s of parts) {
      const sub = new Iv(max(T.lo, s.t0), lt(T.hi, s.t1) ? T.hi : s.t1);
      let vals = s.models.map((m) => Iv.from(m.at(sub)));
      if (s.tight) {
        // y(t) ∈ y(t; c) + (J(t)·B)·r, intersected with the direct enclosure
        const { point, J, B, r } = s.tight;
        const n = point.length;
        vals = vals.map((wide, i) => {
          let acc = Iv.from(point[i].at(sub));
          for (let k = 0; k < n; k++) {
            let m = Iv.point(ZERO);
            for (let j = 0; j < n; j++) m = m.add(Iv.from(J[i * n + j].at(sub)).scale(B[j][k]));
            acc = acc.add(m.mul(r[k]));
          }
          return acc.intersect(wide) ?? acc;
        });
      }
      acc = acc ? acc.map((a, i) => a.hull(vals[i])) : vals;
    }
    const out = acc.map((a) => a.toRationalInterval());
    return this.system ? out : out[0];
  }
  /** Enclosure(s) at the end of the solved span. */
  get final() {
    return this.at(this.t1);
  }
  describe() {
    const w = this.steps.at(-1)?.models.map((m) => m.rem.width.toNumber().toExponential(2)).join(", ");
    return `${this.steps.length} validated steps on [${this.t0}, ${this.t1}]${this.complete ? "" : ` (stopped: ${this.reason})`}; last remainder widths ${w}`;
  }
}

function* solveStages(pb, opts) {
  const t0 = q(opts.t0 ?? 0);
  const until = q(opts.until);
  if (!gt(until, t0)) refuse("bad-ode", "until must be after t0");
  const order = opts.order ?? 10;
  const bits = opts.bits ?? DEFAULTS.bits;
  const maxSteps = opts.maxSteps ?? 400;
  const minStep = opts.minStep ? q(opts.minStep) : until.subtract(t0).divide(new Rational(1n << 20n));
  // a step is tight when it adds at most `tol` to the width it inherited
  const tol = opts.tol !== undefined ? q(opts.tol) : new Rational(1n, 1n << 40n);
  const h0 = opts.step ? q(opts.step) : until.subtract(t0);
  let h = h0;
  let loose = null; // latest validated-but-wide step at this t
  let tightenings = 0;
  const maxTightenings = opts.maxTightenings ?? 8;
  let t = t0;
  let Y = pb.y0;
  // the set of initial values as centre + frame·box, when the variational equation is available
  let set = null;
  if (pb.variational && opts.track !== false) {
    const c = pb.y0.map((v) => v.mid);
    set = { c, B: c.map((_, i) => c.map((_, k) => (i === k ? ONE : ZERO))), r: pb.y0.map((v, i) => v.sub(c[i])) };
  }
  const steps = [];
  const span = until.subtract(t0);
  while (lt(t, until)) {
    if (steps.length >= maxSteps) {
      return { value: new ODESolution(pb, steps, false, `budget hit: ${maxSteps} steps`), via: "validated Picard steps (budget hit)" };
    }
    if (gt(t.add(h), until)) h = until.subtract(t);
    let step = set ? tightStep(pb, t, h, set, { order, bits }) : tryStep(pb, t, h, Y, { order, bits });
    if (step) {
      // Width this step adds beyond what it inherited, per unit time. Halving
      // h shrinks the truncation part fast; the part inherited from Y0 grows
      // at a rate halving cannot change, so stop halving once it stops paying.
      // (With the initial value tracked, the step's own error is the width of
      // the point solution's remainder.)
      step.rate = set ? step.excess.divide(h) : excessRate(step, Y);
      if (!le(step.excess, tol)) {
        if (loose && gt(step.rate.multiply(TWO), loose.rate)) {
          step = loose; // halving did not help: keep the longer step
        } else if (tightenings < maxTightenings) {
          loose = step;
          tightenings++;
          h = h.divide(TWO);
          continue;
        }
      }
    } else if (loose) {
      step = loose; // smaller steps did not validate
    } else {
      h = h.divide(TWO);
    }
    if (!step) {
      if (lt(h, minStep)) {
        return { value: new ODESolution(pb, steps, false, `no enclosure with step ≥ ${minStep} at t = ${t}`), via: "validated Picard steps (stopped early)" };
      }
      continue;
    }
    if (step.complete) {
      const full = step.complete();
      if (!full) {
        // the box of initial values is too wide for this step length: shorten it
        h = step.t1.subtract(step.t0).divide(TWO);
        loose = null;
        if (lt(h, minStep)) {
          return { value: new ODESolution(pb, steps, false, `no enclosure with step ≥ ${minStep} at t = ${t}`), via: "validated Picard steps (stopped early)" };
        }
        continue;
      }
      step = full;
    }
    loose = null;
    tightenings = 0;
    h = step.t1.subtract(step.t0);
    steps.push({ t0: step.t0, t1: step.t1, models: step.models, tight: step.tight });
    t = step.t1;
    if (set) {
      set = step.next;
      Y = boxOf(set);
    } else Y = step.models.map((m) => Iv.from(m.at(step.t1)));
    const done = Math.round(1000 * t.subtract(t0).divide(span).toNumber());
    yield { done, of: 1000, step: `t = ${t}`, partial: new ODESolution(pb, steps.slice(), false, "in progress") };
    // try a longer step next time, capped at the first one
    h = h.multiply(TWO);
    if (gt(h, h0)) h = h0;
  }
  return { value: new ODESolution(pb, steps, true), via: `${steps.length} validated Picard steps (Taylor models, order ${order}${set ? ", initial value tracked" : ""})` };
}

/** Classical RK4 on doubles, for previews. */
function rk4(pb, t0, t1, steps) {
  const F = pb.floatF;
  const h = (t1 - t0) / steps;
  let y = pb.y0.map((v) => v.mid.toNumber());
  const ts = new Float64Array(steps + 1);
  const ys = pb.y0.map(() => new Float64Array(steps + 1));
  const put = (k, t) => {
    ts[k] = t;
    y.forEach((v, i) => (ys[i][k] = v));
  };
  put(0, t0);
  const axpy = (a, x, b) => a.map((v, i) => v + b * x[i]);
  for (let k = 1; k <= steps; k++) {
    const t = t0 + (k - 1) * h;
    const k1 = F(t, y);
    const k2 = F(t + h / 2, axpy(y, k1, h / 2));
    const k3 = F(t + h / 2, axpy(y, k2, h / 2));
    const k4 = F(t + h, axpy(y, k3, h));
    y = y.map((v, i) => v + (h / 6) * (k1[i] + 2 * k2[i] + 2 * k3[i] + k4[i]));
    put(k, t + h);
  }
  return { t: ts, y: pb.system ? ys : ys[0] };
}

/**
 * ode.solve({ f, y0, t0, until, order, step, vars, time, params, float, previewSteps })
 * → Refinement: quick = RK4 samples { t, y }, exact = ODESolution with
 * certified enclosures (.at(t), .final, .steps, .complete).
 */
export function solve(spec) {
  let pb = problem(spec);
  const start = q(spec.t0 ?? 0);
  if (lt(q(spec.until), start)) {
    // backward in time: with s = start − t, dy/ds = −F(start − s, y)
    const fwd = pb;
    const flip = (run) => (sv, ys) => {
      const st = { order: sv.order, bits: sv.bits };
      return run(sv.negate().add(start), ys).map((m) => lift(sv.domain, m, st).negate());
    };
    pb = { ...fwd, modelF: flip(fwd.modelF), variational: fwd.variational && flip(fwd.variational), reverse: start };
    return new Refinement(
      () => {
        if (!fwd.floatF) return { value: null, trust: "unsure" };
        const value = rk4(fwd, start.toNumber(), q(spec.until).toNumber(), spec.previewSteps ?? 200);
        const ys = fwd.system ? value.y : [value.y];
        return { value, trust: ys.every((a) => a.every(Number.isFinite)) ? "good" : "unsure" };
      },
      () => solveStages(pb, { ...spec, t0: 0, until: start.subtract(q(spec.until)) }),
    );
  }
  return new Refinement(
    () => {
      if (!pb.floatF) return { value: null, trust: "unsure" };
      const value = rk4(pb, q(spec.t0 ?? 0).toNumber(), q(spec.until).toNumber(), spec.previewSteps ?? 200);
      const ys = pb.system ? value.y : [value.y];
      const finite = ys.every((a) => a.every(Number.isFinite));
      return { value, trust: finite ? "good" : "unsure" };
    },
    () => solveStages(pb, spec),
  );
}

/** One validated step: { t0, t1, models } or throws when none is found for h. */
export function step(spec) {
  const pb = problem(spec);
  const t0 = q(spec.t0 ?? 0);
  const h = q(spec.step);
  const r = tryStep(pb, t0, h, pb.y0, { order: spec.order ?? 10, bits: spec.bits ?? DEFAULTS.bits });
  if (!r) refuse("no-enclosure", `no validated enclosure for a step of ${h} from t = ${t0}; try a smaller step`);
  return pb.system ? r : { ...r, model: r.models[0] };
}

export const ode = { solve, step, ODESolution };
