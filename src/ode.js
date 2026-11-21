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
// Steps chain: the enclosure of y(t0 + h) is the next step's Y0. Systems are
// handled componentwise without preconditioning, so enclosures of rotating
// systems grow over long spans (the wrapping effect); shorten spans or raise
// the order to keep them tight.
import { Rational } from "@ratmath/core";
import { Refinement } from "./refine.js";
import { Iv } from "./interval.js";
import { TaylorModel, Domain, DEFAULTS } from "./model.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ, lt, le, gt, max } from "./rat.js";
import { toAst, compileFloat, floatEnv, modelOf, toRational, freeVariables } from "./expr.js";

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
    const compiled = fs.map(compileFloat);
    const fenv = floatEnv(spec.params ?? {});
    floatF = (t, ys) => {
      const env = { ...fenv, [time]: t };
      vars.forEach((name, i) => (env[name] = ys[i]));
      return compiled.map((g) => g(env));
    };
  }
  return { system, n, y0, vars, time, modelF, floatF };
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

class ODESolution {
  constructor(pb, steps, complete, reason) {
    this.steps = steps; // [{ t0, t1, models }]
    this.complete = complete;
    this.reason = reason;
    this.system = pb.system;
    this.vars = pb.vars;
    Object.freeze(this);
  }
  get t0() {
    return this.steps[0]?.t0;
  }
  get t1() {
    return this.steps.at(-1)?.t1;
  }
  /** Certified enclosure(s) of y(t) for t in the solved span. */
  at(t) {
    const T = Iv.from(typeof t === "string" || typeof t === "number" ? q(t) : t);
    const parts = this.steps.filter((s) => le(s.t0, T.hi) && le(T.lo, s.t1));
    if (!parts.length) refuse("outside-domain", `t = ${T} is outside the solved span`);
    let acc = null;
    for (const s of parts) {
      const sub = new Iv(max(T.lo, s.t0), lt(T.hi, s.t1) ? T.hi : s.t1);
      const vals = s.models.map((m) => Iv.from(m.at(sub)));
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
  const steps = [];
  const span = until.subtract(t0);
  while (lt(t, until)) {
    if (steps.length >= maxSteps) {
      return { value: new ODESolution(pb, steps, false, `budget hit: ${maxSteps} steps`), via: "validated Picard steps (budget hit)" };
    }
    if (gt(t.add(h), until)) h = until.subtract(t);
    let step = tryStep(pb, t, h, Y, { order, bits });
    if (step) {
      // Width this step adds beyond what it inherited, per unit time. Halving
      // h shrinks the truncation part fast; the part inherited from Y0 grows
      // at a rate halving cannot change, so stop halving once it stops paying.
      step.rate = excessRate(step, Y);
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
    loose = null;
    tightenings = 0;
    h = step.t1.subtract(step.t0);
    steps.push({ t0: step.t0, t1: step.t1, models: step.models });
    t = step.t1;
    Y = step.models.map((m) => Iv.from(m.at(step.t1)));
    const done = Math.round(1000 * t.subtract(t0).divide(span).toNumber());
    yield { done, of: 1000, step: `t = ${t}`, partial: new ODESolution(pb, steps.slice(), false, "in progress") };
    // try a longer step next time, capped at the first one
    h = h.multiply(TWO);
    if (gt(h, h0)) h = h0;
  }
  return { value: new ODESolution(pb, steps, true), via: `${steps.length} validated Picard steps (Taylor models, order ${order})` };
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
  const pb = problem(spec);
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
