// The three classical partial differential equations by separation of
// variables, with a proven bound for the part of the series left out; the
// wave equation by d'Alembert's formula; and Sturm-Liouville eigenvalues by
// shooting, each bracketed by two validated solutions.
//
// Every value is an enclosure of the true solution of the problem: finitely
// many terms with certified Fourier coefficients, widened by a bound on the
// tail that holds for the whole infinite series.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ } from "./rat.js";
import { toAst, format, compileFloat, num, v as variable, op, call, toRational, simplify, derivative, constantRational, freeVariables } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { fn } from "./fn.js";
import { fourier } from "./fourier.js";
import { quad1 } from "./quad.js";
import { solve as odeSolve } from "./ode.js";

const qOf = (x) => (x instanceof Rational ? x : typeof x === "string" || typeof x === "number" ? toRational(x) : toQ(x));
const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const ev = (text, env, bits) => encloseAst(typeof text === "string" ? toAst(text) : text, env, bits);
const pt = (q) => Iv.point(q);
const sym = (iv) => new Iv(iv.mag.negate(), iv.mag);
const out = (iv) => iv.toRationalInterval();
/** sup |f| on [a, b], enclosed from above */
function supAbs(f, a, b, variableName) {
  const r = fn(f, { variable: variableName, params: {} }).range([a, b]).exact();
  return Iv.from(r).mag;
}
const PI = (bits) => ev("pi", {}, bits);
const EXP = (iv, bits) => ev("exp(s_)", { s_: iv }, bits);
/** Σ_{n > N} ρⁿ = ρ^{N+1}/(1 − ρ) for an enclosure of ρ in (0, 1), from above */
function geometricTail(rho, N) {
  if (rho.hi.compareTo(ONE) >= 0) return null;
  return rho.hi.pow(N + 1).divide(ONE.subtract(rho.hi));
}

class SeriesSolution {
  constructor(spec) {
    Object.assign(this, spec);
  }
  /**
   * The solution at a point: { value, partial, tail } where `partial` encloses
   * the terms kept, `tail` bounds everything left out, and `value` is their
   * sum: an enclosure of the true solution.
   */
  at(...point) {
    const bits = this._bits;
    const { partial, tail } = this._at(point.map(qOf), bits);
    if (tail === null) return { value: null, partial: out(partial), tail: null };
    const t = Iv.sym(tail);
    return { value: out(partial.add(t).roundOut(bits)), partial: out(partial.roundOut(bits)), tail: new Rational(tail.numerator, tail.denominator) };
  }
  /** The terms kept, as a formula with decimal coefficients (for plotting). */
  formula(terms = this.terms, digits = 6) {
    return this._formula(Math.min(terms, this.terms), digits);
  }
}
const dec = (iv, digits) => {
  const m = Iv.from(iv).mid.toNumber();
  return Math.abs(m) < 10 ** -digits ? 0 : Number(m.toPrecision(digits));
};
const tidyText = (s) => s.replaceAll("+ -", "- ").replace(/(^|[^\d.])1\*/g, "$1").replaceAll("/1)", ")");

/**
 * u_t = k·u_xx on 0 < x < L with u(x, 0) = f(x) and
 *   ends: "fixed"      u = 0 at both ends (a sine series), or
 *   ends: "insulated"  u_x = 0 at both ends (a cosine series).
 *
 *     heat({ k: 1, length: 1, initial: "x*(1 - x)", terms: 8 }).at("1/2", "1/10")
 */
export function heat({ k = 1, length = 1, initial, ends = "fixed", terms = 8, digits = 10, x = "x" }) {
  const L = qOf(length);
  const kq = qOf(k);
  if (kq.numerator <= 0n || L.numerator <= 0n) refuse("bad-problem", "k and the length must be positive");
  const kind = ends === "fixed" ? "sine" : ends === "insulated" ? "cosine" : refuse("bad-problem", 'ends is "fixed" or "insulated"');
  const fs = fourier(initial, [0, L], { kind, terms, digits, variable: x }).exact();
  const coeff = kind === "sine" ? fs.b : fs.a;
  const B = supAbs(initial, ZERO, L, x).multiply(TWO); // |coefficient| ≤ (2/L)·∫|f| ≤ 2·sup|f|
  const bits = bitsForDigits(digits) + 32;
  const trig = kind === "sine" ? "sin" : "cos";
  return new SeriesSolution({
    equation: `u_t = ${kq}*u_xx`,
    kind,
    terms,
    length: L,
    k: kq,
    coefficients: coeff.slice(),
    modes: coeff.map((c, n) => ({ n, coefficient: c, rate: tidyText(`${kq}*(${n}*pi/${L})^2`) })).slice(kind === "sine" ? 1 : 0),
    _bits: bits,
    _at([xv, tv], b) {
      if (tv.numerator < 0n) refuse("bad-point", "the heat equation runs forward in time: t ≥ 0");
      const pi = PI(b);
      const w = pi.scale(L.reciprocal()); // π/L
      let s = kind === "cosine" ? Iv.from(coeff[0]).scale(Q(1, 2)) : pt(ZERO);
      for (let n = 1; n <= terms; n++) {
        const wn = w.scale(Q(n));
        const decay = EXP(wn.mul(wn).scale(kq.multiply(tv)).neg(), b);
        const shape = ev(`${trig}(s_)`, { s_: wn.scale(xv) }, b);
        s = s.add(Iv.from(coeff[n]).mul(decay).mul(shape)).roundOut(b + 16);
      }
      // |term n| ≤ B·e^{−c n²} ≤ B·ρⁿ with ρ = e^{−c(N+1)}, c = kπ²t/L²
      let tail = null;
      if (tv.numerator > 0n) {
        const c = w.mul(w).scale(kq.multiply(tv));
        const rho = EXP(c.scale(Q(terms + 1)).neg(), b);
        const g = geometricTail(rho, terms);
        tail = g === null ? null : B.multiply(g);
      }
      return { partial: s, tail };
    },
    _formula(N, d) {
      const parts = [];
      if (kind === "cosine") parts.push(`${dec(coeff[0], d) / 2}`);
      for (let n = 1; n <= N; n++) {
        const c = dec(coeff[n], d);
        if (c === 0) continue;
        parts.push(`${c}*exp(-${kq.multiply(Q(n * n)).divide(L.multiply(L))}*pi^2*t)*${trig}(${Q(n).divide(L)}*pi*${x})`);
      }
      return tidyText(parts.join(" + ")) || "0";
    },
  });
}

/**
 * Laplace's equation u_xx + u_yy = 0 on the rectangle 0 < x < a, 0 < y < b
 * with u = f(x) on the top edge y = b and u = 0 on the other three.
 */
export function laplaceRectangle({ width = 1, height = 1, top, terms = 8, digits = 10, x = "x" }) {
  const a = qOf(width);
  const b = qOf(height);
  const fs = fourier(top, [0, a], { kind: "sine", terms, digits, variable: x }).exact();
  const B = supAbs(top, ZERO, a, x).multiply(TWO);
  const bits = bitsForDigits(digits) + 32;
  return new SeriesSolution({
    equation: "u_xx + u_yy = 0",
    kind: "sine",
    terms,
    width: a,
    height: b,
    coefficients: fs.b.slice(),
    modes: fs.b.map((c, n) => ({ n, coefficient: c, shape: `sinh(${n}*pi*y/${a})/sinh(${n}*pi*${b}/${a})*sin(${n}*pi*${x}/${a})` })).slice(1),
    _bits: bits,
    _at([xv, yv], bb) {
      if (yv.numerator < 0n || yv.compareTo(b) > 0 || xv.numerator < 0n || xv.compareTo(a) > 0) refuse("bad-point", "the point is outside the rectangle");
      const w = PI(bb).scale(a.reciprocal());
      let s = pt(ZERO);
      for (let n = 1; n <= terms; n++) {
        const wn = w.scale(Q(n));
        const ratio = ev("sinh(p_)/sinh(q_)", { p_: wn.scale(yv), q_: wn.scale(b) }, bb);
        s = s.add(Iv.from(fs.b[n]).mul(ratio).mul(ev("sin(s_)", { s_: wn.scale(xv) }, bb))).roundOut(bb + 16);
      }
      // sinh(ny')/sinh(nb') ≤ e^{−n(b'−y')}/(1 − e^{−2b'}): a geometric tail below the top edge
      let tail = null;
      if (yv.compareTo(b) < 0) {
        const rho = EXP(w.scale(b.subtract(yv)).neg(), bb);
        const g = geometricTail(rho, terms);
        const fix = pt(ONE).sub(EXP(w.scale(b.multiply(TWO)).neg(), bb));
        tail = g === null ? null : B.multiply(g).divide(fix.lo);
      }
      return { partial: s, tail };
    },
    _formula(N, d) {
      const parts = [];
      for (let n = 1; n <= N; n++) {
        const c = dec(fs.b[n], d);
        if (c !== 0) parts.push(`${c}*sinh(${Q(n).divide(a)}*pi*y)/sinh(${Q(n).multiply(b).divide(a)}*pi)*sin(${Q(n).divide(a)}*pi*${x})`);
      }
      return tidyText(parts.join(" + ")) || "0";
    },
  });
}

/**
 * Laplace's equation on the disc r < R with u = f(θ) on the circle. The
 * boundary values are a formula in the angle (named "theta" unless told
 * otherwise); the point is given as (r, s) with θ = 2π·s, so that a rational
 * s names an exact direction.
 */
export function laplaceDisc({ radius = 1, boundary, terms = 8, digits = 10, angle = "theta" }) {
  const R0 = qOf(radius);
  // f as a function of s in [0, 1], θ = 2π s
  const inS = substituteAngle(boundary, angle);
  const fs = fourier(inS, [0, 1], { kind: "full", terms, digits, variable: "s_" }).exact();
  const B = supAbs(inS, ZERO, ONE, "s_").multiply(TWO);
  const bits = bitsForDigits(digits) + 32;
  return new SeriesSolution({
    equation: "u_rr + u_r/r + u_θθ/r² = 0",
    kind: "full",
    terms,
    radius: R0,
    coefficients: { a: fs.a.slice(), b: fs.b.slice() },
    /** the value at the centre is the mean of the boundary values */
    mean: out(Iv.from(fs.a[0]).scale(Q(1, 2))),
    _bits: bits,
    _at([rv, sv], bb) {
      if (rv.numerator < 0n || rv.compareTo(R0) > 0) refuse("bad-point", "the point is outside the disc");
      const rho = rv.divide(R0);
      const theta = PI(bb).scale(TWO.multiply(sv));
      let s = Iv.from(fs.a[0]).scale(Q(1, 2));
      let rn = ONE;
      for (let n = 1; n <= terms; n++) {
        rn = rn.multiply(rho);
        const ang = theta.scale(Q(n));
        const term = Iv.from(fs.a[n]).mul(ev("cos(s_)", { s_: ang }, bb)).add(Iv.from(fs.b[n]).mul(ev("sin(s_)", { s_: ang }, bb)));
        s = s.add(term.scale(rn)).roundOut(bb + 16);
      }
      const g = rho.compareTo(ONE) < 0 ? geometricTail(pt(rho), terms) : null;
      return { partial: s, tail: g === null ? null : B.multiply(TWO).multiply(g) };
    },
    _formula(N, d) {
      const parts = [`${dec(fs.a[0], d) / 2}`];
      for (let n = 1; n <= N; n++) {
        const [an, bn] = [dec(fs.a[n], d), dec(fs.b[n], d)];
        if (an !== 0) parts.push(`${an}*(r/${R0})^${n}*cos(${n}*${angle})`);
        if (bn !== 0) parts.push(`${bn}*(r/${R0})^${n}*sin(${n}*${angle})`);
      }
      return tidyText(parts.join(" + "));
    },
  });
}
function substituteAngle(f, angle) {
  const ast = toAst(f);
  const by = op("*", op("*", num(2), { type: "var", name: "pi" }), variable("s_"));
  const piTree = toAst("2*pi*s_");
  void by;
  const sub = (t) => (t.type === "var" && t.name === angle ? piTree : t.args ? { ...t, args: t.args.map(sub) } : t);
  return format(sub(ast));
}

/**
 * The wave equation u_tt = c²·u_xx with u(x, 0) = f(x), u_t(x, 0) = g(x):
 * on the whole line, or with { length: L } on 0 < x < L with fixed ends.
 *
 * Values come from d'Alembert's formula
 *     u(x, t) = (f(x − ct) + f(x + ct))/2 + (1/2c)·∫_{x−ct}^{x+ct} g,
 * which is exact (on an interval f and g are continued as odd functions of
 * period 2L), so `at` needs no series. `modes(N)` lists the standing waves
 * for comparison.
 */
export function wave({ c = 1, length = null, position = "0", velocity = "0", digits = 12, x = "x" }) {
  const cq = qOf(c);
  if (cq.numerator <= 0n) refuse("bad-problem", "the speed c must be positive");
  const L = length === null ? null : qOf(length);
  const bits = bitsForDigits(digits) + 32;
  const fAst = toAst(position);
  const gAst = toAst(velocity);
  const gZero = format(gAst) === "0";
  const tol = new Rational(1n, 10n ** BigInt(digits));
  // reduce s to [0, L] with a sign: the odd extension of period 2L
  const fold = (s) => {
    if (L === null) return { r: s, sign: 1 };
    const P2 = L.multiply(TWO);
    const kf = s.divide(P2);
    const floor = kf.numerator >= 0n ? kf.numerator / kf.denominator : -((-kf.numerator + kf.denominator - 1n) / kf.denominator);
    let r = s.subtract(P2.multiply(new Rational(floor))); // in [0, 2L)
    let sign = 1;
    if (r.compareTo(L) > 0) {
      r = P2.subtract(r);
      sign = -1;
    }
    return { r, sign };
  };
  const fAt = (s) => {
    const { r, sign } = fold(s);
    const val = encloseAst(fAst, { [x]: pt(r) }, bits);
    return sign < 0 ? val.neg() : val;
  };
  // G(s) = ∫_0^s of the extended g: even and 2L-periodic on an interval
  const GAt = (s) => {
    if (gZero) return pt(ZERO);
    if (L === null) {
      if (s.numerator === 0n) return pt(ZERO);
      const iv = s.numerator > 0n ? quad1(gAst, x, {}, ZERO, s, { tol, bits }).iv : quad1(gAst, x, {}, s, ZERO, { tol, bits }).iv.neg();
      return iv;
    }
    const { r } = fold(s);
    return r.numerator === 0n ? pt(ZERO) : quad1(gAst, x, {}, ZERO, r, { tol, bits }).iv;
  };
  return {
    equation: `u_tt = ${cq.multiply(cq)}*u_xx`,
    speed: cq,
    length: L,
    /** u(x, t), enclosed, by d'Alembert's formula */
    at(xv, tv) {
      const X = qOf(xv);
      const T = qOf(tv);
      if (L !== null && (X.numerator < 0n || X.compareTo(L) > 0)) refuse("bad-point", "x is outside the interval");
      const [lo, hi] = [X.subtract(cq.multiply(T)), X.add(cq.multiply(T))];
      const travelling = fAt(lo).add(fAt(hi)).scale(Q(1, 2));
      const fromVelocity = GAt(hi).sub(GAt(lo)).scale(cq.multiply(TWO).reciprocal());
      return out(travelling.add(fromVelocity).roundOut(bits));
    },
    /** the two travelling waves that make up the solution when g = 0 */
    travelling: gZero ? { right: format(substituteVar(fAst, x, `${x} - ${cq}*t`)), left: format(substituteVar(fAst, x, `${x} + ${cq}*t`)) } : null,
    /** the first N standing waves on an interval: { n, frequency, cos, sin } with certified coefficients */
    modes(N = 6) {
      if (L === null) refuse("bad-problem", "standing waves belong to the problem on an interval: pass length");
      const A = fourier(position, [0, L], { kind: "sine", terms: N, digits: Math.min(digits, 10), variable: x }).exact();
      const Bv = gZero ? null : fourier(velocity, [0, L], { kind: "sine", terms: N, digits: Math.min(digits, 10), variable: x }).exact();
      const pi = PI(bits);
      const res = [];
      for (let n = 1; n <= N; n++) {
        const omega = pi.scale(cq.multiply(Q(n)).divide(L));
        res.push({
          n,
          frequency: `${cq.multiply(Q(n)).divide(L)}*pi`,
          cos: A.b[n],
          sin: Bv ? out(Iv.from(Bv.b[n]).div(omega).roundOut(bits)) : new RationalInterval(ZERO, ZERO),
        });
      }
      return res;
    },
  };
}
function substituteVar(ast, name, text) {
  const by = toAst(text);
  const go = (t) => (t.type === "var" && t.name === name ? by : t.args ? { ...t, args: t.args.map(go) } : t);
  return go(ast);
}

/**
 * Eigenvalues of the Sturm-Liouville problem
 *     −(p·y′)′ + q·y = λ·w·y  on [a, b],   y(a) = y(b) = 0,
 * by shooting: y(b; λ) for the solution with y(a) = 0, y′(a) = 1 changes
 * sign at each eigenvalue. The sign changes are located in floating point
 * and then each is proven: validated solutions at the two ends of a small
 * interval of λ give y(b) of opposite signs, so an eigenvalue lies between.
 *
 * Returns [{ index, eigenvalue, proven }] with eigenvalue a RationalInterval.
 */
export function sturmLiouville({ p = "1", q = "0", w = "1", interval, count = 3, from = 0, to = 400, x = "x", width = "1e-6", certify = true, order = 10, tol = "1e-10" }) {
  const [a, b] = interval.map(qOf);
  const [pA, qA, wA] = [p, q, w].map((e) => toAst(typeof e === "number" ? String(e) : e));
  const pf = compileFloat(pA);
  const qf = compileFloat(qA);
  const wf = compileFloat(wA);
  // y′ = z/p, z′ = (q − λw)·y, with z = p·y′
  const shoot = (lam) => {
    const steps = 2000;
    const h = (b.toNumber() - a.toNumber()) / steps;
    let xv = a.toNumber();
    let y = 0;
    let z = pf({ [x]: xv });
    const f = (xx, yy, zz) => [zz / pf({ [x]: xx }), (qf({ [x]: xx }) - lam * wf({ [x]: xx })) * yy];
    for (let i = 0; i < steps; i++) {
      const k1 = f(xv, y, z);
      const k2 = f(xv + h / 2, y + (h / 2) * k1[0], z + (h / 2) * k1[1]);
      const k3 = f(xv + h / 2, y + (h / 2) * k2[0], z + (h / 2) * k2[1]);
      const k4 = f(xv + h, y + h * k3[0], z + h * k3[1]);
      y += (h / 6) * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]);
      z += (h / 6) * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]);
      xv += h;
    }
    return y;
  };
  const found = [];
  const lo0 = (typeof from === "number" ? from : toQ(from).toNumber());
  const hi0 = (typeof to === "number" ? to : toQ(to).toNumber());
  const scan = 800;
  let prev = shoot(lo0);
  let lamPrev = lo0;
  for (let i = 1; i <= scan && found.length < count; i++) {
    const lam = lo0 + ((hi0 - lo0) * i) / scan;
    const cur = shoot(lam);
    if (prev === 0 || prev * cur < 0) {
      let [l, r, fl] = [lamPrev, lam, prev];
      for (let it = 0; it < 60; it++) {
        const m = (l + r) / 2;
        const fm = shoot(m);
        if (fl * fm <= 0) r = m;
        else [l, fl] = [m, fm];
      }
      found.push((l + r) / 2);
    }
    prev = cur;
    lamPrev = lam;
  }
  const half = qOf(width).divide(TWO);
  const pT = format(pA);
  const rhs = [`z_/(${pT})`, `((${format(qA)}) - lam_*(${format(wA)}))*y_`];
  const endSign = (lam) => {
    const p0 = encloseAst(pA, { [x]: pt(a) }, 96);
    const sol = odeSolve({ f: rhs, vars: ["y_", "z_"], time: x, y0: [ZERO, p0.isPoint ? p0.lo : p0.toRationalInterval()], t0: a, until: b, params: { lam_: lam }, order, tol, track: false }).exact();
    if (!sol.complete) return null;
    const yb = sol.final[0];
    return yb.low.numerator > 0n ? 1 : yb.high.numerator < 0n ? -1 : null;
  };
  return found.map((est, index) => {
    const centre = toRational(est.toFixed(9));
    const lo = centre.subtract(half);
    const hi = centre.add(half);
    let proven = false;
    if (certify) {
      const s1 = endSign(lo);
      const s2 = s1 === null ? null : endSign(hi);
      proven = s1 !== null && s2 !== null && s1 !== s2;
    }
    return { index: index + 1, eigenvalue: new RationalInterval(lo, hi), estimate: est, proven };
  });
}

/**
 * The type of a second-order linear PDE A·u_xx + B·u_xy + C·u_yy + (lower
 * order) = 0 from the sign of the discriminant B² − 4AC: hyperbolic where it
 * is positive, parabolic where it is zero, elliptic where it is negative.
 *
 *     classifyPDE({ A: "y", B: "0", C: "1" })   // the Tricomi equation
 *
 * A, B and C may depend on x and y. → { discriminant, type, regions, at, on }:
 * `type` is the type everywhere when the discriminant is constant, else
 * null; `regions` gives the condition for each type (solved for the variable
 * when the discriminant is linear in one variable, as in "y < 0"); `at(x, y)`
 * is the type at a point, decided exactly for polynomial coefficients at
 * rational points and by a certified enclosure otherwise (null if that
 * cannot decide); `on([[x0, x1], [y0, y1]])` is the single type on a
 * rectangle when the enclosure proves one, else null.
 */
export function classifyPDE(coefficients, opts = {}) {
  const [xName, yName] = opts.variables ?? ["x", "y"];
  const { A = "0", B = "0", C = "0" } = Array.isArray(coefficients) ? { A: coefficients[0], B: coefficients[1], C: coefficients[2] } : coefficients;
  const [a, b, c] = [A, B, C].map((t) => toAst(typeof t === "number" ? String(t) : t));
  const disc = simplify(op("-", op("*", b, b), op("*", op("*", num(Q(4)), a), c)));
  const typeOf = (sign) => (sign > 0 ? "hyperbolic" : sign < 0 ? "elliptic" : "parabolic");
  const signOf = (iv) => (iv.lo.numerator > 0n ? 1 : iv.hi.numerator < 0n ? -1 : iv.isPoint ? 0 : null);
  const text = format(disc);
  const constant = constantRational(disc);
  let regions;
  if (constant !== null) {
    const t = typeOf(constant.numerator > 0n ? 1 : constant.numerator < 0n ? -1 : 0);
    regions = { hyperbolic: t === "hyperbolic" ? "everywhere" : "nowhere", parabolic: t === "parabolic" ? "everywhere" : "nowhere", elliptic: t === "elliptic" ? "everywhere" : "nowhere" };
  } else {
    regions = { hyperbolic: `${text} > 0`, parabolic: `${text} = 0`, elliptic: `${text} < 0` };
    const free = [...freeVariables(disc)];
    if (free.length === 1) {
      // linear in one variable: D = s·v + r, so D > 0 is v > −r/s (or v < −r/s when s < 0)
      const v = free[0];
      const s = constantRational(simplify(derivative(disc, v)));
      const r = constantRational(disc, { [v]: ZERO });
      if (s !== null && r !== null && s.numerator !== 0n) {
        const cut = r.negate().divide(s);
        const [above, below] = s.numerator > 0n ? ["hyperbolic", "elliptic"] : ["elliptic", "hyperbolic"];
        const side = { [above]: `${v} > ${cut}`, [below]: `${v} < ${cut}` };
        regions = { hyperbolic: side.hyperbolic, parabolic: `${v} = ${cut}`, elliptic: side.elliptic };
      }
    }
  }
  const evalAt = (env) => {
    const exact = constantRational(disc, env);
    if (exact !== null) return Iv.point(exact);
    return encloseAst(disc, Object.fromEntries(Object.entries(env).map(([k, q]) => [k, q instanceof Iv ? q : Iv.point(q)])), 120);
  };
  return {
    discriminant: text,
    type: constant === null ? null : regions.hyperbolic === "everywhere" ? "hyperbolic" : regions.elliptic === "everywhere" ? "elliptic" : "parabolic",
    regions,
    at(x, y) {
      const s = signOf(evalAt({ [xName]: qOf(x), [yName]: qOf(y) }));
      return s === null ? null : typeOf(s);
    },
    on([[x0, x1], [y0, y1]]) {
      const iv = encloseAst(disc, { [xName]: new Iv(qOf(x0), qOf(x1)), [yName]: new Iv(qOf(y0), qOf(y1)) }, 120);
      const s = signOf(iv);
      return s === null ? null : typeOf(s);
    },
  };
}
export { classifyPDE as classify };
