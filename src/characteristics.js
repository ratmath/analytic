// First-order equations u_t + c·u_x + k·u = s with u(x, 0) = f(x), solved along
// characteristics.
//
// A characteristic is a curve x(t) with dx/dt = c. Along it the equation is
// the ordinary one du/dt = s − k·u, so with constant k and s
//
//     u(x, t) = f(ξ)·e^(−kt) + s·(1 − e^(−kt))/k        (f(ξ) + s·t when k = 0)
//
// where ξ is the foot: the point of the line t = 0 the characteristic through
// (x, t) started from. What is left is to find the foot.
//
// * c constant:            ξ = x − c·t, a closed formula.
// * c = a·x + b:           ξ = (x + b/a)·e^(−at) − b/a, a closed formula.
// * c = c(x, t) otherwise: the foot is the value at time 0 of the validated
//   solution of dx/dt = c(x, t) run back from (x, t): an enclosure.
//   Characteristics of a speed that does not involve u never cross: two
//   solutions of one ordinary equation through the same point are the same.
// * c = c(u) (k = s = 0):  u is constant on the straight line
//   x = ξ + F(ξ)·t with F(ξ) = c(f(ξ)). The lines first cross at the
//   breaking time t_b = −1/min F′ (never, when F′ ≥ 0). Before that the foot
//   is the one root of ξ + F(ξ)·t = x, found by bisection after
//   1 + F′·t > 0 is proven on the bracket; at or after it the request is
//   refused, because the equation no longer has a single-valued solution.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ } from "./rat.js";
import { toAst, format, num, v as variable, op, call, toRational, simplify, derivative, constantRational, freeVariables } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { solve as odeSolve } from "./ode.js";
import { weakSign } from "./uniform.js";

const qOf = (x) => (x instanceof Rational ? x : typeof x === "string" || typeof x === "number" ? toRational(x) : toQ(x));
const subst = (t, name, by) => (t.type === "var" ? (t.name === name ? by : t) : t.args ? { ...t, args: t.args.map((a) => subst(a, name, by)) } : t);
const out = (iv) => iv.toRationalInterval();


/** An enclosure of the least value of the tree for the variable in [a, b]. */
function leastOn(ast, name, a, b, bits) {
  const enc = (l, r) => encloseAst(ast, { [name]: l.equals(r) ? Iv.point(l) : new Iv(l, r) }, bits);
  let upper = [a, b, a.add(b).divide(TWO)].map((p) => enc(p, p).hi).reduce((m, q) => (q.compareTo(m) < 0 ? q : m));
  let cells = [[a, b, enc(a, b).lo]];
  let lower = cells[0][2];
  const tol = new Rational(1n, 1n << 30n);
  for (let round = 0; round < 48 && upper.subtract(lower).compareTo(tol) > 0 && cells.length < 4096; round++) {
    const next = [];
    for (const [l, r] of cells) {
      const m = l.add(r).divide(TWO);
      const top = enc(m, m).hi;
      if (top.compareTo(upper) < 0) upper = top;
      for (const [p, q] of [[l, m], [m, r]]) next.push([p, q, enc(p, q).lo]);
    }
    cells = next.filter((c) => c[2].compareTo(upper) <= 0);
    lower = cells.map((c) => c[2]).reduce((m, q) => (q.compareTo(m) < 0 ? q : m));
  }
  return new Iv(lower, upper);
}

/** Whether the tree is > 0 for the variable throughout [a, b], shown by subdivision. */
function positiveOn(ast, name, a, b, bits, depth = 14) {
  let lo;
  try {
    lo = encloseAst(ast, { [name]: new Iv(a, b) }, bits).lo;
  } catch {
    lo = null;
  }
  if (lo !== null && lo.numerator > 0n) return true;
  if (depth === 0) return false;
  const m = a.add(b).divide(TWO);
  return positiveOn(ast, name, a, m, bits, depth - 1) && positiveOn(ast, name, m, b, bits, depth - 1);
}

class TransportSolution {
  constructor(spec) {
    Object.assign(this, spec);
  }
  /**
   * The solution at (x, t): { value, foot } with `foot` the starting point of
   * the characteristic through (x, t) and `value` an enclosure of u(x, t)
   * (one number when the arithmetic is exact).
   */
  at(xv, tv = 0) {
    const [X, T] = [qOf(xv), qOf(tv)];
    const foot = this._foot(X, T, this._bits).roundOut(this._bits);
    const f0 = foot.lo.equals(foot.hi) ? constantRational(this._initial, { [this.variables.x]: foot.lo }) : null;
    let val = f0 !== null ? Iv.point(f0) : encloseAst(this._initial, { [this.variables.x]: foot }, this._bits);
    const { k, s } = this._along;
    if (k.numerator !== 0n) {
      if (T.numerator !== 0n) {
        const E = encloseAst(toAst("exp(a_)"), { a_: Iv.point(k.multiply(T).negate()) }, this._bits);
        val = val.mul(E).add(Iv.point(ONE).sub(E).scale(s.divide(k)));
      }
    } else if (s.numerator !== 0n) val = val.add(Iv.point(s.multiply(T)));
    return { value: out(val.roundOut(this._bits)), foot: out(foot) };
  }
  /**
   * An enclosure of the left side minus the right side of the equation,
   * u_t + c·u_x + k·u − s, at a point, worked out by differentiating the
   * closed formula: 0 lies in it when the formula solves the equation there.
   * Only for the cases with a closed formula.
   */
  residual(xv, tv) {
    if (!this._residual) refuse("no-formula", "there is no closed formula to differentiate: compare .at() with a difference quotient instead");
    const { x, t } = this.variables;
    const env = { [x]: qOf(xv), [t]: qOf(tv) };
    const exact = constantRational(this._residual, env);
    if (exact !== null) return new RationalInterval(exact, exact);
    return out(encloseAst(this._residual, { [x]: Iv.point(env[x]), [t]: Iv.point(env[t]) }, this._bits));
  }
}

/**
 * u_t + speed·u_x + decay·u = source with u(x, 0) = initial.
 *
 *     transport({ speed: 2, initial: "exp(-x^2)" }).formula          // "exp(-(x - 2*t)^2)"
 *     transport({ speed: "u", initial: "exp(-x^2)", interval: [-3, 3] }).crossing.time
 *
 * `speed` is a number or a formula in x, t (linear equations) or in u alone
 * (the quasilinear case, with decay = source = 0). `decay` and `source` are
 * numbers. `interval: [a, b]` limits the starting points considered in the
 * quasilinear case, which is what lets the breaking time be computed.
 * `order` and `tol` go to the validated ODE solver that follows a
 * characteristic of a general c(x, t) (a smaller tol gives a tighter foot and
 * takes longer).
 */
export function transport({ speed, decay = 0, source = 0, initial, interval = null, digits = 12, order = 8, tol = "1e-8", x = "x", t = "t", u = "u" }) {
  if (initial === undefined || speed === undefined) refuse("bad-problem", "give the speed and the initial values");
  const c = simplify(toAst(typeof speed === "number" ? String(speed) : speed));
  const f = toAst(typeof initial === "number" ? String(initial) : initial);
  const k = constantRational(toAst(String(decay)));
  const s = constantRational(toAst(String(source)));
  if (k === null || s === null) refuse("bad-problem", "decay and source must be numbers");
  for (const name of freeVariables(f)) if (name !== x) refuse("unbound", `the initial values are a formula in ${x} alone, but ${name} appears`);
  const cv = freeVariables(c);
  for (const name of cv) if (![x, t, u].includes(name)) refuse("unbound", `${name} has no value: the speed is a formula in ${x}, ${t} or ${u}`);
  const bits = bitsForDigits(digits) + 32;
  const X = variable(x);
  const Tt = variable(t);
  const equation = `${u}_${t} + (${format(c)})*${u}_${x}${k.numerator === 0n ? "" : ` + ${k}*${u}`} = ${s}`;
  const base = { equation, variables: { x, t, u }, _initial: f, _along: { k, s }, _bits: bits };

  // u along the characteristic, as a tree in x and t, from the foot as a tree
  const formulaFrom = (footAst) => {
    let body = subst(f, x, footAst);
    if (k.numerator !== 0n) {
      const E = call("exp", op("neg", op("*", num(k), Tt)));
      body = op("*", body, E);
      if (s.numerator !== 0n) body = op("+", body, op("*", num(s.divide(k)), op("-", num(ONE), E)));
    } else if (s.numerator !== 0n) body = op("+", body, op("*", num(s), Tt));
    return simplify(body);
  };
  const residualOf = (U) => {
    let r = op("+", derivative(U, t), op("*", c, derivative(U, x)));
    if (k.numerator !== 0n) r = op("+", r, op("*", num(k), U));
    if (s.numerator !== 0n) r = op("-", r, num(s));
    return simplify(r);
  };
  const neverLinear = { never: true, time: null, reason: `the speed does not involve ${u}, so the characteristics are the solutions of one ordinary equation d${x}/d${t} = c and two of them never meet` };

  if (cv.has(u)) {
    // ---- quasilinear: c = c(u) ----
    if (cv.has(x) || cv.has(t)) refuse("unsupported", `a speed that involves ${u} together with ${x} or ${t} is not handled: the characteristics are then not straight lines`);
    if (k.numerator !== 0n || s.numerator !== 0n) refuse("unsupported", `with a speed that involves ${u}, decay and source must be 0 here`);
    const F = simplify(subst(c, u, f)); // the speed of the characteristic from ξ, in the variable x
    const dF = simplify(derivative(F, x));
    const G1 = (T) => op("+", num(ONE), op("*", dF, num(T))); // d/dξ of ξ + F(ξ)·T
    const [a, b] = interval ? interval.map(qOf) : [null, null];
    if (interval && a.compareTo(b) >= 0) refuse("bad-problem", "the interval must have a < b");
    const where = interval ? `starting points in [${a}, ${b}]` : "all starting points";
    let crossing;
    if (weakSign(dF, {}) >= 1 || (dF.type === "num" && dF.value.numerator >= 0n)) {
      crossing = { never: true, time: null, reason: `the speed F(ξ) = ${format(F)} of the characteristic from ξ never decreases (F′ = ${format(dF)} ≥ 0 everywhere), so later characteristics never catch earlier ones` };
    } else if (interval) {
      const m = leastOn(dF, x, a, b, bits);
      if (m.lo.numerator >= 0n) crossing = { never: true, time: null, reason: `F′ = ${format(dF)} ≥ 0 for ${where}, so those characteristics never cross` };
      else if (m.hi.numerator < 0n) {
        const time = new Iv(m.lo.reciprocal().negate(), m.hi.reciprocal().negate());
        crossing = { never: false, time: out(time), reason: `characteristics first cross at t = −1/min F′, with F(ξ) = ${format(F)} and min F′ in [${m.lo.toNumber()}, ${m.hi.toNumber()}] over ${where}` };
      } else crossing = { never: null, time: null, reason: `the least value of F′ over ${where} could not be separated from 0` };
    } else {
      crossing = { never: null, time: null, reason: `whether characteristics cross depends on the least value of F′ = ${format(dF)}; pass interval: [a, b] for the breaking time over starting points in [a, b]` };
    }
    return new TransportSolution({
      ...base,
      kind: "quasilinear",
      characteristics: `${x} = ξ + (${format(F)} at ${x} = ξ)*${t}: straight lines, ${u} constant on each`,
      foot: null,
      formula: null,
      implicit: `${u} = f(ξ) with ξ + (${format(F)} at ${x} = ξ)*${t} = ${x}`,
      crossing,
      _foot(xq, tq, bb) {
        if (tq.numerator < 0n) refuse("bad-point", `${t} must be ≥ 0`);
        if (tq.numerator === 0n) return Iv.point(xq);
        if (crossing.never === false && tq.compareTo(crossing.time.low) >= 0) {
          refuse("crossed", `characteristics have crossed by ${t} = ${tq} (the breaking time is about ${crossing.time.low.toNumber()}): the equation has no single-valued solution there`);
        }
        const G = (p) => encloseAst(F, { [x]: Iv.point(p) }, bb).scale(tq).add(Iv.point(p.subtract(xq)));
        let L;
        let R;
        if (interval) {
          [L, R] = [a, b];
          if (!(G(L).hi.numerator <= 0n && G(R).lo.numerator >= 0n)) refuse("outside", `no characteristic from a starting point in [${a}, ${b}] is shown to pass through (${xq}, ${tq})`);
        } else {
          let W = ONE;
          for (let i = 0; ; i++) {
            [L, R] = [xq.subtract(W), xq.add(W)];
            if (G(L).hi.numerator <= 0n && G(R).lo.numerator >= 0n) break;
            if (i > 60) refuse("no-bracket", `no starting point was bracketed for (${xq}, ${tq})`);
            W = W.multiply(TWO);
          }
        }
        if (crossing.never !== true && !positiveOn(G1(tq), x, L, R, bb)) {
          refuse("crossed", `1 + F′(ξ)*${t} > 0 could not be shown for ξ in [${L}, ${R}] at ${t} = ${tq}: characteristics may have crossed`);
        }
        // one root in [L, R], and ξ + F(ξ)t increases through it: bisect
        const tol = new Rational(1n, 1n << BigInt(bb));
        while (R.subtract(L).compareTo(tol) > 0) {
          const m = L.add(R).divide(TWO);
          const g = G(m);
          if (g.hi.numerator <= 0n) L = m;
          else if (g.lo.numerator >= 0n) R = m;
          else break;
        }
        return new Iv(L, R);
      },
    });
  }

  const cConst = constantRational(c);
  if (cConst !== null) {
    const footAst = simplify(op("-", X, op("*", num(cConst), Tt)));
    const U = formulaFrom(footAst);
    return new TransportSolution({
      ...base,
      kind: "constant speed",
      characteristics: `${format(footAst)} = const`,
      foot: format(footAst),
      formula: format(U),
      crossing: { never: true, time: null, reason: "the characteristics are parallel straight lines" },
      _residual: residualOf(U),
      _foot: (xq, tq) => Iv.point(xq.subtract(cConst.multiply(tq))),
    });
  }

  const a1 = constantRational(simplify(derivative(c, x)));
  const b1 = a1 !== null && a1.numerator !== 0n ? constantRational(simplify(subst(c, x, num(ZERO)))) : null;
  if (b1 !== null && !cv.has(t)) {
    // c = a·x + b: dx/dt = a·x + b gives x + b/a = (ξ + b/a)·e^(at)
    const shift = b1.divide(a1);
    const E = call("exp", op("neg", op("*", num(a1), Tt)));
    const footAst = simplify(op("-", op("*", op("+", X, num(shift)), E), num(shift)));
    const U = formulaFrom(footAst);
    return new TransportSolution({
      ...base,
      kind: "linear speed",
      characteristics: `${format(simplify(op("*", op("+", X, num(shift)), E)))} = const`,
      foot: format(footAst),
      formula: format(U),
      crossing: neverLinear,
      _residual: residualOf(U),
      _foot(xq, tq, bb) {
        if (tq.numerator === 0n) return Iv.point(xq);
        const e = encloseAst(toAst("exp(a_)"), { a_: Iv.point(a1.multiply(tq).negate()) }, bb);
        return e.scale(xq.add(shift)).add(Iv.point(shift.negate()));
      },
    });
  }

  // ---- c = c(x, t): the foot by a validated solve of dx/dt = c back to t = 0 ----
  return new TransportSolution({
    ...base,
    kind: "variable speed",
    characteristics: `solutions of d${x}/d${t} = ${format(c)}`,
    foot: null,
    formula: null,
    crossing: neverLinear,
    _foot(xq, tq) {
      if (tq.numerator === 0n) return Iv.point(xq);
      const sol = odeSolve({ f: format(c), vars: [x], time: t, y0: xq, t0: tq, until: 0, order, tol, track: false }).exact();
      if (!sol.complete) refuse("no-enclosure", `the characteristic through (${xq}, ${tq}) could not be followed back to ${t} = 0: ${sol.reason ?? "the validated solve stopped early"}`);
      return Iv.from(sol.at(0));
    },
  });
}

