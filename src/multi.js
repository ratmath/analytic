// Functions of several variables: certified values, gradients and Hessians,
// ranges over boxes and regions, multiple integrals, critical points, and
// line and surface integrals.
//
//   const f = field("x^2*y + sin(x*y)", ["x", "y"]);
//   f.gradient()                         // [2x·y + cos(x·y)·y, x² + cos(x·y)·x]
//   f.value({ x: 1, y: "1/2" })          // Refinement: float, then an interval
//   f.range({ x: [0, 1], y: [0, 1] })    // Refinement: enclosure of the range
//   f.integral("0:x:1 && 0:y:x")         // over a Core MultiRegion (a triangle)
//   f.integral({ x: [0, 1], y: ["0", "x^2"] })   // curved bounds, in order
//   f.criticalPoints({ x: [-2, 2], y: [-2, 2] }) // proven, classified
//
// The engine is a second-order interval jet: for an expression and a box it
// returns enclosures of the value, every first partial and every second
// partial over the whole box. Ranges use the mean value form, integrals the
// midpoint rule with the Hessian as the proven error, critical points a
// Krawczyk test on the gradient.

import { Rational, RationalInterval, MultiRegion } from "@ratmath/core";
import { Refinement } from "@ratmath/core/refine";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ, lt, le, gt, ge, max, min } from "./rat.js";
import { toAst, format, compileFloat, floatEnv, derivative, simplify, freeVariables, constantRational, toRational, num, v as variable, op, call } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { AnalyticFunction } from "./fn.js";

const q = (x) => (typeof x === "string" ? toRational(x) : typeof x === "number" && !Number.isInteger(x) ? toRational(x) : toQ(x));
const R = (iv, bits) => iv.roundOut(bits, 6000);
const IZ = Iv.point(ZERO);
const HALF = new Rational(1n, 2n);

/**
 * The same tree with equal subtrees made one object, so the evaluators
 * (which remember each node they have seen) work a repeated sin(u) out once.
 */
export function share(ast) {
  const seen = new Map();
  const ids = new Map();
  const go = (node) => {
    let key;
    let made = node;
    if (node.type === "num") key = `n${node.value}`;
    else if (node.type === "var" || node.type === "const") key = `${node.type[0]}${node.name}`;
    else {
      const args = node.args.map(go);
      key = `${node.type === "op" ? "o" : "c"}${node.op ?? node.name}(${args.map((a) => ids.get(a)).join(",")})`;
      if (args.some((a, i) => a !== node.args[i])) made = { ...node, args };
    }
    const have = seen.get(key);
    if (have) return have;
    seen.set(key, made);
    ids.set(made, ids.size);
    return made;
  };
  return go(ast);
}

// ---- jets ------------------------------------------------------------------------------------

const unaryCache = new Map();
/** f(u), f′(u), f″(u) as trees in u, for a one-argument tree in u. */
function unaryDerivatives(key, make) {
  let r = unaryCache.get(key);
  if (!r) {
    const f = make(variable("u"));
    const d1 = simplify(derivative(f, "u"));
    const d2 = simplify(derivative(d1, "u"));
    unaryCache.set(key, (r = { f, d1, d2, higher: [f, d1, d2] }));
  }
  return r;
}
/** The tree of the k-th derivative in u (built on demand). */
function unaryOrder(trees, k) {
  while (trees.higher.length <= k) trees.higher.push(simplify(derivative(trees.higher[trees.higher.length - 1], "u")));
  return trees.higher[k];
}

const FACT = [1n];
for (let k = 1n; k <= 40n; k++) FACT.push(FACT[FACT.length - 1] * k);


/**
 * Taylor coefficients F₀ … F_K of a one-argument function about every point
 * of the interval a0: F_k encloses f⁽ᵏ⁾(u)/k! for u in a0. The common
 * functions have closed forms that share their evaluations; the rest use
 * derivative trees. Throws AnalyticError where a derivative has no enclosure.
 */
function unaryTaylor(key, make, a0, K, env, bits) {
  const at = { ...env, u: a0 };
  const U = variable("u");
  const scaleK = (iv, k) => iv.scale(new Rational(1n, FACT[k]));
  if (key === "sqrt") key = "pow 1/2";
  if (key === "exp") {
    const e = encloseAst(call("exp", U), at, bits);
    return Array.from({ length: K + 1 }, (_, k) => scaleK(e, k));
  }
  if (key === "sin" || key === "cos") {
    const sn = encloseAst(call("sin", U), at, bits);
    const cs = encloseAst(call("cos", U), at, bits);
    // derivatives of sin cycle sin, cos, −sin, −cos; cos starts one step later
    const cycle = [sn, cs, sn.neg(), cs.neg()];
    const shift = key === "sin" ? 0 : 1;
    return Array.from({ length: K + 1 }, (_, k) => scaleK(cycle[(k + shift) % 4], k));
  }
  if (key === "sinh" || key === "cosh") {
    const sh = encloseAst(call("sinh", U), at, bits);
    const ch = encloseAst(call("cosh", U), at, bits);
    return Array.from({ length: K + 1 }, (_, k) => scaleK((k % 2 === 0) === (key === "sinh") ? sh : ch, k));
  }
  if (key === "recip" || key === "log") {
    const out = [encloseAst(key === "log" ? call("log", U) : op("/", num(1), U), at, bits)];
    const inv = key === "log" ? encloseAst(op("/", num(1), U), at, bits) : out[0];
    // log: F_k = (−1)^(k−1)/(k·u^k); 1/u: F_k = (−1)^k/u^(k+1)
    let power = key === "log" ? Iv.point(ONE) : inv;
    for (let k = 1; k <= K; k++) {
      power = R(power.mul(inv), bits);
      out.push(key === "log" ? power.scale(new Rational(k % 2 ? 1n : -1n, BigInt(k))) : (k % 2 ? power.neg() : power));
    }
    return out;
  }
  if (key.startsWith("pow ")) {
    const c = toRational(key.slice(4));
    if (c.denominator === 1n && c.numerator >= 0n && c.numerator <= 64n) {
      // u^n: F_k = C(n, k)·u^(n−k)
      const n = Number(c.numerator);
      const out = [];
      let binom = 1n;
      for (let k = 0; k <= K; k++) {
        out.push(k > n ? IZ : R(a0.pow(n - k).scale(new Rational(binom)), bits));
        binom = (binom * BigInt(n - k)) / BigInt(k + 1);
      }
      return out;
    }
    // u^c: F_k = C(c, k)·u^c/u^k with the generalised binomial coefficient
    if (le(a0.lo, ZERO) && ge(a0.hi, ZERO)) refuse("not-smooth", "a fractional power has no derivative at 0");
    const inv = R(encloseAst(op("/", num(1), U), at, bits), bits);
    let power = R(encloseAst(op("^", U, num(c)), at, bits), bits);
    const out = [];
    let binom = ONE;
    for (let k = 0; k <= K; k++) {
      out.push(power.scale(binom));
      power = R(power.mul(inv), bits);
      binom = binom.multiply(c.subtract(new Rational(BigInt(k)))).divide(new Rational(BigInt(k + 1)));
    }
    return out;
  }
  const trees = unaryDerivatives(key, make);
  return Array.from({ length: K + 1 }, (_, k) => scaleK(encloseAst(unaryOrder(trees, k), at, bits), k));
}

/**
 * Taylor coefficients c₀ … c_K of the tree in one variable, enclosed over the
 * whole box `env`: c_k contains (∂ᵏ/∂nameᵏ) f / k! at every point of the box.
 * Returns null where a derivative cannot be enclosed (a kink, an end of a domain).
 * With `scale` = h the coefficients are those in s for name = centre + h·s,
 * that is c_k·h^k, which keeps them near the size of f on wide boxes.
 */
export function taylorAlong(ast, env, name, bits = 64, K = 4, scale = null) {
  // Coefficients are pairs [lo, hi] of BigInt at the fixed scale 2^−P, so the
  // products of a series cost shifts instead of gcds. Each function is
  // applied by its series recurrence (exp: j·b_j = Σ i·a_i·b_(j−i), and the
  // like), which keeps every term at the size of the result.
  const P = BigInt(bits + 64);
  const UNIT = 1n << P;
  const floor = (r) => {
    const n = r.numerator << P;
    const d = r.denominator;
    const quotient = n / d;
    return n < 0n && n % d !== 0n ? quotient - 1n : quotient;
  };
  const from = (iv) => [floor(iv.lo), -floor(iv.hi.negate())];
  const toIv = ([lo, hi]) => new Iv(new Rational(lo, UNIT), new Rational(hi, UNIT));
  const Z = [0n, 0n];
  const U1 = [UNIT, UNIT];
  const isZero = (x) => x[0] === 0n && x[1] === 0n;
  const zero = () => new Array(K + 1).fill(Z);
  const fdiv = (n, d) => { const quotient = n / d; return n % d !== 0n && (n < 0n) !== (d < 0n) ? quotient - 1n : quotient; };
  const cdiv = (n, d) => -fdiv(-n, d);
  const memo = new Map();
  let smooth = true;
  const go = (node) => {
    if (node.type !== "op" && node.type !== "call") return eval1(node);
    let r = memo.get(node);
    if (r === undefined) memo.set(node, (r = eval1(node)));
    return r;
  };
  const constant = (val) => { const c = zero(); c[0] = val; return c; };
  const isConstant = (a) => a.every((x, k) => k === 0 || isZero(x));
  /** Σ_{i=from..to} w(i)·x[i]·y[j−i] at the scale 2^−2P, as [lo, hi]. */
  const wsum = (x, y, j, lo0, hi0, w) => {
    let lo = 0n;
    let hi = 0n;
    for (let i = lo0; i <= hi0; i++) {
      const p = x[i];
      const q2 = y[j - i];
      if (isZero(p) || isZero(q2)) continue;
      const weight = w ? w(i) : 1n;
      if (weight === 0n) continue;
      let least;
      let most;
      if (p[0] >= 0n && q2[0] >= 0n) { least = p[0] * q2[0]; most = p[1] * q2[1]; } else {
        const p1 = p[0] * q2[0];
        const p2 = p[0] * q2[1];
        const p3 = p[1] * q2[0];
        const p4 = p[1] * q2[1];
        least = p1 < p2 ? p1 : p2;
        if (p3 < least) least = p3;
        if (p4 < least) least = p4;
        most = p1 > p2 ? p1 : p2;
        if (p3 > most) most = p3;
        if (p4 > most) most = p4;
      }
      if (weight > 0n) { lo += least * weight; hi += most * weight; } else { lo += most * weight; hi += least * weight; }
    }
    return [lo, hi];
  };
  /** Rounds a 2^−2P sum to 2^−P, after dividing by the positive integer d. */
  const settle = ([lo, hi], d = 1n) => [fdiv(lo, d << P), cdiv(hi, d << P)];
  const mulI = (x, y) => settle(wsum([x], [y], 0, 0, 0));
  const recipI = (y) => {
    if (y[0] <= 0n && y[1] >= 0n) refuse("division-by-zero", "division by an interval that contains 0");
    const sq = UNIT * UNIT;
    return y[0] > 0n ? [fdiv(sq, y[1]), cdiv(sq, y[0])] : [fdiv(sq, y[1]), cdiv(sq, y[0])];
  };
  const mul = (a, b) => {
    const out = [];
    for (let k = 0; k <= K; k++) out.push(settle(wsum(a, b, k, 0, k)));
    return out;
  };
  const neg = (a) => a.map((x) => [-x[1], -x[0]]);
  const addS = (a, b) => a.map((x, k) => [x[0] + b[k][0], x[1] + b[k][1]]);
  const big = (i) => BigInt(i);
  const value = (a0, make) => from(encloseAst(make(variable("u")), { ...env, u: toIv(a0) }, bits));
  /** b with b′ = a′·g: j·b_j = Σ_{i=1..j} i·a_i·g_(j−i). g may be filled in as b grows. */
  const integrate = (a, b0, gOf) => {
    const b = zero();
    b[0] = b0;
    const g = [];
    for (let j = 1; j <= K; j++) {
      g[j - 1] = gOf(b, j - 1);
      b[j] = settle(wsum(a, g, j, 1, j, big), big(j));
    }
    return b;
  };
  const recipS = (a) => {
    const inv = recipI(a[0]);
    const b = zero();
    b[0] = inv;
    for (let j = 1; j <= K; j++) {
      const t = settle(wsum(a, b, j, 1, j));
      b[j] = mulI([-t[1], -t[0]], inv);
    }
    return b;
  };
  const expS = (a) => integrate(a, value(a[0], (u) => call("exp", u)), (b, i) => b[i]);
  const logS = (a) => {
    const b = zero();
    b[0] = value(a[0], (u) => call("log", u));
    const inv = recipI(a[0]);
    for (let j = 1; j <= K; j++) {
      // j·a_0·b_j = j·a_j − Σ_{i=1..j−1} i·b_i·a_(j−i)
      const t = j > 1 ? settle(wsum(b, a, j, 1, j - 1, big), big(j)) : Z;
      b[j] = mulI([a[j][0] - t[1], a[j][1] - t[0]], inv);
    }
    return b;
  };
  const powS = (a, c) => {
    if (c.denominator === 1n && c.numerator >= 0n && c.numerator <= 64n) {
      let out = constant(U1);
      let base = a;
      for (let n = c.numerator; n > 0n; n >>= 1n) {
        if (n & 1n) out = mul(out, base);
        if (n > 1n) base = mul(base, base);
      }
      return out;
    }
    if (a[0][0] <= 0n && a[0][1] >= 0n) refuse("not-smooth", "a fractional or negative power has no derivative at 0");
    const b = zero();
    b[0] = value(a[0], (u) => op("^", u, num(c)));
    const inv = recipI(a[0]);
    for (let j = 1; j <= K; j++) {
      // j·a_0·b_j = Σ_{i=1..j} (c·i − (j − i))·a_i·b_(j−i)
      const t = settle(wsum(a, b, j, 1, j, (i) => c.numerator * big(i) - c.denominator * big(j - i)), big(j) * c.denominator);
      b[j] = mulI(t, inv);
    }
    return b;
  };
  const trig = (a, hyperbolic) => {
    const s = zero();
    const c = zero();
    s[0] = value(a[0], (u) => call(hyperbolic ? "sinh" : "sin", u));
    c[0] = value(a[0], (u) => call(hyperbolic ? "cosh" : "cos", u));
    for (let j = 1; j <= K; j++) {
      s[j] = settle(wsum(a, c, j, 1, j, big), big(j));
      const t = settle(wsum(a, s, j, 1, j, big), big(j));
      c[j] = hyperbolic ? t : [-t[1], -t[0]];
    }
    return [s, c];
  };
  const one = () => constant(U1);
  const square = (a) => mul(a, a);
  /** The series of a one-argument function of the series a. */
  const apply = (fname, a) => {
    switch (fname) {
      case "exp": return expS(a);
      case "log": return logS(a);
      case "sin": return trig(a, false)[0];
      case "cos": return trig(a, false)[1];
      case "sinh": return trig(a, true)[0];
      case "cosh": return trig(a, true)[1];
      case "sqrt": return powS(a, new Rational(1n, 2n));
      case "cbrt": return powS(a, new Rational(1n, 3n));
      case "log1p": return logS(addS(one(), a));
      case "tan":
      case "tanh": {
        // b′ = a′·(1 ± b²), the square filled in as b grows
        const sq = [];
        return integrate(a, value(a[0], (u) => call(fname, u)), (b, i) => {
          sq[i] = settle(wsum(b, b, i, 0, i));
          const t = fname === "tan" ? sq[i] : [-sq[i][1], -sq[i][0]];
          return i === 0 ? [t[0] + UNIT, t[1] + UNIT] : t;
        });
      }
      case "atan": {
        const g = recipS(addS(one(), square(a)));
        return integrate(a, value(a[0], (u) => call("atan", u)), (_b, i) => g[i]);
      }
      case "asin":
      case "acos": {
        const g = powS(addS(one(), neg(square(a))), new Rational(-1n, 2n));
        const signed = fname === "asin" ? g : neg(g);
        return integrate(a, value(a[0], (u) => call(fname, u)), (_b, i) => signed[i]);
      }
      case "erf": {
        const factor = from(encloseAst(op("/", num(2), call("sqrt", { type: "const", name: "pi" })), {}, bits));
        const g = mul(constant(factor), expS(neg(square(a))));
        return integrate(a, value(a[0], (u) => call("erf", u)), (_b, i) => g[i]);
      }
    }
    return refuse("bad-expression", `cannot expand ${fname}`);
  };
  /** apply(), with the value kept and `smooth` cleared where a derivative does not exist (sqrt at 0). */
  const compose = (a, fname, make, run) => {
    if (isConstant(a)) return constant(value(a[0], make));
    try {
      return run();
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      const out = constant(value(a[0], make)); // throws again where even the value is undefined
      smooth = false;
      return out;
    }
  };
  const eval1 = (node) => {
    switch (node.type) {
      case "num":
        return constant(from(Iv.point(node.value)));
      case "const":
        return constant(from(encloseAst(node, env, bits)));
      case "var": {
        const val = env[node.name];
        if (val === undefined) refuse("unbound", `no value for ${node.name}`);
        const c = constant(from(val));
        // with a scale h the series is in s where name = centre + h·s
        if (node.name === name) c[1] = scale ? from(Iv.point(scale)) : U1;
        return c;
      }
      case "op": {
        if (node.op === "neg") return neg(go(node.args[0]));
        if (node.op === "+") return addS(go(node.args[0]), go(node.args[1]));
        if (node.op === "-") return addS(go(node.args[0]), neg(go(node.args[1])));
        if (node.op === "*") return mul(go(node.args[0]), go(node.args[1]));
        if (node.op === "/") {
          const b = go(node.args[1]);
          return mul(go(node.args[0]), compose(b, "recip", (u) => op("/", num(1), u), () => recipS(b)));
        }
        if (node.op === "^") {
          const a = go(node.args[0]);
          const c = constantRational(node.args[1]);
          if (c !== null) return compose(a, "pow", (u) => op("^", u, num(c)), () => powS(a, c));
          const logu = compose(a, "log", (u) => call("log", u), () => logS(a));
          const e = mul(go(node.args[1]), logu);
          return compose(e, "exp", (u) => call("exp", u), () => expS(e));
        }
        break;
      }
      case "call": {
        if (node.name === "min" || node.name === "max" || node.name === "abs") {
          const a = go(node.args[0]);
          if (node.name === "abs") {
            if (a[0][0] >= 0n) return a;
            if (a[0][1] <= 0n) return neg(a);
            smooth = false;
            return constant([0n, -a[0][0] > a[0][1] ? -a[0][0] : a[0][1]]);
          }
          const b = go(node.args[1]);
          const isMin = node.name === "min";
          if (isMin ? a[0][1] <= b[0][0] : a[0][0] >= b[0][1]) return a;
          if (isMin ? b[0][1] <= a[0][0] : b[0][0] >= a[0][1]) return b;
          smooth = false;
          const pick = (x, y) => ((isMin ? x < y : x > y) ? x : y);
          return constant([pick(a[0][0], b[0][0]), pick(a[0][1], b[0][1])]);
        }
        const fname = node.name === "ln" ? "log" : node.name;
        const a = go(node.args[0]);
        return compose(a, fname, (u) => call(fname, u), () => apply(fname, a));
      }
    }
    return refuse("bad-expression", `cannot evaluate ${node.type} ${node.op ?? node.name ?? ""}`);
  };
  const out = go(ast);
  return smooth ? out.map(toIv) : null;
}

/**
 * Value, gradient and Hessian enclosures of the tree over the box `env`
 * (names → Iv), with respect to `names`. `order` is 0, 1 or 2. `smooth` is
 * false when a derivative could not be enclosed on the box (a kink of abs,
 * min or max inside it, sqrt at 0): the value is still valid, the
 * derivatives are not to be used.
 */
export function jet(ast, env, names, bits = 64, order = 2) {
  const n = names.length;
  const index = new Map(names.map((name, i) => [name, i]));
  let smooth = true;
  const zeros = () => new Array(n).fill(IZ);
  const zeroH = () => Array.from({ length: n }, zeros);
  const constant = (val) => ({ v: val, g: order >= 1 ? zeros() : null, h: order >= 2 ? zeroH() : null });
  const memo = new Map();
  const go = (node) => {
    if (node.type !== "op" && node.type !== "call") return eval1(node);
    let r = memo.get(node);
    if (r === undefined) memo.set(node, (r = eval1(node)));
    return r;
  };
  const add = (a, b, sign) => ({
    v: R(sign > 0 ? a.v.add(b.v) : a.v.sub(b.v), bits),
    g: order >= 1 ? a.g.map((x, i) => R(sign > 0 ? x.add(b.g[i]) : x.sub(b.g[i]), bits)) : null,
    h: order >= 2 ? a.h.map((row, i) => row.map((x, j) => R(sign > 0 ? x.add(b.h[i][j]) : x.sub(b.h[i][j]), bits))) : null,
  });
  const mul = (a, b) => ({
    v: R(a.v.mul(b.v), bits),
    g: order >= 1 ? a.g.map((x, i) => R(x.mul(b.v).add(a.v.mul(b.g[i])), bits)) : null,
    h: order >= 2
      ? a.h.map((row, i) => row.map((x, j) => (j < i ? null : R(x.mul(b.v).add(a.g[i].mul(b.g[j])).add(a.g[j].mul(b.g[i])).add(a.v.mul(b.h[i][j])), bits))))
        .map((row, i, all) => row.map((x, j) => (j < i ? all[j][i] : x)))
      : null,
  });
  /** Compose with a one-argument function (`make` builds its tree from a tree in u). */
  const compose = (a, key, make) => {
    if (order === 0) return { v: R(encloseAst(make(variable("u")), { ...env, u: a.v }, bits), bits), g: null, h: null };
    let F;
    try {
      F = unaryTaylor(key, make, a.v, order, env, bits);
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      smooth = false;
      F = [encloseAst(make(variable("u")), { ...env, u: a.v }, bits), IZ, IZ];
    }
    const d1 = F[1];
    const d2 = order >= 2 ? F[2].scale(TWO) : IZ;
    return {
      v: R(F[0], bits),
      g: a.g.map((x) => R(d1.mul(x), bits)),
      h: order >= 2 ? a.h.map((row, i) => row.map((x, j) => R(d2.mul(a.g[i]).mul(a.g[j]).add(d1.mul(x)), bits))) : null,
    };
  };
  const eval1 = (node) => {
    switch (node.type) {
      case "num":
        return constant(Iv.point(node.value));
      case "const":
        return constant(encloseAst(node, env, bits));
      case "var": {
        const val = env[node.name];
        if (val === undefined) refuse("unbound", `no value for ${node.name}`);
        const out = constant(val);
        const i = index.get(node.name);
        if (i !== undefined && order >= 1) out.g[i] = Iv.point(ONE);
        return out;
      }
      case "op": {
        if (node.op === "neg") {
          const a = go(node.args[0]);
          return { v: a.v.neg(), g: a.g && a.g.map((x) => x.neg()), h: a.h && a.h.map((row) => row.map((x) => x.neg())) };
        }
        if (node.op === "+") return add(go(node.args[0]), go(node.args[1]), 1);
        if (node.op === "-") return add(go(node.args[0]), go(node.args[1]), -1);
        if (node.op === "*") return mul(go(node.args[0]), go(node.args[1]));
        if (node.op === "/") {
          const b = go(node.args[1]);
          return mul(go(node.args[0]), compose(b, "recip", (u) => op("/", num(1), u)));
        }
        if (node.op === "^") {
          const c = constantRational(node.args[1]);
          if (c !== null) return compose(go(node.args[0]), `pow ${c}`, (u) => op("^", u, num(c)));
          // u^w = exp(w·log u)
          const logu = compose(go(node.args[0]), "log", (u) => call("log", u));
          return compose(mul(go(node.args[1]), logu), "exp", (u) => call("exp", u));
        }
        break;
      }
      case "call": {
        if (node.name === "min" || node.name === "max") {
          const a = go(node.args[0]);
          const b = go(node.args[1]);
          const pickA = node.name === "min" ? le(a.v.hi, b.v.lo) : ge(a.v.lo, b.v.hi);
          const pickB = node.name === "min" ? le(b.v.hi, a.v.lo) : ge(b.v.lo, a.v.hi);
          if (pickA) return a;
          if (pickB) return b;
          smooth = false;
          const lo = node.name === "min" ? min(a.v.lo, b.v.lo) : max(a.v.lo, b.v.lo);
          const hi = node.name === "min" ? min(a.v.hi, b.v.hi) : max(a.v.hi, b.v.hi);
          return { v: new Iv(lo, hi), g: a.g, h: a.h };
        }
        if (node.name === "abs") {
          const a = go(node.args[0]);
          if (ge(a.v.lo, ZERO)) return a;
          if (le(a.v.hi, ZERO)) return { v: a.v.neg(), g: a.g && a.g.map((x) => x.neg()), h: a.h && a.h.map((row) => row.map((x) => x.neg())) };
          smooth = false;
          return { v: new Iv(ZERO, a.v.mag), g: a.g, h: a.h };
        }
        const name = node.name === "ln" ? "log" : node.name;
        return compose(go(node.args[0]), name, (u) => call(name, u));
      }
    }
    return refuse("bad-expression", `cannot evaluate ${node.type} ${node.op ?? node.name ?? ""}`);
  };
  const out = go(ast);
  return { v: out.v, g: out.g, h: out.h, smooth };
}

// ---- regions ---------------------------------------------------------------------------------

const substitute = (ast, map) => {
  if (ast.type === "var") return map.has(ast.name) ? map.get(ast.name) : ast;
  if (!ast.args) return ast;
  return { ...ast, args: ast.args.map((a) => substitute(a, map)) };
};

const affineAst = (bound, names) => {
  let out = num(bound.constant);
  bound.coefficients.forEach((c, i) => {
    if (c.numerator === 0n) return;
    out = op("+", out, op("*", num(c), variable(names[i])));
  });
  return simplify(out);
};

/**
 * Cut a convex cell into pieces in which every variable has one lower and one
 * upper bound. Where two bounds compete (y below both 4 − x and 3 − x/2), the
 * cell is cut along the line where they are equal and Core recomputes each
 * half, so integrands stay smooth inside every piece.
 */
function singleBounds(bounds, constraints, names, depth) {
  const same = (a, b) => a.constant.equals(b.constant) && a.coefficients.every((c, i) => c.equals(b.coefficients[i]));
  for (let k = 0; k < bounds.length; k++) {
    for (const which of ["lower", "upper"]) {
      const list = bounds[k][which];
      if (list.length < 2) continue;
      const [A, B] = list;
      const width = names.length;
      const diff = { coefficients: Array.from({ length: width }, (_, i) => (A.coefficients[i] ?? ZERO).subtract(B.coefficients[i] ?? ZERO)), constant: A.constant.subtract(B.constant) };
      const drop = (bs, gone) => bs.map((b, i) => (i === k ? { ...b, [which]: b[which].filter((x) => !same(x, gone)) } : b));
      if (diff.coefficients.every((c) => c.numerator === 0n)) {
        // parallel bounds: one always wins (the larger lower bound, the smaller upper bound)
        const aWins = which === "lower" ? diff.constant.numerator >= 0n : diff.constant.numerator <= 0n;
        return singleBounds(drop(bounds, aWins ? B : A), constraints, names, depth);
      }
      if (depth > 24) refuse("bad-region", "the region has too many competing bounds to cut into simple pieces");
      const out = [];
      for (const sign of [1, -1]) {
        // sign = 1: A − B ≥ 0 here, so A wins a lower pair and B wins an upper pair
        const extra = { coefficients: diff.coefficients.map((c) => (sign > 0 ? c : c.negate())), constant: sign > 0 ? diff.constant : diff.constant.negate() };
        const loser = (which === "lower") === (sign > 0) ? B : A;
        const text = constraintsText([...constraints, extra], names);
        for (const cell of MultiRegion.parse(text, { variables: names }).cells()) {
          if (cell.measure !== null && cell.measure.numerator === 0n) continue;
          out.push(...singleBounds(drop(cell.bounds, loser), cell.constraints, names, depth + 1));
        }
      }
      return out;
    }
  }
  return [bounds];
}

/** Chains for a list of constraints a·z + c ≥ 0: each bounds the last variable it uses. */
function constraintsText(constraints, names) {
  const chains = [];
  for (const { coefficients, constant } of constraints) {
    let j = coefficients.length - 1;
    while (j >= 0 && coefficients[j].numerator === 0n) j -= 1;
    if (j < 0) continue; // a constant constraint holds on the whole cell
    const c = coefficients[j];
    let rest = `(${constant.negate().divide(c)})`;
    for (let i = 0; i < j; i++) if (coefficients[i].numerator !== 0n) rest += ` + (${coefficients[i].negate().divide(c)})*${names[i]}`;
    chains.push(c.numerator > 0n ? `(${rest}):${names[j]}:_` : `_:${names[j]}:(${rest})`);
  }
  return chains.join(" && ");
}

/**
 * A region as a list of pieces, each a list of { name, lo, hi } in variable
 * order with lo and hi trees in the earlier variables. Accepts:
 *   { x: [0, 1], y: [0, 2] }           a box
 *   { x: [0, 1], y: ["0", "x^2"] }     bounds in the earlier variables
 *   [[0, 1], [0, 2]]                    a box in variable order
 *   "0:x:1 && 0:y:x" or a MultiRegion   affine chains from @ratmath/core
 */
function piecesOf(region, names, params) {
  if (typeof region === "string") region = MultiRegion.parse(region, { variables: names, params });
  if (region instanceof MultiRegion) {
    if (region.variables.length !== names.length || region.variables.some((name, i) => name !== names[i])) {
      refuse("bad-region", `the region's variables (${region.variables.join(", ")}) must be the function's (${names.join(", ")}), in the same order`);
    }
    const cells = region.cells();
    // pieces of different || alternatives may overlap; an integral would count the overlap twice
    for (let i = 0; i < cells.length; i++) {
      for (let j = i + 1; j < cells.length; j++) {
        if (cells[i].alternative === cells[j].alternative) continue;
        const apart = cells[i].box.some(([lo, hi], k) => ge(lo, cells[j].box[k][1]) || le(hi, cells[j].box[k][0]));
        if (!apart) refuse("bad-region", "the alternatives joined by || may overlap; give regions that do not overlap, or handle each one separately");
      }
    }
    return cells.flatMap((cell) => singleBounds(cell.bounds, cell.constraints, names, 0)).map((bounds) => bounds.map((b, k) => {
      if (!b.lower.length || !b.upper.length) refuse("bad-region", `the region is not bounded in ${names[k]}`);
      return { name: names[k], lo: affineAst(b.lower[0], names), hi: affineAst(b.upper[0], names) };
    }));
  }
  const sides = Array.isArray(region) ? names.map((_, i) => region[i]) : names.map((name) => region?.[name]);
  return [sides.map((side, k) => {
    let pair = side;
    if (side instanceof RationalInterval) pair = [side.low, side.high];
    if (!Array.isArray(pair) || pair.length !== 2) refuse("bad-region", `the region needs [low, high] for ${names[k]}`);
    const tree = (x) => {
      if (typeof x === "string") {
        const t = toAst(x);
        for (const name of freeVariables(t)) {
          if (names.indexOf(name) >= k && !(name in params)) refuse("bad-region", `the bounds of ${names[k]} may only use the variables before it (${names.slice(0, k).join(", ") || "none"}), not ${name}`);
        }
        return t;
      }
      return num(q(x));
    };
    return { name: names[k], lo: tree(pair[0]), hi: tree(pair[1]) };
  })];
}

/**
 * Rewrite f over a piece as a function g on a box, with ∫_piece f = ∫_box g:
 * a variable with constant bounds keeps its interval; one with bounds in the
 * earlier variables becomes lo + s·(hi − lo) with s in [0, 1], and the factor
 * (hi − lo) joins the integrand. Returns { ast, weight, names, box }.
 */
function flatten(ast, piece, paramEnv, bits) {
  const map = new Map();
  const names = [];
  const box = {};
  let weight = num(1);
  for (const { name, lo, hi } of piece) {
    const L = substitute(lo, map);
    const H = substitute(hi, map);
    const cl = constantInterval(L, paramEnv, bits);
    const ch = constantInterval(H, paramEnv, bits);
    if (cl && ch && cl.isPoint && ch.isPoint) {
      if (gt(cl.lo, ch.lo)) refuse("bad-region", `the bounds of ${name} are reversed`);
      names.push(name);
      box[name] = new Iv(cl.lo, ch.lo);
      continue;
    }
    const s = `${name}′`;
    names.push(s);
    box[s] = new Iv(ZERO, ONE);
    const span = op("-", H, L);
    map.set(name, op("+", L, op("*", variable(s), span)));
    weight = op("*", weight, span);
  }
  return { ast: substitute(ast, map), weight, names, box };
}

function constantInterval(ast, paramEnv, bits) {
  for (const name of freeVariables(ast)) if (!(name in paramEnv)) return null;
  try {
    return encloseAst(ast, paramEnv, bits);
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
    return null;
  }
}

// ---- the function class ------------------------------------------------------------------------

const tenTo = (d) => new Rational(1n, 10n ** BigInt(d));

export class ScalarField {
  #float;
  constructor(expression, variables, { params = {} } = {}) {
    this.ast = toAst(expression);
    if (!Array.isArray(variables) || !variables.length) refuse("bad-variables", "give the variables in order, such as [\"x\", \"y\"]");
    this.variables = Object.freeze([...variables]);
    this.params = Object.freeze({ ...params });
    for (const name of freeVariables(this.ast)) {
      if (!this.variables.includes(name) && !(name in params)) refuse("unbound", `${name} has no value: list it in the variables or pass it in params`);
    }
    Object.freeze(this);
  }

  get dimension() {
    return this.variables.length;
  }
  toString() {
    return format(this.ast);
  }
  /** The same formula with other parameter values (for sliders). */
  with(p) {
    return new ScalarField(this.ast, this.variables, { params: { ...this.params, ...p } });
  }
  #same(ast) {
    return new ScalarField(ast, this.variables, { params: this.params });
  }
  #paramEnv() {
    const env = {};
    for (const [k, val] of Object.entries(this.params)) env[k] = Iv.from(typeof val === "string" || typeof val === "number" ? q(val) : val);
    return env;
  }
  #point(p) {
    const list = Array.isArray(p) ? p : this.variables.map((name) => p?.[name]);
    if (list.length !== this.dimension || list.some((x) => x === undefined)) refuse("bad-point", `a point needs a value for each of ${this.variables.join(", ")}`);
    // a pair [a, b] is a side of a box
    return list.map((x) => (x instanceof RationalInterval || x instanceof Iv ? Iv.from(x) : Array.isArray(x) ? new Iv(q(x[0]), q(x[1])) : Iv.point(q(x))));
  }
  #env(point) {
    const env = this.#paramEnv();
    this.variables.forEach((name, i) => (env[name] = point[i]));
    return env;
  }

  /** Float value at a point given as numbers (fast; no guarantee). */
  float(p) {
    const f = (this.#float ??= compileFloat(this.ast));
    const env = floatEnv(this.params);
    const list = Array.isArray(p) ? p : this.variables.map((name) => p[name]);
    this.variables.forEach((name, i) => (env[name] = Number(list[i])));
    return f(env);
  }

  /** ∂f/∂name, symbolically. Several names give a higher partial: partial("x", "y"). */
  partial(...names) {
    let ast = this.ast;
    for (const name of names) {
      if (!this.variables.includes(name)) refuse("unbound", `${name} is not one of the variables`);
      ast = simplify(derivative(ast, name));
    }
    return this.#same(ast);
  }
  /** [∂f/∂x₁, …, ∂f/∂xₙ], symbolically. */
  gradient() {
    return this.variables.map((name) => this.partial(name));
  }
  /** The matrix of second partials, symbolically. */
  hessian() {
    const g = this.gradient();
    return g.map((gi) => this.variables.map((name) => gi.partial(name)));
  }
  /** Σ ∂²f/∂xᵢ². */
  laplacian() {
    return this.#same(simplify(this.variables.map((name) => this.partial(name, name).ast).reduce((a, b) => op("+", a, b))));
  }
  /** f with one variable replaced by a value or an expression in the others. */
  substitute(values) {
    const map = new Map(Object.entries(values).map(([k, val]) => [k, typeof val === "string" ? toAst(val) : val?.type ? val : num(q(val))]));
    const rest = this.variables.filter((name) => !map.has(name));
    const ast = simplify(substitute(this.ast, map));
    if (rest.length === 1) return new AnalyticFunction(ast, { variable: rest[0], params: this.params });
    if (rest.length === 0) return new AnalyticFunction(ast, { params: this.params });
    return new ScalarField(ast, rest, { params: this.params });
  }
  /** The curve t ↦ f(x₁(t), …): a one-variable function. `curve` maps each variable to an expression in `variable`. */
  along(curve, { variable: t = "t" } = {}) {
    const map = new Map(this.variables.map((name) => [name, toAst(String(curve[name]))]));
    return new AnalyticFunction(simplify(substitute(this.ast, map)), { variable: t, params: this.params });
  }

  /** Value, gradient and Hessian at a point or over a box, as certified intervals. */
  jet(p, { digits = 20, order = 2 } = {}) {
    const point = this.#point(p);
    const r = jet(this.ast, this.#env(point), this.variables, bitsForDigits(digits) + 24, order);
    const out = (x) => x.toRationalInterval();
    return {
      value: out(r.v),
      gradient: r.g && r.smooth ? r.g.map(out) : null,
      hessian: r.h && r.smooth ? r.h.map((row) => row.map(out)) : null,
      smooth: r.smooth,
    };
  }

  /** f at a point: float preview, then a certified interval to `digits` significant digits. */
  value(p, opts = {}) {
    const digits = opts.digits ?? 20;
    const point = this.#point(p);
    return new Refinement(
      () => {
        const value = this.float(point.map((x) => x.mid.toNumber()));
        return { value, trust: Number.isFinite(value) ? "good" : "unsure" };
      },
      function* () {
        let bits = Math.max(64, bitsForDigits(digits) + 16);
        for (let attempt = 1; ; attempt++) {
          const r = encloseAst(this.ast, this.#env(point), bits);
          const narrow = r.isPoint || (!r.containsZero() && le(r.width, r.mig.multiply(tenTo(digits)))) || (r.containsZero() && le(r.width, tenTo(digits * 4)));
          if (narrow || bits >= 8192) return { value: r.toRationalInterval(), via: r.isPoint ? "exact rational arithmetic" : `certified enclosure at ${bits} bits` };
          yield { done: attempt, of: attempt + 1, step: `bits ${bits}`, partial: r.toRationalInterval() };
          bits *= 2;
        }
      }.bind(this),
    );
  }

  /** The directional derivative ∇f·u at a point, u normalised to length 1 unless `unit: false`. */
  directional(p, direction, opts = {}) {
    const dir = (Array.isArray(direction) ? direction : this.variables.map((name) => direction[name])).map((x) => (typeof x === "string" && /[a-z(]/i.test(x) ? toAst(x) : num(q(x))));
    let ast = this.gradient().map((g, i) => op("*", g.ast, dir[i])).reduce((a, b) => op("+", a, b));
    if (opts.unit !== false) ast = op("/", ast, call("sqrt", dir.map((d) => op("^", d, num(2))).reduce((a, b) => op("+", a, b))));
    return this.#same(simplify(ast)).value(p, opts);
  }

  /** The tangent plane (linearisation) at a point, as a ScalarField with certified coefficients' midpoints. */
  linearization(p, opts = {}) {
    const point = this.#point(p);
    const j = this.jet(point, { ...opts, order: 1 });
    if (!j.smooth) refuse("not-smooth", "the function is not differentiable at this point");
    const mid = (iv) => num(iv.low.add(iv.high).divide(TWO));
    let ast = mid(j.value);
    this.variables.forEach((name, i) => {
      ast = op("+", ast, op("*", mid(j.gradient[i]), op("-", variable(name), num(point[i].mid))));
    });
    return this.#same(simplify(ast));
  }

  /** Range over a box or region: sampled preview, then a certified enclosure to `digits` digits. */
  range(region, opts = {}) {
    const pieces = piecesOf(region, this.variables, this.params);
    return new Refinement(
      () => {
        let lo = Infinity;
        let hi = -Infinity;
        for (const s of this.#samples(pieces, opts.samples ?? 24)) {
          if (Number.isNaN(s.value)) return { value: [NaN, NaN], trust: "unsure" };
          if (s.value < lo) lo = s.value;
          if (s.value > hi) hi = s.value;
        }
        return { value: [lo, hi], trust: "rough" };
      },
      () => rangeStages(this, pieces, this.#paramEnv(), opts),
    );
  }

  /** ∫ f over a box or region: product Gauss preview, then a certified enclosure. */
  integral(region, opts = {}) {
    const pieces = piecesOf(region, this.variables, this.params);
    return new Refinement(
      () => {
        let total = 0;
        for (const piece of pieces) total += this.#floatIntegral(piece, opts.nodes ?? 12);
        // Gauss nodes are spectrally accurate on a box; a curved side (a square root) costs digits
        const boxy = pieces.every((piece) => piece.every(({ lo, hi }) => constantRational(lo) !== null && constantRational(hi) !== null));
        return { value: total, trust: !Number.isFinite(total) ? "unsure" : boxy ? "good" : "rough" };
      },
      () => integralStages(this, pieces, this.#paramEnv(), opts),
    );
  }

  /**
   * Points where the gradient vanishes inside a box, each proven to exist
   * and to be the only one in its small box, with its kind ("min", "max",
   * "saddle" or "degenerate") from the signs of the Hessian's pivots.
   * Records the search could not decide come back with kind "possible".
   */
  criticalPoints(box, opts = {}) {
    const [piece] = piecesOf(box, this.variables, this.params);
    const B = piece.map(({ name, lo, hi }) => {
      const a = constantRational(lo);
      const b = constantRational(hi);
      if (a === null || b === null) refuse("bad-region", `criticalPoints needs a box with rational sides (${name})`);
      return new Iv(a, b);
    });
    return new Refinement(
      () => ({ value: this.#floatCritical(B, opts), trust: "rough" }),
      () => criticalStages(this, B, this.#paramEnv(), opts),
    );
  }

  // ---- float helpers
  *#samples(pieces, n) {
    const fenv = floatEnv(this.params);
    for (const piece of pieces) {
      const bounds = piece.map(({ lo, hi }) => [compileFloat(lo), compileFloat(hi)]);
      const d = piece.length;
      const per = Math.max(3, Math.round(n ** (2 / d)));
      const idx = new Array(d).fill(0);
      for (;;) {
        const env = { ...fenv };
        const pt = [];
        for (let k = 0; k < d; k++) {
          const a = bounds[k][0](env);
          const b = bounds[k][1](env);
          const x = a + ((b - a) * idx[k]) / (per - 1);
          env[piece[k].name] = x;
          pt.push(x);
        }
        yield { point: pt, value: this.float(pt) };
        let k = d - 1;
        while (k >= 0 && ++idx[k] === per) idx[k--] = 0;
        if (k < 0) break;
      }
    }
  }
  #floatIntegral(piece, nodes) {
    const [xs, ws] = gaussNodes(nodes);
    const fenv = floatEnv(this.params);
    const bounds = piece.map(({ lo, hi }) => [compileFloat(lo), compileFloat(hi)]);
    const rec = (k, env, pt) => {
      if (k === piece.length) return this.float(pt);
      const a = bounds[k][0](env);
      const b = bounds[k][1](env);
      let s = 0;
      for (let i = 0; i < xs.length; i++) {
        const x = (a + b) / 2 + ((b - a) / 2) * xs[i];
        s += ws[i] * rec(k + 1, { ...env, [piece[k].name]: x }, [...pt, x]);
      }
      return (s * (b - a)) / 2;
    };
    return rec(0, fenv, []);
  }
  #floatCritical(B, opts) {
    // Newton on the gradient from a grid of starts
    const g = this.gradient();
    const H = this.hessian();
    const n = this.dimension;
    const per = Math.max(2, Math.round((opts.starts ?? 36) ** (1 / n)));
    const found = [];
    const idx = new Array(n).fill(0);
    const lo = B.map((b) => b.lo.toNumber());
    const hi = B.map((b) => b.hi.toNumber());
    for (;;) {
      let x = idx.map((i, k) => lo[k] + ((hi[k] - lo[k]) * (i + 0.5)) / per);
      let ok = false;
      for (let it = 0; it < 40; it++) {
        const gv = g.map((gi) => gi.float(x));
        const Hv = H.map((row) => row.map((h) => h.float(x)));
        const step = solveFloat(Hv, gv);
        if (!step || step.some((s) => !Number.isFinite(s))) break;
        x = x.map((xi, k) => xi - step[k]);
        if (Math.max(...step.map(Math.abs)) < 1e-12) { ok = true; break; }
      }
      if (ok && x.every((xi, k) => xi >= lo[k] - 1e-9 && xi <= hi[k] + 1e-9) && !found.some((p) => p.point.every((pi, k) => Math.abs(pi - x[k]) < 1e-7))) {
        found.push({ point: x, value: this.float(x) });
      }
      let k = n - 1;
      while (k >= 0 && ++idx[k] === per) idx[k--] = 0;
      if (k < 0) break;
    }
    return found;
  }
}

/** field("x^2 + y^2", ["x", "y"], { params }) */
export function field(expression, variables, opts) {
  if (expression instanceof ScalarField) return expression;
  return new ScalarField(expression, variables, opts);
}

function solveFloat(A, b) {
  const n = b.length;
  const M = A.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let best = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[best][c])) best = r;
    if (!(Math.abs(M[best][c]) > 1e-300)) return null;
    [M[c], M[best]] = [M[best], M[c]];
    for (let r = 0; r < n; r++) {
      if (r === c) continue;
      const f = M[r][c] / M[c][c];
      for (let j = c; j <= n; j++) M[r][j] -= f * M[c][j];
    }
  }
  return M.map((row, i) => row[n] / row[i]);
}

const gaussCache = new Map();
function gaussNodes(n) {
  let r = gaussCache.get(n);
  if (r) return r;
  const xs = [];
  const ws = [];
  for (let i = 1; i <= n; i++) {
    let x = Math.cos((Math.PI * (i - 0.25)) / (n + 0.5));
    let dp = 1;
    for (let it = 0; it < 60; it++) {
      let p0 = 1;
      let p1 = x;
      for (let k = 2; k <= n; k++) [p0, p1] = [p1, ((2 * k - 1) * x * p1 - (k - 1) * p0) / k];
      dp = (n * (x * p1 - p0)) / (x * x - 1);
      const dx = p1 / dp;
      x -= dx;
      if (Math.abs(dx) < 1e-15) break;
    }
    xs.push(x);
    ws.push(2 / ((1 - x * x) * dp * dp));
  }
  gaussCache.set(n, (r = [xs, ws]));
  return r;
}

// ---- certified stages ----------------------------------------------------------------------------

const volume = (box) => box.reduce((s, b) => s.multiply(b.width), ONE);
const widestSide = (box) => box.reduce((best, b, i) => (gt(b.width, box[best].width) ? i : best), 0);
const split = (box, i, at = HALF) => {
  const m = box[i].lo.add(box[i].width.multiply(at));
  return [box.map((b, k) => (k === i ? new Iv(b.lo, m) : b)), box.map((b, k) => (k === i ? new Iv(m, b.hi) : b))];
};
const envOf = (names, box, paramEnv) => {
  const env = { ...paramEnv };
  names.forEach((name, i) => (env[name] = box[i]));
  return env;
};

/**
 * ∫_box g with a proven error, by a product Newton–Cotes rule. In each
 * direction Simpson's error on a side of width w is at most
 * w⁵·max|∂⁴g|/2880 and Boole's is at most w⁷·max|∂⁶g|/1935360, so the
 * whole error is at most vol·Σᵢ wᵢ⁴·|c₄ᵢ|/120 or vol·Σᵢ wᵢ⁶·|c₆ᵢ|/2688
 * with c_kᵢ enclosing ∂ᵢᵏg/k! over the box. Where g has
 * a kink in the box, the plain bound vol·g(box) is used instead.
 * Returns { iv, side } with the side to split next, or null where g cannot
 * be enclosed on the whole box.
 */
function boxIntegral(ast, names, box, paramEnv, bits, cache) {
  const vol = volume(box);
  const env = envOf(names, box, paramEnv);
  let plain;
  try {
    plain = encloseAst(ast, env, bits).scale(vol);
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
    return null; // not defined on the whole box: the caller splits
  }
  let side = widestSide(box);
  if (vol.numerator === 0n) return { iv: plain, side, smooth: true };
  // Simpson (three points, fourth derivative) and Boole (five points, sixth derivative): the smaller bound wins
  const rules = [
    { order: 4, divisor: new Rational(120n), error: ZERO, best: ZERO, side },
    { order: 6, divisor: new Rational(2688n), error: ZERO, best: ZERO, side },
  ];
  try {
    for (let i = 0; i < names.length; i++) {
      const w = box[i].width;
      if (w.numerator === 0n) continue;
      const c = taylorAlong(ast, env, names[i], bits, 6);
      if (!c) return { iv: plain, side, smooth: false };
      for (const rule of rules) {
        const term = c[rule.order].mag.multiply(w.pow(rule.order)).divide(rule.divisor);
        rule.error = rule.error.add(term);
        if (gt(term, rule.best)) { rule.best = term; rule.side = i; }
      }
    }
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
    return { iv: plain, side, smooth: false };
  }
  const boole = lt(rules[1].error, rules[0].error);
  const { error } = rules[boole ? 1 : 0];
  side = rules[boole ? 1 : 0].side;
  const n = names.length;
  const sixth = (k) => new Rational(BigInt(k), 6n);
  const ninetieth = (k) => new Rational(BigInt(k), 90n);
  const quarter = (b, k) => b.lo.add(b.width.multiply(new Rational(BigInt(k), 4n)));
  const pts = box.map((b) => (b.width.numerator === 0n
    ? [[b.lo, ONE]]
    : boole
      ? [[b.lo, ninetieth(7)], [quarter(b, 1), ninetieth(32)], [b.mid, ninetieth(12)], [quarter(b, 3), ninetieth(32)], [b.hi, ninetieth(7)]]
      : [[b.lo, sixth(1)], [b.mid, sixth(4)], [b.hi, sixth(1)]]));
  let sum = IZ;
  const idx = new Array(n).fill(0);
  try {
    for (;;) {
      let weight = ONE;
      const point = [];
      for (let k = 0; k < n; k++) {
        point.push(pts[k][idx[k]][0]);
        weight = weight.multiply(pts[k][idx[k]][1]);
      }
      const key = point.join(",");
      let val = cache.get(key);
      if (val === undefined) {
        val = encloseAst(ast, envOf(names, point.map((x) => Iv.point(x)), paramEnv), bits);
        cache.set(key, val);
      }
      sum = sum.add(val.scale(weight));
      let k = n - 1;
      while (k >= 0 && ++idx[k] === pts[k].length) idx[k--] = 0;
      if (k < 0) break;
    }
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
    return { iv: plain, side, smooth: false };
  }
  const err = error.multiply(vol);
  const simpson = sum.scale(vol).add(new Iv(err.negate(), err));
  return { iv: R(simpson.intersect(plain) ?? simpson, bits), side, smooth: true };
}

/** A max-heap of { key, ... } items. */
export class Heap {
  #a = [];
  get size() { return this.#a.length; }
  items() { return this.#a; }
  push(item) {
    const a = this.#a;
    a.push(item);
    let i = a.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (a[p].key >= a[i].key) break;
      [a[p], a[i]] = [a[i], a[p]];
      i = p;
    }
  }
  pop() {
    const a = this.#a;
    const top = a[0];
    const last = a.pop();
    if (a.length) {
      a[0] = last;
      let i = 0;
      for (;;) {
        const l = 2 * i + 1;
        const r = l + 1;
        let m = i;
        if (l < a.length && a[l].key > a[m].key) m = l;
        if (r < a.length && a[r].key > a[m].key) m = r;
        if (m === i) break;
        [a[m], a[i]] = [a[i], a[m]];
        i = m;
      }
    }
    return top;
  }
}

/** For a box where no derivative bound is available: the side whose halving narrows the enclosure most. */
function sideByWidth(ast, names, box, paramEnv, bits) {
  let side = widestSide(box);
  let best = null;
  for (let i = 0; i < box.length; i++) {
    if (box[i].width.numerator === 0n) continue;
    try {
      const thin = box.map((b, k) => (k === i ? Iv.point(b.mid) : b));
      const w = encloseAst(ast, envOf(names, thin, paramEnv), bits).width;
      if (best === null || lt(w, best)) { best = w; side = i; }
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
    }
  }
  return side;
}

function* integralStages(f, pieces, paramEnv, opts) {
  const digits = opts.digits ?? 6;
  const bits = opts.bits ?? Math.max(64, bitsForDigits(digits) + 24);
  const maxBoxes = opts.maxBoxes ?? 4000;
  const flats = pieces.map((piece) => {
    const flat = flatten(f.ast, piece, paramEnv, bits);
    return { ...flat, ast: share(simplify(op("*", flat.ast, flat.weight))), start: flat.names.map((name) => flat.box[name]), cache: new Map() };
  });
  // every box waits in a heap ordered by the width of its enclosure; the widest is split next
  const heap = new Heap();
  let sum = IZ; // enclosures of all boxes in the heap
  let width = ZERO;
  let boxes = 0;
  const put = (flat, box, depth) => {
    const value = boxIntegral(flat.ast, flat.names, box, paramEnv, bits, flat.cache);
    boxes += 1;
    if (!value) {
      // not defined on the whole box (an end of a domain inside it): split until it is
      if (depth >= 40) refuse("not-integrable", `the integrand could not be bounded near ${flat.names.map((name, i) => `${name} = ${box[i].mid.toNumber()}`).join(", ")}`);
      for (const half of split(box, sideByWidth(flat.ast, flat.names, box, paramEnv, bits))) put(flat, half, depth + 1);
      return;
    }
    sum = sum.add(value.iv);
    width = width.add(value.iv.width);
    heap.push({ key: value.iv.width.toNumber(), flat, box, value, depth });
  };
  for (const flat of flats) put(flat, flat.start, 0);
  let tick = 0;
  for (;;) {
    const tol = max(ONE, sum.mig).multiply(tenTo(digits));
    if (le(width, tol) || boxes >= maxBoxes || !heap.size) break;
    const item = heap.pop();
    if (item.key === 0 || item.depth >= 200) { heap.push({ ...item, key: -1 }); if (item.key === 0) break; continue; }
    sum = sum.sub(item.value.iv);
    // subtracting an interval widens: rebuild the running sum from the heap now and then
    width = width.subtract(item.value.iv.width);
    const side = item.value.smooth ? item.value.side : sideByWidth(item.flat.ast, item.flat.names, item.box, paramEnv, bits);
    for (const half of split(item.box, side)) put(item.flat, half, item.depth + 1);
    if (++tick % 16 === 0) {
      sum = heap.items().reduce((acc, it) => acc.add(it.value.iv), IZ);
      yield { done: boxes, of: Math.max(maxBoxes, boxes), step: "boxes", partial: R(sum, bits).toRationalInterval() };
    }
  }
  sum = heap.items().reduce((acc, it) => acc.add(it.value.iv), IZ);
  const out = R(sum, bits);
  const met = le(out.width, max(ONE, out.mig).multiply(tenTo(digits)).multiply(TWO));
  return { value: out.toRationalInterval(), via: `Simpson and Boole rules with derivative bounds on ${heap.size} boxes${met ? "" : " (budget hit: wider than asked)"}` };
}

/** Enclosure of g over a box: the plain interval value, tightened by the mean value form when g is smooth there. */
function boxRange(ast, names, box, paramEnv, bits) {
  const over = jet(ast, envOf(names, box, paramEnv), names, bits, 1);
  let outer = over.v;
  const centre = box.map((b) => Iv.point(b.mid));
  let c = null;
  try {
    c = encloseAst(ast, envOf(names, centre, paramEnv), bits);
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
  }
  if (over.smooth && c) {
    let mv = c;
    box.forEach((b, i) => {
      mv = mv.add(over.g[i].mul(new Iv(b.rad.negate(), b.rad)));
    });
    outer = outer.intersect(mv) ?? outer;
  }
  return { outer, c, g: over.smooth ? over.g : null };
}

function* rangeStages(f, pieces, paramEnv, opts) {
  const digits = opts.digits ?? 6;
  const bits = opts.bits ?? Math.max(64, bitsForDigits(digits) + 24);
  const maxBoxes = opts.maxBoxes ?? 4000;
  const flats = pieces.map((piece) => flatten(f.ast, piece, paramEnv, bits));
  let items = [];
  const make = (flat, box) => {
    try {
      return { flat, box, ...boxRange(flat.ast, flat.names, box, paramEnv, bits) };
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      return refuse(e.code, `range: the function is not defined on the whole region (${e.message})`);
    }
  };
  for (const flat of flats) items.push(make(flat, flat.names.map((name) => flat.box[name])));
  let boxes = items.length;
  for (let round = 1; ; round++) {
    let outLo = items[0].outer.lo;
    let outHi = items[0].outer.hi;
    let inLo = null; // an upper bound for the minimum: the smallest proven value at a centre
    let inHi = null; // a lower bound for the maximum
    for (const it of items) {
      outLo = min(outLo, it.outer.lo);
      outHi = max(outHi, it.outer.hi);
      if (it.c) {
        inLo = inLo === null ? it.c.hi : min(inLo, it.c.hi);
        inHi = inHi === null ? it.c.lo : max(inHi, it.c.lo);
      }
    }
    const target = max(ONE, max(outLo.abs(), outHi.abs())).multiply(tenTo(digits));
    const loDone = inLo !== null && le(inLo.subtract(outLo), target);
    const hiDone = inHi !== null && le(outHi.subtract(inHi), target);
    if ((loDone && hiDone) || boxes >= maxBoxes) {
      const iv = R(new Iv(outLo, outHi), bits);
      return { value: iv.toRationalInterval(), via: `mean value form on ${boxes} boxes${loDone && hiDone ? "" : " (budget hit: wider than asked)"}` };
    }
    // keep only boxes that can still hold an extreme, and split those that set the outer bounds
    const next = [];
    for (const it of items) {
      const mayMin = inLo === null || le(it.outer.lo, inLo);
      const mayMax = inHi === null || ge(it.outer.hi, inHi);
      if (!mayMin && !mayMax) {
        // cannot hold an extreme: fold its outer range into a sentinel so the hull stays valid
        continue;
      }
      const needs = (!loDone && mayMin && le(it.outer.lo.subtract(outLo), target)) || (!hiDone && mayMax && le(outHi.subtract(it.outer.hi), target));
      const tiny = it.box.every((b) => b.width.numerator === 0n);
      if (!needs || tiny) {
        next.push(it);
        continue;
      }
      let side = widestSide(it.box);
      if (it.g) {
        let best = null;
        it.box.forEach((b, i) => {
          const score = it.g[i].mag.multiply(b.width);
          if (best === null || gt(score, best)) { best = score; side = i; }
        });
        if (best !== null && best.numerator === 0n) side = widestSide(it.box);
      }
      for (const half of split(it.box, side)) {
        next.push(make(it.flat, half));
        boxes += 1;
      }
    }
    items = next;
    yield { done: round, of: round + 1, step: `boxes ${boxes}`, partial: new RationalInterval(outLo, outHi) };
  }
}

/** Signs of the pivots of a symmetric interval matrix: [positive, negative, undecided]. */
function pivotSigns(H, bits) {
  // Symmetric elimination in intervals, by Sylvester's law of inertia. A
  // diagonal entry of one sign is a 1×1 pivot; where every diagonal entry may
  // vanish (the saddle x·y), a 2×2 block of negative determinant counts one
  // positive and one negative direction.
  let W = H.map((row) => [...row]);
  let pos = 0;
  let neg = 0;
  while (W.length) {
    const n = W.length;
    const p = W.findIndex((row, i) => !row[i].containsZero());
    if (p >= 0) {
      if (gt(W[p][p].lo, ZERO)) pos += 1;
      else neg += 1;
      const rest = W.map((_, i) => i).filter((i) => i !== p);
      W = rest.map((r) => rest.map((j) => R(W[r][j].sub(W[r][p].mul(W[p][j]).div(W[p][p])), bits)));
      continue;
    }
    let block = null;
    for (let i = 0; i < n && !block; i++) {
      for (let j = i + 1; j < n && !block; j++) {
        const det = W[i][i].mul(W[j][j]).sub(W[i][j].mul(W[j][i]));
        if (lt(det.hi, ZERO)) block = [i, j, det];
      }
    }
    if (!block) return [pos, neg, n];
    pos += 1;
    neg += 1;
    const [i, j, det] = block;
    const rest = W.map((_, k) => k).filter((k) => k !== i && k !== j);
    const [a, b, d] = [W[i][i], W[i][j], W[j][j]];
    W = rest.map((r) => rest.map((c) => {
      const [u, w, x, y] = [W[r][i], W[r][j], W[i][c], W[j][c]];
      const t = u.mul(d.mul(x).sub(b.mul(y))).add(w.mul(a.mul(y).sub(b.mul(x))));
      return R(W[r][c].sub(t.div(det)), bits);
    }));
  }
  return [pos, neg, 0];
}

function* criticalStages(f, B, paramEnv, opts) {
  const digits = opts.digits ?? 12;
  const bits = Math.max(96, bitsForDigits(digits) + 40);
  const maxBoxes = opts.maxBoxes ?? 6000;
  const names = f.variables;
  const n = names.length;
  const grad = f.gradient().map((g) => g.ast);
  const minWidth = max(ONE, B.reduce((s, b) => max(s, b.mag), ZERO)).multiply(new Rational(1n, 1n << 30n));
  const gradOver = (box) => grad.map((g) => jet(g, envOf(names, box, paramEnv), names, bits, 1));
  const results = [];
  const possible = [];
  // splitting off-centre keeps symmetric critical points (the origin) off the cuts
  const CUT = new Rational(13n, 29n);
  const stack = [B];
  let boxes = 0;
  /** One Krawczyk step for ∇f = 0 on the box X; returns the image, or null. */
  const krawczyk = (X) => {
    let over;
    let at;
    const c = X.map((b) => Iv.point(b.mid));
    try {
      over = gradOver(X);
      at = grad.map((g) => encloseAst(g, envOf(names, c, paramEnv), bits));
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      return null;
    }
    if (over.some((j) => !j.smooth)) return null;
    const J = over.map((j) => j.g); // interval Hessian
    const Jm = J.map((row) => row.map((x) => x.mid.toNumber()));
    const Cf = invertFloat(Jm);
    if (!Cf) return null;
    const C = Cf.map((row) => row.map((x) => toRational(Number(x.toPrecision(12)))));
    const out = [];
    for (let i = 0; i < n; i++) {
      let acc = c[i];
      for (let k = 0; k < n; k++) acc = acc.sub(at[k].scale(C[i][k]));
      for (let j = 0; j < n; j++) {
        // (I − C·J)_ij
        let m = Iv.point(i === j ? ONE : ZERO);
        for (let k = 0; k < n; k++) m = m.sub(J[k][j].scale(C[i][k]));
        acc = acc.add(m.mul(new Iv(X[j].rad.negate(), X[j].rad)));
      }
      out.push(R(acc, bits));
    }
    return out;
  };
  const inside = (K, X) => K.every((k, i) => gt(k.lo, X[i].lo) && lt(k.hi, X[i].hi));
  while (stack.length) {
    const box = stack.pop();
    boxes += 1;
    if (boxes % 32 === 0) yield { done: boxes, of: boxes + stack.length, step: "boxes" };
    let over;
    try {
      over = gradOver(box);
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      over = null;
    }
    if (over && over.some((j) => !j.v.containsZero())) continue; // some partial has one sign here
    const small = box.every((b) => le(b.width, minWidth));
    // test a slightly larger box, so a point on a cut is still caught
    const grown = box.map((b) => { const pad = b.width.divide(new Rational(8n)); return new Iv(b.lo.subtract(pad), b.hi.add(pad)); });
    let K = over ? krawczyk(grown) : null;
    if (K && inside(K, grown)) {
      let X = K;
      for (let it = 0; it < 40; it++) {
        const next = krawczyk(X);
        if (!next) break;
        const tighter = next.map((k, i) => k.intersect(X[i]) ?? X[i]);
        const gain = tighter.some((k, i) => lt(k.width.multiply(new Rational(10n)), X[i].width.multiply(new Rational(9n))));
        X = tighter;
        if (!gain) break;
      }
      // the same point may be proven from two neighbouring boxes
      // the same point may be proven from two neighbouring boxes: it is the same one when a box that
      // holds both enclosures is itself proven to hold a single critical point
      const dup = results.some((r) => {
        if (!r.box.every((b, i) => b.intersect(X[i]) !== null)) return false;
        const hull = r.box.map((b, i) => b.hull(X[i]));
        if (hull.every((b, i) => le(r.box[i].lo, b.lo) && ge(r.box[i].hi, b.hi)) || hull.every((b, i) => le(X[i].lo, b.lo) && ge(X[i].hi, b.hi))) return true;
        const wide = hull.map((b) => { const pad = b.width.divide(new Rational(8n)); return new Iv(b.lo.subtract(pad), b.hi.add(pad)); });
        const Kh = krawczyk(wide);
        return Kh !== null && inside(Kh, wide);
      });
      if (!dup && X.every((x, i) => ge(x.hi, B[i].lo) && le(x.lo, B[i].hi))) {
        let kind = "degenerate";
        let value = null;
        try {
          const j = jet(f.ast, envOf(names, X, paramEnv), names, bits, 2);
          value = j.v;
          if (j.smooth) {
            const [pos, neg, unknown] = pivotSigns(j.h, bits);
            if (!unknown) kind = neg === 0 ? "min" : pos === 0 ? "max" : "saddle";
          }
        } catch (e) {
          if (!(e instanceof AnalyticError)) throw e;
        }
        results.push({ box: X, kind, value });
      }
      continue;
    }
    if (small || boxes >= maxBoxes) {
      possible.push(box);
      continue;
    }
    const side = widestSide(box);
    stack.push(...split(box, side, CUT));
  }
  const out = (iv) => iv.toRationalInterval();
  const records = results.map((r) => ({ kind: r.kind, unique: true, point: r.box.map(out), value: r.value ? out(R(r.value, bits)) : null }));
  // Undecided boxes that touch a proven point add nothing. The rest are
  // gathered into connected groups: a curve of critical points (x²y² along
  // the axes) is reported once, as the box around the group.
  const loose = possible.filter((box) => !results.some((r) => r.box.every((b, i) => b.intersect(box[i]) !== null))).slice(0, 2000);
  const group = loose.map((_, i) => i);
  const find = (i) => { while (group[i] !== i) i = group[i] = group[group[i]]; return i; };
  for (let i = 0; i < loose.length; i++) {
    for (let j = i + 1; j < loose.length; j++) {
      if (loose[i].every((b, k) => b.intersect(loose[j][k]) !== null)) group[find(i)] = find(j);
    }
  }
  const hulls = new Map();
  loose.forEach((box, i) => {
    const g = find(i);
    const have = hulls.get(g);
    hulls.set(g, have ? have.map((b, k) => b.hull(box[k])) : box);
  });
  for (const box of hulls.values()) records.push({ kind: "possible", unique: false, point: box.map(out), value: null });
  records.sort((a, b) => {
    for (let i = 0; i < n; i++) {
      const c = a.point[i].low.compareTo(b.point[i].low);
      if (c) return c;
    }
    return 0;
  });
  return { value: records, via: `krawczyk on the gradient, ${boxes} boxes` };
}

function invertFloat(A) {
  const n = A.length;
  const M = A.map((row, i) => [...row, ...Array.from({ length: n }, (_, j) => (i === j ? 1 : 0))]);
  for (let c = 0; c < n; c++) {
    let best = c;
    for (let r = c + 1; r < n; r++) if (Math.abs(M[r][c]) > Math.abs(M[best][c])) best = r;
    if (!(Math.abs(M[best][c]) > 1e-200)) return null;
    [M[c], M[best]] = [M[best], M[c]];
    const piv = M[c][c];
    for (let j = 0; j < 2 * n; j++) M[c][j] /= piv;
    for (let r = 0; r < n; r++) {
      if (r === c) continue;
      const fac = M[r][c];
      if (fac === 0) continue;
      for (let j = 0; j < 2 * n; j++) M[r][j] -= fac * M[c][j];
    }
  }
  const out = M.map((row) => row.slice(n));
  return out.flat().every(Number.isFinite) ? out : null;
}

// ---- vector calculus -----------------------------------------------------------------------------

const asFields = (F, variables, opts) => F.map((c) => field(c, variables, opts));

/** ∇·F for F = [F₁, …, Fₙ] (expressions or ScalarFields) in the given variables. */
export function divergence(F, variables, opts) {
  const fs = asFields(F, variables, opts);
  return new ScalarField(simplify(fs.map((c, i) => c.partial(variables[i]).ast).reduce((a, b) => op("+", a, b))), variables, opts);
}

/** ∇×F in three variables, as three ScalarFields; in two variables the scalar ∂F₂/∂x − ∂F₁/∂y. */
export function curl(F, variables, opts) {
  const fs = asFields(F, variables, opts);
  const d = (i, j) => fs[i].partial(variables[j]).ast;
  const mk = (ast) => new ScalarField(simplify(ast), variables, opts);
  if (fs.length === 2 && variables.length === 2) return mk(op("-", d(1, 0), d(0, 1)));
  if (fs.length !== 3 || variables.length !== 3) refuse("bad-dimension", "curl needs two or three components and as many variables");
  return [mk(op("-", d(2, 1), d(1, 2))), mk(op("-", d(0, 2), d(2, 0))), mk(op("-", d(1, 0), d(0, 1)))];
}

/** The matrix ∂Fᵢ/∂xⱼ, symbolically. */
export function jacobian(F, variables, opts) {
  return asFields(F, variables, opts).map((c) => variables.map((name) => c.partial(name)));
}

/**
 * ∫_C F·dr along the curve r(t), t from a to b, as a one-variable integral
 * (a Refinement). `curve` maps each variable to an expression in t. With a
 * single expression instead of a list, the scalar line integral ∫_C f ds.
 */
export function lineIntegral(F, variables, curve, [a, b], opts = {}) {
  const t = opts.variable ?? "t";
  const r = variables.map((name) => toAst(String(curve[name])));
  const dr = r.map((x) => simplify(derivative(x, t)));
  const map = new Map(variables.map((name, i) => [name, r[i]]));
  let ast;
  if (Array.isArray(F)) {
    ast = asFields(F, variables, opts).map((c, i) => op("*", substitute(c.ast, map), dr[i])).reduce((x, y) => op("+", x, y));
  } else {
    const speed = call("sqrt", dr.map((d) => op("^", d, num(2))).reduce((x, y) => op("+", x, y)));
    ast = op("*", substitute(field(F, variables, opts).ast, map), speed);
  }
  return new AnalyticFunction(simplify(ast), { variable: t, params: opts.params ?? {} }).integral(a, b, opts);
}

/**
 * A surface integral over r(u, v) with (u, v) in a region. With a list F of
 * three components, the flux ∫∫ F·(r_u × r_v) du dv; with one expression,
 * ∫∫ f |r_u × r_v| du dv. `surface` maps each of the three variables to an
 * expression in the two parameters.
 */
export function surfaceIntegral(F, variables, surface, parameters, region, opts = {}) {
  if (variables.length !== 3 || parameters.length !== 2) refuse("bad-dimension", "a surface integral needs three variables and two parameters");
  const r = variables.map((name) => toAst(String(surface[name])));
  const ru = r.map((x) => simplify(derivative(x, parameters[0])));
  const rv = r.map((x) => simplify(derivative(x, parameters[1])));
  const cross = [
    op("-", op("*", ru[1], rv[2]), op("*", ru[2], rv[1])),
    op("-", op("*", ru[2], rv[0]), op("*", ru[0], rv[2])),
    op("-", op("*", ru[0], rv[1]), op("*", ru[1], rv[0])),
  ];
  const map = new Map(variables.map((name, i) => [name, r[i]]));
  let ast;
  if (Array.isArray(F)) {
    ast = asFields(F, variables, opts).map((c, i) => op("*", substitute(c.ast, map), cross[i])).reduce((x, y) => op("+", x, y));
  } else {
    ast = op("*", substitute(field(F, variables, opts).ast, map), call("sqrt", cross.map((c) => op("^", c, num(2))).reduce((x, y) => op("+", x, y))));
  }
  return new ScalarField(simplify(ast), parameters, { params: opts.params ?? {} }).integral(region, opts);
}
