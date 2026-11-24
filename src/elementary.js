// Elementary functions of Taylor models, by composition with the outer
// function's Taylor series about the inner model's centre value c0:
//
//   f(c0 + h) = Σ_{k≤n} f^(k)(c0)/k! · h^k  +  f^(n+1)(ξ)/(n+1)! · h^(n+1)
//
// with ξ between c0 and c0 + h. h = g − c0 is a model with range Rh, so the
// last term is enclosed by  [f^(n+1)/(n+1)! over c0 + Rh] · Rh^(n+1).
// Coefficients f^(k)(c0)/k! are certified intervals; their midpoints go into
// the polynomial and their radii into the remainder.
import { Rational } from "@ratmath/core";
import { Iv, IV_ZERO } from "./interval.js";
import { ZERO, ONE, TWO, HALF, rat, lt, le, gt, eq, isZero, factorial, roundDyadic, log2Approx, max } from "./rat.js";
import { expPoint, sinCosPoint, logPoint, atanPoint, sqrtPoint, piIv, asinPoint, rootPoint, erfPoint } from "./points.js";
import { refuse } from "./errors.js";
import { TaylorModel } from "./model.js";
import { magBound } from "./poly.js";

function fact(n) {
  return new Rational(factorial(n));
}

/**
 * Compose `spec` with model g. spec(c0, n, X, bits) returns
 *   { coeffs: Iv[n+1], lagrange: Iv }   where lagrange ⊇ f^(n+1)(ξ)/(n+1)! for ξ ∈ X,
 * after checking that f is defined (and smooth) on X = c0 + Rh.
 */
function compose(g, name, spec) {
  if (!(g instanceof TaylorModel)) refuse("bad-operand", `${name} expects a Taylor model here`);
  const n = g.order;
  const bits = g.bits;
  const c0 = g.coeffs[0];
  const hCoeffs = g.coeffs.slice();
  hCoeffs[0] = ZERO;
  // Powers of h are kept to degree 2n and the sum is truncated once at the
  // end, so the high-degree parts of the separate powers can cancel.
  const h = new TaylorModel({ domain: g.domain, coeffs: hCoeffs, rem: g.rem, order: 2 * n, bits, notes: g.notes, assumed: g.assumed });
  // ξ lies between c0 and c0 + h; an h that is exactly 0 (a point value) needs no rounding
  const hZero = hCoeffs.every(isZero) && g.rem.isPoint && isZero(g.rem.lo);
  const Rh = hZero ? IV_ZERO : h.bound(2).hull(IV_ZERO);
  const X = Rh.add(c0);
  const { coeffs, lagrange, rule } = spec(c0, n, X, bits);

  let poly = [ZERO];
  let rem = lagrange.mul(Rh.pow(n + 1));
  let hk = null; // h^k
  for (let k = 0; k <= n; k++) {
    const ck = coeffs[k];
    if (k > 0) hk = hk === null ? h : hk.multiply(h);
    const m = ck.isPoint ? ck.lo : roundMid(ck, bits);
    const r = max(ck.hi.subtract(m).abs(), ck.lo.subtract(m).abs());
    if (k === 0) {
      poly = [m];
      if (!isZero(r)) rem = rem.add(Iv.sym(r));
      continue;
    }
    if (isZero(m) && isZero(r)) continue;
    const term = hk.multiply(m);
    poly = addPoly(poly, term.coeffs);
    rem = rem.add(term.rem);
    if (!isZero(r)) rem = rem.add(Iv.sym(r.multiply(poly_hb(hk).mag)));
  }
  return new TaylorModel({
    domain: g.domain, coeffs: poly, rem, order: n, bits,
    notes: [...g.notes, `${name} (${rule})`], assumed: g.assumed,
  });
}

function addPoly(p, q) {
  const n = Math.max(p.length, q.length);
  const r = [];
  for (let i = 0; i < n; i++) r.push((p[i] ?? ZERO).add(q[i] ?? ZERO));
  return r;
}

function roundMid(iv, bits) {
  const m = iv.mid;
  const e = log2Approx(m.abs());
  return roundDyadic(m, bits + 24 - (Number.isFinite(e) ? e : 0));
}

const ivFact = (iv, n) => iv.scale(new Rational(1n, factorial(n)));

// ------------------------------------------------------------------ exp

const EXP_LIMIT = new Rational(1n << 16n);
function expSpec(c0, n, X, bits) {
  if (gt(X.hi, EXP_LIMIT)) refuse("overflow", `exp argument range reaches ${X.hi.toNumber()}, beyond the supported 2^16`);
  const E = expPoint(c0, bits + 8);
  const coeffs = [];
  for (let k = 0; k <= n; k++) coeffs.push(ivFact(E, k));
  const Xr = X.roundOut(40); // a slightly wider argument range keeps the bound cheap
  const M = new Iv(expPoint(Xr.lo, 32).lo, expPoint(Xr.hi, 32).hi);
  return { coeffs, lagrange: ivFact(M, n + 1), rule: "Lagrange, |exp^(n+1)| ≤ e^max" };
}

// ------------------------------------------------------------------ sin, cos

function trigSpec(phase) {
  // derivative k of sin is sin(x + kπ/2): cycle [sin, cos, -sin, -cos]
  return (c0, n, X, bits) => {
    const { sin, cos } = sinCosPoint(c0, bits + 8);
    const cyc = [sin, cos, sin.neg(), cos.neg()];
    const coeffs = [];
    for (let k = 0; k <= n; k++) coeffs.push(ivFact(cyc[(k + phase) % 4], k));
    return { coeffs, lagrange: ivFact(new Iv(rat(-1), ONE), n + 1), rule: "Lagrange, |derivatives| ≤ 1" };
  };
}

// ------------------------------------------------------------------ log

function logSpec(c0, n, X, bits) {
  if (le(X.lo, ZERO)) {
    refuse("domain", `log needs a positive argument, but the argument's range is ${X}`, { range: X.toRationalInterval() });
  }
  const coeffs = [logPoint(c0, bits + 8)];
  let p = ONE;
  for (let k = 1; k <= n; k++) {
    p = p.multiply(c0);
    const v = new Rational(k % 2 === 1 ? 1n : -1n).divide(p.multiply(new Rational(BigInt(k))));
    coeffs.push(Iv.point(v));
  }
  // f^(n+1)(ξ)/(n+1)! = (−1)^n / ((n+1) ξ^(n+1))
  const s = new Rational(n % 2 === 0 ? 1n : -1n, BigInt(n + 1));
  const lag = X.pow(n + 1).recip().scale(s);
  return { coeffs, lagrange: lag, rule: "Lagrange, argument range bounded away from 0" };
}

// ------------------------------------------------------------------ atan

function atanSpec(c0, n, X, bits) {
  const coeffs = [atanPoint(c0, bits + 8)];
  // Taylor coefficients b_j of 1/(1 + x²) about c0:  (A + B t + t²)·b = 1
  const A = ONE.add(c0.multiply(c0));
  const B = TWO.multiply(c0);
  const b = [];
  for (let j = 0; j < n; j++) {
    let v = j === 0 ? ONE : ZERO;
    if (j >= 1) v = v.subtract(B.multiply(b[j - 1]));
    if (j >= 2) v = v.subtract(b[j - 2]);
    b.push(v.divide(A));
  }
  for (let k = 1; k <= n; k++) coeffs.push(Iv.point(b[k - 1].divide(new Rational(BigInt(k)))));
  // |atan^(k)(x)| ≤ (k−1)!/(1+x²)^(k/2)  ⇒  |f^(n+1)/(n+1)!| ≤ 1/((n+1)(1+m²)^⌊(n+1)/2⌋)
  const m = X.mig;
  const den = ONE.add(m.multiply(m)).pow(Math.floor((n + 1) / 2)).multiply(new Rational(BigInt(n + 1)));
  return { coeffs, lagrange: Iv.sym(den.reciprocal()), rule: "Lagrange, |atan^(k)| ≤ (k−1)!/(1+x²)^(k/2)" };
}

// ------------------------------------------------------------------ asin

/** r_k with (1 − x²)^(−1/2) = S·Σ r_k t^k about c (S = 1/√(1 − c²)), from (1 − x²)w′ = x·w. */
function invSqrtRatios(c, n) {
  const A = ONE.subtract(c.multiply(c));
  const B = TWO.multiply(c);
  const r = [ONE];
  for (let k = 0; k < n; k++) {
    let v = c.add(B.multiply(new Rational(BigInt(k)))).multiply(r[k]);
    if (k >= 1) v = v.add(r[k - 1].multiply(new Rational(BigInt(k))));
    r.push(v.divide(A.multiply(new Rational(BigInt(k + 1)))));
  }
  return r;
}

function asinSpec(c0, n, X, bits) {
  const M = X.mag;
  if (gt(M, ONE)) refuse("domain", `asin and acos need an argument in [-1, 1], but the argument's range is ${X}`, { range: X.toRationalInterval() });
  if (eq(M, ONE)) refuse("not-smooth", `asin and acos are not smooth at ±1, and the argument's range ${X} reaches it; split the domain there`, { range: X.toRationalInterval() });
  const S = sqrtPoint(ONE.subtract(c0.multiply(c0)), bits + 8).recip();
  const r = invSqrtRatios(c0, n);
  const coeffs = [asinPoint(c0, bits + 8)];
  for (let k = 1; k <= n; k++) coeffs.push(S.scale(r[k - 1].divide(new Rational(BigInt(k)))));
  // asin's series at 0 has non-negative coefficients, so |asin^(k)(ξ)| ≤ asin^(k)(M) for |ξ| ≤ M:
  // the (n+1)-th Taylor coefficient about M bounds the Lagrange factor
  const SM = sqrtPoint(ONE.subtract(M.multiply(M)), 40).recip();
  const top = SM.hi.multiply(invSqrtRatios(M, n)[n]).divide(new Rational(BigInt(n + 1)));
  return { coeffs, lagrange: Iv.sym(top), rule: "Lagrange, |asin^(k)(ξ)| ≤ asin^(k)(max |argument|)" };
}

// ------------------------------------------------------------------ erf

function erfSpec(c0, n, X, bits) {
  // erf′(x) = (2/√π)·e^(−x²). With e^(−(c+t)²) = E·Σ g_k t^k (E = e^(−c²)), g′ = −2(c + t)·g gives
  //   (k+1)·g_(k+1) = −2c·g_k − 2·g_(k−1),   g_0 = 1.
  const pi = piIv(bits + 16);
  const scale = new Iv(sqrtPoint(pi.lo, bits + 16).lo, sqrtPoint(pi.hi, bits + 16).hi).recip().scale(TWO).mul(expPoint(c0.multiply(c0).negate(), bits + 16));
  const g = [ONE];
  for (let k = 0; k < n; k++) {
    let v = TWO.multiply(c0).multiply(g[k]).negate();
    if (k >= 1) v = v.subtract(TWO.multiply(g[k - 1]));
    g.push(v.divide(new Rational(BigInt(k + 1))));
  }
  const coeffs = [erfPoint(c0, bits + 8)];
  for (let k = 1; k <= n; k++) coeffs.push(scale.scale(g[k - 1].divide(new Rational(BigInt(k)))));
  // erf^(n+1)(ξ) = (2/√π)·(−1)^n·H_n(ξ)·e^(−ξ²) and |H_n(ξ)|·e^(−ξ²/2) ≤ 1.09·√(2^n·n!) (Cramér),
  // so |erf^(n+1)(ξ)|/(n+1)! ≤ 1.24·√(2^n·n!)/(n+1)!   (2/√π·1.09 < 1.24)
  const sq = sqrtPoint(new Rational((1n << BigInt(n)) * factorial(n)), 40).hi;
  const top = sq.multiply(new Rational(124n, 100n)).divide(new Rational(factorial(n + 1)));
  return { coeffs, lagrange: Iv.sym(top), rule: "Lagrange, Cramér's bound on Hermite functions" };
}

// ------------------------------------------------------------------ x^q, q rational

/** ξ^(num/den) for ξ > 0 as an interval. */
function ratPow(x, num, den, bits) {
  const root = den === 1 ? Iv.point(x) : rootPoint(x, den, bits);
  return num >= 0 ? root.pow(num) : root.pow(-num).recip();
}

function powSpec(q) {
  const num = Number(q.numerator);
  const den = Number(q.denominator);
  return (c0, n, X, bits) => {
    if (le(X.lo, ZERO)) {
      refuse("not-smooth", `a fractional power is not smooth where its base is 0: the base's range ${X} reaches 0; split the domain there`, { range: X.toRationalInterval() });
    }
    const S = ratPow(c0, num, den, bits + 8);
    // binom(q, k)
    const bin = [ONE];
    for (let k = 1; k <= n + 1; k++) bin.push(bin[k - 1].multiply(q.subtract(new Rational(BigInt(k - 1)))).divide(new Rational(BigInt(k))));
    const coeffs = [];
    let p = ONE;
    for (let k = 0; k <= n; k++) {
      coeffs.push(S.scale(bin[k].divide(p)));
      p = p.multiply(c0);
    }
    // binom(q, n+1)·ξ^(q − n − 1) is monotone in ξ > 0: its range is spanned by the ends of X
    const at = (x) => ratPow(x, num, den, 40).scale(x.pow(n + 1).reciprocal());
    return { coeffs, lagrange: at(X.lo).hull(at(X.hi)).scale(bin[n + 1]), rule: "Lagrange, base range bounded away from 0" };
  };
}

// ------------------------------------------------------------------ sqrt

function sqrtSpec(c0, n, X, bits) {
  if (le(X.lo, ZERO)) {
    refuse("domain", `sqrt models need the argument's range to stay above 0, but it is ${X}`, { range: X.toRationalInterval() });
  }
  const S = sqrtPoint(c0, bits + 8);
  // binom(1/2, k)
  const bin = [ONE];
  for (let k = 1; k <= n + 1; k++) bin.push(bin[k - 1].multiply(HALF.subtract(new Rational(BigInt(k - 1)))).divide(new Rational(BigInt(k))));
  const coeffs = [];
  let p = ONE;
  for (let k = 0; k <= n; k++) {
    coeffs.push(S.scale(bin[k].divide(p)));
    p = p.multiply(c0);
  }
  // binom(1/2, n+1) ξ^(1/2 − n − 1): decreasing in ξ > 0
  const hiVal = sqrtPoint(X.lo, 32).hi.divide(X.lo.pow(n + 1));
  const loVal = sqrtPoint(X.hi, 32).lo.divide(X.hi.pow(n + 1));
  const lag = new Iv(loVal, hiVal).scale(bin[n + 1]);
  return { coeffs, lagrange: lag, rule: "Lagrange, argument range bounded away from 0" };
}

// ------------------------------------------------------------------ 1/x

function recipSpec(c0, n, X) {
  if (X.containsZero()) {
    refuse("division-by-zero", `cannot divide: the divisor's range ${X} contains 0`, { range: X.toRationalInterval() });
  }
  const coeffs = [];
  let p = c0;
  for (let k = 0; k <= n; k++) {
    coeffs.push(Iv.point(new Rational(k % 2 === 0 ? 1n : -1n).divide(p)));
    p = p.multiply(c0);
  }
  // f^(n+1)(ξ)/(n+1)! = (−1)^(n+1) ξ^−(n+2)
  const lag = X.pow(n + 2).recip().scale(new Rational(n % 2 === 0 ? -1n : 1n));
  return { coeffs, lagrange: lag, rule: "Lagrange, divisor range excludes 0" };
}

// ------------------------------------------------------------------ public

export const exp = (g) => compose(g, "exp", expSpec);
export const sin = (g) => compose(g, "sin", trigSpec(0));
export const cos = (g) => compose(g, "cos", trigSpec(1));
export const log = (g) => compose(g, "log", logSpec);
export const atan = (g) => compose(g, "atan", atanSpec);
export const sqrt = (g) => compose(g, "sqrt", sqrtSpec);
export const reciprocal = (g) => compose(g, "1/x", recipSpec);
export const log1p = (g) => log(g.add(ONE));
export const tan = (g) => sin(g).divide(cos(g));
export const sinh = (g) => exp(g).subtract(exp(g.negate())).multiply(HALF);
export const cosh = (g) => exp(g).add(exp(g.negate())).multiply(HALF);
export const tanh = (g) => {
  const e = exp(g);
  const ei = exp(g.negate());
  return e.subtract(ei).divide(e.add(ei)); // cosh ≥ 1 keeps the divisor away from 0
};
const settingsOf = (g) => ({ order: g.order, bits: g.bits });

export const asin = (g) => compose(g, "asin", asinSpec);
export const erf = (g) => compose(g, "erf", erfSpec);
export const acos = (g) => asin(g).negate().add(TaylorModel.constant(g.domain, piIv(g.bits + 8).scale(HALF).toRationalInterval(), settingsOf(g)));

/**
 * g^a for rational a. Integers use exact powers. Otherwise exp(a·log g) where
 * g > 0; where g < 0 and a has an odd denominator the real root is used:
 * (−8)^(1/3) = −2. Across g = 0 the power is not smooth and is refused.
 */
export function power(g, a) {
  const q = a instanceof Rational ? a : new Rational(BigInt(a));
  if (q.denominator === 1n) return g.pow(Number(q.numerator));
  if (eq(q, HALF)) return sqrt(g);
  const small = q.denominator <= 64n && q.numerator <= 64n && q.numerator >= -64n;
  const pos = (m) => (small ? compose(m, `power ${q}`, powSpec(q)) : exp(log(m).multiply(q)));
  const r = g.bound(4);
  if (gt(r.lo, ZERO)) return pos(g);
  if (lt(r.hi, ZERO)) {
    if (q.denominator % 2n === 0n) refuse("domain", `a power with an even root needs a non-negative base, but the base's range is ${r}`);
    const m = pos(g.negate());
    return q.numerator % 2n === 0n ? m : m.negate();
  }
  if (r.isPoint && gt(q, ZERO)) return TaylorModel.constant(g.domain, ZERO, settingsOf(g));
  if (lt(r.lo, ZERO) && q.denominator % 2n === 0n) refuse("domain", `a power with an even root needs a non-negative base, but the base's range is ${r}`);
  return refuse("not-smooth", `a fractional power is not smooth where its base is 0: the base's range ${r} contains 0; split the domain there`);
}
export const cbrt = (g) => power(g, new Rational(1n, 3n));
export { piIv };

function poly_hb(m) {
  return Iv.sym(magBound(m.coeffs, m.domain.t.mag)).add(m.rem);
}
