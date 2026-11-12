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
import { expPoint, sinCosPoint, logPoint, atanPoint, sqrtPoint, piIv } from "./points.js";
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
  const Rh = h.bound(2).hull(IV_ZERO); // ξ lies between c0 and c0 + h
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

function expSpec(c0, n, X, bits) {
  const E = expPoint(c0, bits + 8);
  const coeffs = [];
  for (let k = 0; k <= n; k++) coeffs.push(ivFact(E, k));
  const M = new Iv(expPoint(X.lo, 32).lo, expPoint(X.hi, 32).hi);
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
    refuse("domain", `log needs a positive argument, but the argument's range ${X} reaches ${X.lo}`, { range: X.toRationalInterval() });
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

// ------------------------------------------------------------------ sqrt

function sqrtSpec(c0, n, X, bits) {
  if (le(X.lo, ZERO)) {
    refuse("domain", `sqrt models need the argument's range to stay above 0, but it reaches ${X.lo}`, { range: X.toRationalInterval() });
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
/** g^a for rational a via exp(a·log g) (integers use exact powers). */
export function power(g, a) {
  const q = a instanceof Rational ? a : new Rational(BigInt(a));
  if (q.denominator === 1n) return g.pow(Number(q.numerator));
  if (eq(q, HALF)) return sqrt(g);
  return exp(log(g).multiply(q));
}
export { piIv };

function poly_hb(m) {
  return Iv.sym(magBound(m.coeffs, m.domain.t.mag)).add(m.rem);
}
