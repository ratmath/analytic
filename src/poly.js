// Dense polynomials as arrays of Rationals, index = power. Exact arithmetic,
// plus a certified range bound on an interval (Bernstein form + subdivision).
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { ZERO, ONE, isZero, min, max, eq, lt, le, gt } from "./rat.js";

export function trim(p) {
  let n = p.length;
  while (n > 1 && isZero(p[n - 1])) n--;
  return n === p.length ? p : p.slice(0, n);
}

export function add(p, q) {
  const n = Math.max(p.length, q.length);
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = (p[i] ?? ZERO).add(q[i] ?? ZERO);
  return trim(r);
}

export function sub(p, q) {
  const n = Math.max(p.length, q.length);
  const r = new Array(n);
  for (let i = 0; i < n; i++) r[i] = (p[i] ?? ZERO).subtract(q[i] ?? ZERO);
  return trim(r);
}

export function scale(p, c) {
  if (isZero(c)) return [ZERO];
  return p.map((a) => a.multiply(c));
}

// ---- integer-polynomial fast paths (avoid a gcd per Rational operation)

const isPow2 = (n) => n > 0n && (n & (n - 1n)) === 0n;
function tz(n) {
  if (n === 0n) return Infinity;
  if (n < 0n) n = -n;
  return BigInt((n & -n).toString(2).length - 1);
}
export function gcd(a, b) {
  if (a < 0n) a = -a;
  if (b < 0n) b = -b;
  if (isPow2(b)) {
    if (a === 0n) return b;
    const k = tz(a);
    const m = tz(b);
    return 1n << (k < m ? k : m);
  }
  if (isPow2(a)) return gcd(b, a);
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

/** p = N / den with integer N_j and a common denominator. */
export function toInt(p) {
  let den = 1n;
  for (const c of p) {
    const d = c.denominator;
    if (d !== den) den = (den / gcd(den, d)) * d;
  }
  return { N: p.map((c) => c.numerator * (den / c.denominator)), den };
}

/** Product, keeping only degrees ≤ maxDeg in `low` and the rest in `high`. */
export function mulSplit(p, q, maxDeg) {
  const A = toInt(p);
  const B = toInt(q);
  const prod = new Array(p.length + q.length - 1).fill(0n);
  for (let i = 0; i < p.length; i++) {
    const a = A.N[i];
    if (a === 0n) continue;
    for (let j = 0; j < q.length; j++) {
      const b = B.N[j];
      if (b !== 0n) prod[i + j] += a * b;
    }
  }
  const den = A.den * B.den;
  const low = [];
  const high = [];
  for (let k = 0; k < prod.length; k++) {
    const v = prod[k] === 0n ? ZERO : new Rational(prod[k], den);
    if (k <= maxDeg) low.push(v);
    else high[k] = v;
  }
  for (let k = 0; k < high.length; k++) if (high[k] === undefined) high[k] = ZERO;
  return { low: trim(low.length ? low : [ZERO]), high };
}

/** Upper bound of Σ |a_j| r^j (so |p(t)| ≤ it for |t| ≤ r), in integers. */
export function magBound(p, r) {
  const { N, den } = toInt(p);
  const rn = r.numerator < 0n ? -r.numerator : r.numerator;
  const rd = r.denominator;
  const n = N.length - 1;
  let acc = 0n;
  // Σ |N_j| rn^j rd^(n−j)  /  (den · rd^n)   via Horner in rn/rd
  for (let j = n; j >= 0; j--) {
    const a = N[j] < 0n ? -N[j] : N[j];
    acc = acc * rn + a * rd ** BigInt(n - j);
  }
  return new Rational(acc, den * rd ** BigInt(n));
}

export function evaluate(p, x) {
  let r = ZERO;
  for (let i = p.length - 1; i >= 0; i--) r = r.multiply(x).add(p[i]);
  return r;
}

/** Coefficients of p(a + t) in powers of t (Taylor shift, Horner scheme). */
export function shift(p, a) {
  const c = p.slice();
  if (isZero(a)) return c;
  const n = c.length;
  for (let i = 0; i < n - 1; i++) {
    for (let j = n - 2; j >= i; j--) c[j] = c[j].add(a.multiply(c[j + 1]));
  }
  return c;
}

export function derivative(p) {
  if (p.length <= 1) return [ZERO];
  return trim(p.slice(1).map((a, i) => a.multiply(new Rational(BigInt(i + 1)))));
}

export function antiderivative(p) {
  return trim([ZERO, ...p.map((a, i) => a.divide(new Rational(BigInt(i + 1))))]);
}

const binomCache = [];
function binomRow(n) {
  if (binomCache[n]) return binomCache[n];
  const row = [1n];
  for (let k = 1; k <= n; k++) row.push((row[k - 1] * BigInt(n - k + 1)) / BigInt(k));
  binomCache[n] = row;
  return row;
}

/**
 * Bernstein enclosure of {p(t) : t ∈ [l, h]}. Exact at the endpoints; the
 * bound is the hull of the Bernstein coefficients.
 */
function bernstein(p, l, h) {
  const n = p.length - 1;
  if (n === 0) return { iv: Iv.point(p[0]), tight: true };
  const w = h.subtract(l);
  // q(s) = p(l + w s), s ∈ [0, 1]
  const q = shift(p, l);
  let wk = ONE;
  for (let j = 0; j <= n; j++) {
    q[j] = q[j].multiply(wk);
    wk = wk.multiply(w);
  }
  const cn = binomRow(n);
  let lo = null;
  let hi = null;
  const b = new Array(n + 1);
  for (let i = 0; i <= n; i++) {
    const ci = binomRow(i);
    let s = ZERO;
    for (let j = 0; j <= i; j++) {
      if (isZero(q[j])) continue;
      s = s.add(q[j].multiply(new Rational(ci[j], cn[j])));
    }
    b[i] = s;
    lo = lo === null ? s : min(lo, s);
    hi = hi === null ? s : max(hi, s);
  }
  // Tight when the extremes are attained at the endpoints (b_0 = p(l), b_n = p(h)).
  const ends = [b[0], b[n]];
  const tight = ends.some((e) => eq(e, lo)) && ends.some((e) => eq(e, hi));
  return { iv: new Iv(lo, hi), tight, lowEnd: min(b[0], b[n]), highEnd: max(b[0], b[n]) };
}

/**
 * Certified range of p on [l, h]. `depth` bounds the bisection depth;
 * `tol` (Rational) stops refining once the overestimate is below it.
 */
export function range(p, l, h, { depth = 0, tol = null } = {}) {
  p = trim(p);
  if (p.length === 1) return Iv.point(p[0]);
  if (eq(l, h)) return Iv.point(evaluate(p, l));
  const pieces = [[l, h, 0]];
  let lo = null;
  let hi = null;
  // Known attained values give a floor on how good the enclosure can get.
  let attainedLo = null;
  let attainedHi = null;
  const results = [];
  while (pieces.length) {
    const [a, b, d] = pieces.pop();
    const r = bernstein(p, a, b);
    const vLo = r.lowEnd ?? r.iv.lo;
    const vHi = r.highEnd ?? r.iv.hi;
    attainedLo = attainedLo === null ? vLo : min(attainedLo, vLo);
    attainedHi = attainedHi === null ? vHi : max(attainedHi, vHi);
    const over = r.iv.width.subtract(vHi.subtract(vLo));
    if (r.tight || d >= depth || (tol && le(over, tol))) {
      results.push(r.iv);
    } else {
      const m = a.add(b).divide(new Rational(2n));
      pieces.push([a, m, d + 1], [m, b, d + 1]);
    }
  }
  for (const iv of results) {
    lo = lo === null ? iv.lo : min(lo, iv.lo);
    hi = hi === null ? iv.hi : max(hi, iv.hi);
  }
  return new Iv(lo, hi);
}

/** Range of p over an interval argument (point → exact value). */
export function rangeOn(p, iv, opts) {
  return range(p, iv.lo, iv.hi, opts);
}

/**
 * Cheap enclosure of {p(t) : t ∈ iv} by interval Horner. Looser than
 * `range` but needs no Bernstein transform; used for small remainder terms.
 */
export function hornerBound(p, iv) {
  let r = Iv.point(p[p.length - 1] ?? ZERO);
  for (let i = p.length - 2; i >= 0; i--) r = r.mul(iv).add(p[i]);
  return r;
}
