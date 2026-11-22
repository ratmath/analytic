// Certified enclosures of elementary functions at rational points.
// Every function returns an Iv that provably contains the true value, with
// relative width about 2^-bits. Error terms are bounded explicitly; rounding of
// intermediate terms is accounted for in the radius.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import {
  ZERO, ONE, TWO, HALF, rat, lt, le, gt, ge, eq, isZero, sign,
  log2Approx, floorDyadic, ceilDyadic, roundDyadic, floorDiv, isqrt, bitLen,
} from "./rat.js";
import { refuse } from "./errors.js";

const pow2 = (k) => (k >= 0 ? new Rational(1n << BigInt(k)) : new Rational(1n, 1n << BigInt(-k)));

/**
 * Sum Σ_{k<N} t_k where `next(t_prev, k)` gives t_k exactly, stopping once
 * |t_k| ≤ 2^-wp and `tailBound(k, t_k)` is ≤ 2^-wp too. Terms are rounded to
 * wp+8 absolute bits; the accumulated rounding error is added to the radius.
 */
function sumSeries(t0, next, tailBound, wp, maxTerms = 100000) {
  const ulp = pow2(-(wp + 8));
  const eps = pow2(-wp);
  let sum = ZERO;
  let rounding = ZERO;
  let t = t0;
  let k = 0;
  while (true) {
    const tail = tailBound(k, t);
    if (tail !== null && le(tail, eps)) {
      return new Iv(sum.subtract(tail).subtract(rounding), sum.add(tail).add(rounding));
    }
    if (k > maxTerms) refuse("budget", "series did not converge within the term budget");
    const tr = roundDyadic(t, wp + 8);
    if (!eq(tr, t)) rounding = rounding.add(ulp);
    sum = sum.add(tr);
    k += 1;
    t = next(t, k);
  }
}

// ---------------------------------------------------------------- exp

const EXP_BIG = new Rational(1n << 12n);

export function expPoint(q, bits = 96) {
  if (isZero(q)) return Iv.point(ONE);
  const neg = sign(q) < 0;
  const a = q.abs();
  if (gt(a, EXP_BIG)) {
    // e^a would need more than 5900 bits: refuse growth; for decay, e^-a lies
    // in (0, e^-4096] ⊂ [0, 2^-5900] (e > 2^1.44). The lower end 0 is all we can
    // represent cheaply, so such values are indistinguishable from 0.
    if (!neg) refuse("overflow", `exp(${a.toNumber()}) is too large to enclose`);
    return new Iv(ZERO, new Rational(1n, 1n << 5900n));
  }
  const e = log2Approx(a);
  const s = Math.max(0, e + 3);
  const wp = bits + s + 16;
  const r = a.divide(pow2(s)); // 0 < r < 1/4
  // exp(r) = Σ r^k/k!; tail after k terms ≤ 2 r^k / k! (r ≤ 1/2).
  let iv = sumSeries(
    ONE,
    (t, k) => t.multiply(r).divide(new Rational(BigInt(k))),
    (k, t) => (k === 0 ? null : t.multiply(TWO)),
    wp,
  );
  for (let i = 0; i < s; i++) iv = iv.mul(iv).roundOut(wp);
  if (neg) iv = iv.recip();
  return iv.roundOut(bits + 4, 6000); // keep tiny values (e^-1000) positive
}

// ---------------------------------------------------------------- atan, pi

/** atan(x) for |x| ≤ 1/2 (alternating, decreasing series). */
function atanSmall(x, wp) {
  const x2 = x.multiply(x);
  // terms t_k = (-1)^k x^{2k+1}/(2k+1); keep p_k = (-1)^k x^{2k+1} as state.
  let p = x;
  return sumSeries(
    x,
    (_t, k) => {
      p = p.multiply(x2).negate();
      return p.divide(new Rational(BigInt(2 * k + 1)));
    },
    (k, t) => (k === 0 ? null : t.abs()),
    wp,
  );
}

let piCache = null;
export function piIv(bits = 96) {
  if (piCache && piCache.bits >= bits) return piCache.iv;
  const wp = bits + 12;
  const a = atanSmall(rat(1, 5), wp).scale(rat(16));
  const b = atanSmall(rat(1, 239), wp).scale(rat(4));
  const iv = a.sub(b).roundOut(bits + 4);
  piCache = { bits, iv };
  return iv;
}

export function atanPoint(q, bits = 96) {
  if (isZero(q)) return Iv.point(ZERO);
  if (sign(q) < 0) return atanPoint(q.negate(), bits).neg();
  const wp = bits + 8;
  let iv;
  if (gt(q, TWO)) {
    // atan(q) = π/2 − atan(1/q)
    iv = piIv(wp).scale(HALF).sub(atanSmall(q.reciprocal(), wp));
  } else if (gt(q, HALF)) {
    // atan(q) = π/4 + atan((q−1)/(q+1)),   |(q−1)/(q+1)| ≤ 1/3
    iv = piIv(wp).scale(rat(1, 4)).add(atanSmall(q.subtract(ONE).divide(q.add(ONE)), wp));
  } else {
    iv = atanSmall(q, wp);
  }
  return iv.roundOut(bits + 4);
}

// ---------------------------------------------------------------- log

/** 2·atanh(z) for |z| ≤ 1/3: 2Σ z^{2j+1}/(2j+1), tail ≤ 2|t_N|·(2N+1)... bounded geometrically. */
function twoAtanh(z, wp) {
  const z2 = z.multiply(z);
  const q = ONE.subtract(z2); // tail ratio bound: |t_{k+1}/t_k| ≤ z²
  let p = z;
  return sumSeries(
    z,
    (_t, k) => {
      p = p.multiply(z2);
      return p.divide(new Rational(BigInt(2 * k + 1)));
    },
    (k, t) => (k === 0 ? null : t.abs().divide(q)),
    wp,
  ).scale(TWO);
}

let ln2Cache = null;
function ln2Iv(bits) {
  if (ln2Cache && ln2Cache.bits >= bits) return ln2Cache.iv;
  const iv = twoAtanh(rat(1, 3), bits + 8).roundOut(bits + 4);
  ln2Cache = { bits, iv };
  return iv;
}

export function logPoint(q, bits = 96) {
  if (le(q, ZERO)) refuse("domain", `log is undefined at ${q} (needs a positive argument)`);
  if (eq(q, ONE)) return Iv.point(ZERO);
  let k = log2Approx(q);
  let m = q.divide(pow2(k));
  if (ge(m, rat(4, 3))) {
    m = m.divide(TWO);
    k += 1;
  } else if (lt(m, rat(2, 3))) {
    m = m.multiply(TWO);
    k -= 1;
  }
  const wp = bits + 8 + bitLen(BigInt(Math.abs(k)));
  let iv = twoAtanh(m.subtract(ONE).divide(m.add(ONE)), wp);
  if (k !== 0) iv = iv.add(ln2Iv(wp).scale(rat(k)));
  return iv.roundOut(bits + 4);
}

// ---------------------------------------------------------------- sin, cos

// Fixed-point interval arithmetic: an enclosure [lo, hi]·2^-W with BigInt ends.
const fdiv = (n, d) => (n >= 0n ? n / d : -((-n + d - 1n) / d)); // floor, d > 0
const cdiv = (n, d) => -fdiv(-n, d);
function fixMul([a, b], [c, d], W) {
  const p = [a * c, a * d, b * c, b * d];
  let lo = p[0];
  let hi = p[0];
  for (const v of p) {
    if (v < lo) lo = v;
    if (v > hi) hi = v;
  }
  const s = 1n << W;
  return [fdiv(lo, s), cdiv(hi, s)];
}
const fixAbsMax = ([a, b]) => (-a > b ? -a : b);

/**
 * sin and cos at a rational x by their Taylor series in fixed point with
 * outward rounding: every term is an interval that contains the exact term,
 * and once the terms decrease, the tail of the alternating series is bounded
 * by the last term. Much cheaper than exact rational terms, whose denominators
 * grow with every power of x.
 */
function sinCosFixed(x, wp) {
  const W = BigInt(wp + 24);
  const n = x.numerator;
  const d = x.denominator;
  const X = [fdiv(n << W, d), cdiv(n << W, d)];
  const sq = fixMul(X, X, W);
  const X2 = [sq[0] < 0n ? 0n : sq[0], sq[1]];
  const x2max = Number(X2[1] >> W) + 1; // integer bound on x²
  const eps = 1n << 8n; // 2^-(wp+16) in units of 2^-W: terms this small end the sum
  const series = (t, first) => {
    let sum = [t[0], t[1]];
    for (let k = 1; ; k++) {
      const m = BigInt((first + 2 * k - 1) * (first + 2 * k));
      const p = fixMul(t, X2, W);
      t = [fdiv(-p[1], m), cdiv(-p[0], m)];
      sum = [sum[0] + t[0], sum[1] + t[1]];
      const decreasing = (first + 2 * k + 1) * (first + 2 * k + 2) > x2max;
      const big = fixAbsMax(t);
      if (decreasing && big <= eps) return [sum[0] - big, sum[1] + big];
      if (k > 100000) refuse("budget", "series did not converge within the term budget");
    }
  };
  const den = 1n << W;
  const toIv = ([lo, hi]) => new Iv(new Rational(lo, den), new Rational(hi, den));
  return { sin: toIv(series(X, 1)), cos: toIv(series([den, den], 0)) };
}

/** {sin, cos} at a rational point. */
export function sinCosPoint(q, bits = 96) {
  if (isZero(q)) return { sin: Iv.point(ZERO), cos: Iv.point(ONE) };
  let x = q;
  let slack = ZERO;
  const e = log2Approx(q);
  const wp = bits + 12 + Math.max(0, e);
  if (gt(q.abs(), rat(4))) {
    // reduce modulo 2π:  x = q − 2πk  with π enclosed
    const pi = piIv(wp + 8);
    const twoPiMid = pi.mid.multiply(TWO);
    const k = floorDiv(
      q.divide(twoPiMid).add(HALF).numerator,
      q.divide(twoPiMid).add(HALF).denominator,
    );
    const r = Iv.point(q).sub(pi.scale(new Rational(2n * k)));
    x = roundDyadic(r.mid, wp + 8);
    slack = r.lo.subtract(x).abs();
    const s2 = r.hi.subtract(x).abs();
    if (gt(s2, slack)) slack = s2;
  }
  const { sin, cos } = sinCosFixed(x, wp);
  // Lipschitz constant 1 for the reduction slack.
  const widen = (iv) => (isZero(slack) ? iv : new Iv(iv.lo.subtract(slack), iv.hi.add(slack)));
  return { sin: widen(sin).roundOut(bits + 4), cos: widen(cos).roundOut(bits + 4) };
}

export const sinPoint = (q, bits) => sinCosPoint(q, bits).sin;
export const cosPoint = (q, bits) => sinCosPoint(q, bits).cos;

// ---------------------------------------------------------------- sqrt

export function sqrtPoint(q, bits = 96) {
  if (lt(q, ZERO)) refuse("domain", `sqrt is undefined at ${q} (needs a non-negative argument)`);
  if (isZero(q)) return Iv.point(ZERO);
  const n = q.numerator;
  const d = q.denominator;
  const s = BigInt(bits + 8);
  // sqrt(n/d) = sqrt(n·d)/d;  S ≤ sqrt(n·d)·2^s < S+1
  const S = isqrt(n * d << (2n * s));
  const den = d << s;
  if (S * S === n * d << (2n * s)) return Iv.point(new Rational(S, den));
  return new Iv(new Rational(S, den), new Rational(S + 1n, den)).roundOut(bits + 4);
}
