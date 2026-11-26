// Special functions with certified enclosures: gamma, log-gamma, digamma and
// the polygammas (Stirling series after a shift, with the first omitted term
// as the error), and the entire functions J_n, Si and the Fresnel integrals
// (their power series in fixed point, every term rounded both ways).
// Also the Float64 versions used for previews.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, HALF, lt, le, gt, max, floorDyadic, ceilDyadic } from "./rat.js";
import { expPoint, logPoint, piIv } from "./points.js";

const RN = (n, d = 1n) => new Rational(BigInt(n), BigInt(d));
const pow2 = (k) => (k >= 0 ? new Rational(1n << BigInt(k)) : new Rational(1n, 1n << BigInt(-k)));

const BERN = [ONE, RN(-1, 2)];
/** The Bernoulli number B_m, exactly. */
export function bernoulli(m) {
  while (BERN.length <= m) {
    const n = BERN.length;
    let s = ZERO;
    let c = 1n; // C(n+1, k)
    for (let k = 0; k < n; k++) {
      s = s.add(new Rational(c).multiply(BERN[k]));
      c = (c * BigInt(n + 1 - k)) / BigInt(k + 1);
    }
    BERN.push(s.divide(RN(n + 1)).negate());
  }
  return BERN[m];
}
const FACT = [1n];
const fact = (n) => {
  while (FACT.length <= n) FACT.push(FACT[FACT.length - 1] * BigInt(FACT.length));
  return FACT[n];
};

const isInteger = (q) => q.denominator === 1n;
/** How far to shift q upward so that the Stirling series reaches the precision. */
function shiftTo(q, bits, m = 0) {
  const need = RN(Math.ceil(bits / 8) + 6 + 2 * m);
  if (!lt(q, need)) return 0;
  const gap = need.subtract(q);
  const whole = gap.numerator / gap.denominator;
  return Number(gap.numerator % gap.denominator === 0n ? whole : whole + 1n);
}
function noPole(q, name) {
  if (isInteger(q) && q.numerator <= 0n) refuse("pole", `${name} has a pole at ${q}`);
}

/** log Γ(y) for large y by Stirling's series; the error is below the first omitted term. */
function stirling(y, wp) {
  const pi = piIv(wp);
  const half = new Iv(logPoint(pi.lo.multiply(TWO), wp).lo, logPoint(pi.hi.multiply(TWO), wp).hi).scale(HALF);
  let s = logPoint(y, wp).scale(y.subtract(HALF)).sub(Iv.point(y)).add(half);
  const y2 = y.multiply(y);
  let ypow = y;
  const eps = pow2(-wp);
  for (let k = 1; ; k++) {
    const term = bernoulli(2 * k).divide(RN(2 * k * (2 * k - 1)).multiply(ypow));
    if (le(term.abs(), eps) || k > 300) {
      const t = term.abs();
      return s.add(new Iv(t.negate(), t)).roundOut(wp, 6000);
    }
    s = s.add(Iv.point(term)).roundOut(wp + 8, 6000);
    ypow = ypow.multiply(y2);
  }
}

/** log Γ(q) for rational q > 0. */
export function lgammaPoint(q, bits = 96) {
  if (!gt(q, ZERO)) refuse("domain", `lgamma needs a positive argument, got ${q}`);
  if (isInteger(q) && q.numerator <= 2n) return Iv.point(ZERO);
  const wp = bits + 40;
  const N = shiftTo(q, bits);
  let prod = ONE;
  for (let j = 0; j < N; j++) prod = prod.multiply(q.add(RN(j)));
  const L = stirling(q.add(RN(N)), wp);
  return (N ? L.sub(logPoint(prod, wp)) : L).roundOut(bits + 4, 6000);
}

/** Γ(q) for rational q that is not 0, −1, −2, …; exact at positive integers. */
export function gammaPoint(q, bits = 96) {
  noPole(q, "gamma");
  if (isInteger(q) && q.numerator <= 2000n) return Iv.point(new Rational(fact(Number(q.numerator) - 1)));
  const wp = bits + 40;
  const N = shiftTo(q, bits);
  let prod = ONE;
  for (let j = 0; j < N; j++) prod = prod.multiply(q.add(RN(j)));
  const L = stirling(q.add(RN(N)), wp);
  const G = new Iv(expPoint(L.lo, wp).lo, expPoint(L.hi, wp).hi);
  return G.scale(prod.reciprocal()).roundOut(bits + 4, 6000);
}

/**
 * The polygamma function ψ⁽ᵐ⁾(q): m = 0 is the digamma function Γ′/Γ,
 * m = 1 the trigamma function. Shifted by ψ⁽ᵐ⁾(x) = ψ⁽ᵐ⁾(x+1) − (−1)ᵐ·m!/x^(m+1).
 */
export function polygammaPoint(m, q, bits = 96) {
  noPole(q, m === 0 ? "digamma" : "polygamma");
  const wp = bits + 40;
  const N = shiftTo(q, bits, m);
  const y = q.add(RN(N));
  const eps = pow2(-wp - 8 * m);
  const y2 = y.multiply(y);
  let s;
  let ypow; // y^(2k+m)
  if (m === 0) {
    s = logPoint(y, wp).sub(Iv.point(y.multiply(TWO).reciprocal()));
    ypow = y2;
  } else {
    const ym = y.pow(m);
    s = Iv.point(new Rational(fact(m - 1)).divide(ym).add(new Rational(fact(m)).divide(ym.multiply(y).multiply(TWO))));
    ypow = ym.multiply(y2);
  }
  for (let k = 1; ; k++) {
    const term = m === 0
      ? bernoulli(2 * k).divide(RN(2 * k).multiply(ypow)).negate()
      : bernoulli(2 * k).multiply(new Rational(fact(2 * k + m - 1), fact(2 * k))).divide(ypow);
    if (le(term.abs(), eps) || k > 300) {
      const t = term.abs();
      s = s.add(new Iv(t.negate(), t));
      break;
    }
    s = s.add(Iv.point(term)).roundOut(wp + 8, 6000);
    ypow = ypow.multiply(y2);
  }
  if (m > 0 && m % 2 === 0) s = s.neg(); // the sign (−1)^(m+1)
  // back down: ψ⁽ᵐ⁾(q) = ψ⁽ᵐ⁾(y) − (−1)ᵐ·m!·Σ_{j<N} 1/(q+j)^(m+1)
  if (N) {
    let acc = Iv.point(ZERO);
    for (let j = 0; j < N; j++) acc = acc.add(Iv.point(q.add(RN(j)).pow(m + 1).reciprocal())).roundOut(wp + 8, 6000);
    const c = new Rational(m % 2 === 0 ? -fact(m) : fact(m));
    s = s.add(acc.scale(c));
  }
  return s.roundOut(bits + 4, 6000);
}

// ---- entire functions by their power series, in fixed point ------------------------------------

/** floor and ceiling of r·2^W as BigInt. */
const fixed = (r, W) => {
  const n = r.numerator << W;
  const d = r.denominator;
  let lo = n / d;
  if (n < 0n && n % d !== 0n) lo -= 1n;
  return [lo, n % d === 0n ? lo : lo + 1n];
};
const cdiv = (n, d) => (n % d === 0n ? n / d : n / d + 1n); // n, d > 0

/** J_n(q) for integer n and rational q. */
export function besselJPoint(n, q, bits = 96) {
  if (!Number.isInteger(n)) refuse("bad-order", "besselJ needs an integer order");
  if (n < 0) {
    const r = besselJPoint(-n, q, bits);
    return n % 2 === 0 ? r : r.neg();
  }
  if (q.numerator === 0n) return Iv.point(n === 0 ? ONE : ZERO);
  const x = q.abs();
  if (gt(x, RN(4096))) refuse("too-large", "besselJ is only enclosed for |x| ≤ 4096");
  const W = BigInt(bits + 40 + Math.ceil(1.45 * x.toNumber()));
  const UNIT = 1n << W;
  const [hl, hh] = fixed(x.multiply(x).divide(RN(4)), W);
  let [tl, th] = fixed(x.divide(TWO).pow(n).divide(new Rational(fact(n))), W);
  let lo = tl;
  let hi = th;
  for (let k = 1; ; k++) {
    const d = BigInt(k) * BigInt(k + n);
    tl = (tl * hl) / (d << W);
    th = cdiv(th * hh, d << W);
    if (k % 2) { lo -= th; hi -= tl; } else { lo += tl; hi += th; }
    // once the terms more than halve, the rest of the series is below twice the last term
    if (th <= 1n && hh * 2n < d * UNIT) break;
  }
  let out = new Iv(new Rational(lo - 4n, UNIT), new Rational(hi + 4n, UNIT));
  if (q.numerator < 0n && n % 2) out = out.neg();
  return out.intersect(new Iv(RN(-1), ONE)).roundOut(bits + 4, 6000);
}

/** The sine integral Si(q) = ∫₀^q sin(t)/t dt. */
export function siPoint(q, bits = 96) {
  if (q.numerator === 0n) return Iv.point(ZERO);
  const x = q.abs();
  if (gt(x, RN(4096))) refuse("too-large", "Si is only enclosed for |x| ≤ 4096");
  const W = BigInt(bits + 40 + Math.ceil(1.45 * x.toNumber()));
  const UNIT = 1n << W;
  const [yl, yh] = fixed(x.multiply(x), W);
  let [pl, ph] = fixed(x, W); // x^(2k+1)/(2k+1)!
  let lo = pl;
  let hi = ph;
  for (let k = 1; ; k++) {
    const d = BigInt(2 * k) * BigInt(2 * k + 1);
    pl = (pl * yl) / (d << W);
    ph = cdiv(ph * yh, d << W);
    const tl = pl / BigInt(2 * k + 1);
    const th = cdiv(ph, BigInt(2 * k + 1));
    if (k % 2) { lo -= th; hi -= tl; } else { lo += tl; hi += th; }
    if (ph <= 1n && yh * 2n < d * UNIT) break;
  }
  const out = new Iv(new Rational(lo - 4n, UNIT), new Rational(hi + 4n, UNIT));
  return (q.numerator < 0n ? out.neg() : out).roundOut(bits + 4, 6000);
}

/** The Fresnel integrals S(q) = ∫₀^q sin(πt²/2) dt and C(q) = ∫₀^q cos(πt²/2) dt. */
export function fresnelPoint(q, bits = 96) {
  if (q.numerator === 0n) return { S: Iv.point(ZERO), C: Iv.point(ZERO) };
  const x = q.abs();
  const zf = (Math.PI / 2) * x.toNumber() ** 2;
  if (zf > 3000) refuse("too-large", "the Fresnel integrals are only enclosed for |x| ≤ 43");
  const Wn = bits + 40 + Math.ceil(1.45 * zf);
  const W = BigInt(Wn);
  const UNIT = 1n << W;
  const z = piIv(Wn + 8).scale(x.multiply(x).divide(TWO));
  const zl = fixed(z.lo, W)[0];
  const zh = fixed(z.hi, W)[1];
  // q_j = z^j/j!; the term of index j is q_j/(2j+1): even j build C, odd j build S
  let ql = UNIT;
  let qh = UNIT;
  const sum = { C: [UNIT, UNIT], S: [0n, 0n] };
  for (let j = 1; ; j++) {
    ql = (ql * zl) / (BigInt(j) << W);
    qh = cdiv(qh * zh, BigInt(j) << W);
    const tl = ql / BigInt(2 * j + 1);
    const th = cdiv(qh, BigInt(2 * j + 1));
    const target = j % 2 ? sum.S : sum.C;
    if ((j >> 1) % 2) { target[0] -= th; target[1] -= tl; } else { target[0] += tl; target[1] += th; }
    if (qh <= 1n && zh * 2n < BigInt(j) * UNIT) break;
  }
  const finish = ([lo, hi]) => {
    const iv = new Iv(new Rational(lo - 8n, UNIT), new Rational(hi + 8n, UNIT)).scale(x);
    return (q.numerator < 0n ? iv.neg() : iv).roundOut(bits + 4, 6000);
  };
  return { S: finish(sum.S), C: finish(sum.C) };
}

// ---- over intervals ---------------------------------------------------------------------------

function sameGap(v, name) {
  // no pole of Γ may lie in [lo, hi]
  if (le(v.lo, ZERO)) {
    const n = v.lo.numerator / v.lo.denominator; // toward zero: the least integer ≥ lo for lo ≤ 0
    if (le(new Rational(n), v.hi) && n <= 0n) refuse("pole", `${name} has a pole in ${v}`);
  }
}
/** ψ⁽ᵐ⁾ over an interval: ψ increases between poles; for m ≥ 1 it is monotone on x > 0. */
export function polygammaIv(m, v, bits = 96) {
  if (v.isPoint) return polygammaPoint(m, v.lo, bits);
  if (m === 0) {
    sameGap(v, "digamma");
    return new Iv(polygammaPoint(0, v.lo, bits).lo, polygammaPoint(0, v.hi, bits).hi);
  }
  if (!gt(v.lo, ZERO)) refuse("domain", "polygamma over an interval needs positive arguments");
  const a = polygammaPoint(m, v.lo, bits);
  const b = polygammaPoint(m, v.hi, bits);
  return a.hull(b);
}
const MIN_GAMMA = new Rational(8856031944n, 10000000000n); // Γ ≥ 0.8856031944… on x > 0

/** Γ over an interval without poles: |Γ| is log-convex between poles, and Γ′ = Γ·ψ gives a mean value form. */
export function gammaIv(v, bits = 96) {
  if (v.isPoint) return gammaPoint(v.lo, bits);
  sameGap(v, "gamma");
  const a = gammaPoint(v.lo, bits);
  const b = gammaPoint(v.hi, bits);
  const M = max(a.mag, b.mag);
  const positive = gt(a.lo, ZERO);
  let ends = positive ? new Iv(ZERO, M) : new Iv(M.negate(), ZERO);
  if (gt(v.lo, ZERO)) ends = new Iv(MIN_GAMMA, max(M, MIN_GAMMA));
  const slope = ends.mul(polygammaIv(0, v, bits));
  const mid = v.mid;
  const mean = gammaPoint(mid, bits).add(slope.mul(new Iv(v.lo.subtract(mid), v.hi.subtract(mid))));
  return (mean.intersect(ends) ?? ends).roundOut(bits + 4, 6000);
}
/** log Γ over an interval of positive numbers (convex, with derivative ψ). */
export function lgammaIv(v, bits = 96) {
  if (v.isPoint) return lgammaPoint(v.lo, bits);
  if (!gt(v.lo, ZERO)) refuse("domain", `lgamma needs positive arguments, got ${v}`);
  const a = lgammaPoint(v.lo, bits);
  const b = lgammaPoint(v.hi, bits);
  const mid = v.mid;
  const mean = lgammaPoint(mid, bits).add(polygammaIv(0, v, bits).mul(new Iv(v.lo.subtract(mid), v.hi.subtract(mid))));
  const top = max(a.hi, b.hi);
  return new Iv(mean.lo, lt(mean.hi, top) ? mean.hi : top).roundOut(bits + 4, 6000);
}
/** A function with |F′| ≤ 1 and |F| ≤ bound over an interval: its value at the midpoint, give or take the radius. */
function lipschitz(point, bound) {
  return (v, bits = 96) => {
    if (v.isPoint) return point(v.lo, bits);
    const r = v.rad;
    const c = point(v.mid, bits);
    const iv = new Iv(c.lo.subtract(r), c.hi.add(r));
    return (iv.intersect(new Iv(bound.negate(), bound)) ?? iv).roundOut(bits + 4, 6000);
  };
}
export const besselJIv = (n, v, bits) => lipschitz((q, b) => besselJPoint(n, q, b), ONE)(v, bits);
export const siIv = lipschitz(siPoint, RN(1852, 1000));
export const fresnelSIv = lipschitz((q, b) => fresnelPoint(q, b).S, RN(72, 100));
export const fresnelCIv = lipschitz((q, b) => fresnelPoint(q, b).C, RN(78, 100));

// ---- incomplete gamma and beta functions -----------------------------------------------------------

const floorD = (q, b) => floorDyadic(q, b);
const ceilD = (q, b) => ceilDyadic(q, b);
const UNIT = new Iv(ZERO, ONE);
const expIv = (v, wp) => new Iv(expPoint(v.lo, wp).lo, expPoint(v.hi, wp).hi);

/**
 * Σ tₙ for positive terms t₀ = first, tₙ = tₙ₋₁·ratio(n), carried as intervals
 * rounded outward. `settled(n)` returns a bound ρ < 1 on every later ratio once
 * one is known (null before that); the tail is then at most tₙ·ρ/(1 − ρ).
 * `grow` is how many bits the terms may gain before they start to shrink.
 */
function positiveSeries(first, ratio, settled, wp, grow) {
  const b = wp + 16 + grow;
  const eps = pow2(-wp);
  let lo = first;
  let hi = first;
  let sumLo = first;
  let sumHi = first;
  for (let n = 1; ; n++) {
    if (n > 2000000) refuse("budget", "series did not converge within the term budget");
    const rho = settled(n);
    if (rho !== null) {
      const tail = hi.multiply(rho).divide(ONE.subtract(rho));
      if (le(tail, eps)) return new Iv(sumLo, sumHi.add(ceilD(tail, b)));
    }
    const r = ratio(n);
    lo = floorD(lo.multiply(r), b);
    hi = ceilD(hi.multiply(r), b);
    sumLo = sumLo.add(lo);
    sumHi = sumHi.add(hi);
  }
}

/**
 * The regularized lower incomplete gamma function
 *   P(a, x) = γ(a, x)/Γ(a) = 1/Γ(a) · ∫₀ˣ t^(a−1) e^(−t) dt,   a > 0, x ≥ 0,
 * from γ(a, x) = x^a e^(−x) Σ xⁿ/(a(a+1)⋯(a+n)), a series of positive terms.
 * Far to the right, where 1 − P is below the precision asked for, the bound
 * Γ(a, x) ≤ x^(a−1) e^(−x)·x/(x − a + 1) is used instead.
 */
export function gammaPPoint(a, x, bits = 96) {
  if (!gt(a, ZERO)) refuse("domain", `the incomplete gamma function needs a positive shape, got ${a}`);
  if (lt(x, ZERO)) refuse("domain", `the incomplete gamma function needs x ≥ 0, got ${x}`);
  if (x.numerator === 0n) return Iv.point(ZERO);
  const af = a.toNumber();
  const xf = x.toNumber();
  if (xf > af + 1) {
    // an estimate of log2 of the upper tail; only trusted after the certified check below
    const est = ((af - 1) * Math.log(xf) - xf - lgammaFloat(af) + Math.log(xf / (xf - af + 1))) / Math.LN2;
    if (est < -(bits + 12)) {
      const lead = logPoint(x, 64).scale(a.subtract(ONE)).sub(Iv.point(x)).sub(lgammaPoint(a, 64));
      const factor = x.divide(x.subtract(a).add(ONE));
      const bound = expIv(lead, 64).scale(factor);
      if (le(bound.hi, pow2(-(bits + 6)))) return new Iv(ONE.subtract(bound.hi), ONE).roundOut(bits + 4, 6000);
    }
  }
  const grow = Math.max(0, Math.ceil(xf * 1.4427)) + 2;
  const wp = bits + 40 + Math.max(0, Math.ceil(Math.log2(af + 1)));
  const sum = positiveSeries(
    a.reciprocal(),
    (n) => x.divide(a.add(RN(n))),
    (n) => {
      const r = x.divide(a.add(RN(n)));
      return lt(r, ONE) ? r : null;
    },
    wp,
    grow,
  );
  const lead = logPoint(x, wp).scale(a).sub(Iv.point(x)).sub(lgammaPoint(a, wp));
  return (expIv(lead, wp).mul(sum).intersect(UNIT) ?? UNIT).roundOut(bits + 4, 6000);
}

/**
 * The regularized incomplete beta function
 *   I_x(a, b) = 1/B(a, b) · ∫₀ˣ t^(a−1) (1−t)^(b−1) dt,   a, b > 0, 0 ≤ x ≤ 1,
 * from I_x(a, b) = x^a (1−x)^b/(a·B(a, b)) · Σ (a+b)ₙ/(a+1)ₙ · xⁿ, a series of
 * positive terms whose ratios tend to x. For x > 1/2 the reflection
 * I_x(a, b) = 1 − I_(1−x)(b, a) is used, so the ratios tend to at most 1/2.
 */
export function betaIPoint(x, a, b, bits = 96) {
  if (!gt(a, ZERO) || !gt(b, ZERO)) refuse("domain", `the incomplete beta function needs positive parameters, got ${a} and ${b}`);
  if (lt(x, ZERO) || gt(x, ONE)) refuse("domain", `the incomplete beta function needs 0 ≤ x ≤ 1, got ${x}`);
  if (x.numerator === 0n) return Iv.point(ZERO);
  if (x.compareTo(ONE) === 0) return Iv.point(ONE);
  if (gt(x, HALF)) {
    const other = betaIPoint(ONE.subtract(x), b, a, bits);
    return new Iv(ONE.subtract(other.hi), ONE.subtract(other.lo));
  }
  const ab = a.add(b);
  const ratio = (n) => x.multiply(ab.add(RN(n - 1))).divide(a.add(RN(n)));
  // how far the terms climb before the ratios drop below 1 (floats, for the working precision only)
  const [af, bf, xf] = [a.toNumber(), b.toNumber(), x.toNumber()];
  let climb = 0;
  let top = 0;
  for (let n = 1; n < 5000000; n++) {
    const r = (xf * (af + bf + n - 1)) / (af + n);
    if (r <= 1) break;
    climb += Math.log2(r);
    top = Math.max(top, climb);
  }
  const grow = Math.ceil(top) + 2;
  const wp = bits + 40;
  const bLarge = gt(b, ONE);
  const sum = positiveSeries(
    ONE,
    ratio,
    (n) => {
      // the ratios decrease toward x when b > 1 and increase toward x otherwise
      const next = ratio(n + 1);
      const rho = bLarge ? next : max(next, x);
      return lt(rho, ONE) ? rho : null;
    },
    wp,
    grow,
  );
  const lnB = lgammaPoint(a, wp).add(lgammaPoint(b, wp)).sub(lgammaPoint(ab, wp));
  const lead = logPoint(x, wp).scale(a).add(logPoint(ONE.subtract(x), wp).scale(b)).sub(lnB);
  return (expIv(lead, wp).scale(a.reciprocal()).mul(sum).intersect(UNIT) ?? UNIT).roundOut(bits + 4, 6000);
}

// ---- Float64 versions (previews) ------------------------------------------------------------------

const LANCZOS = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
export function gammaFloat(x) {
  if (x < 0.5) return Math.PI / (Math.sin(Math.PI * x) * gammaFloat(1 - x));
  if (Number.isInteger(x) && x <= 171) {
    let r = 1;
    for (let k = 2; k < x; k++) r *= k;
    return r;
  }
  const y = x - 1;
  let a = LANCZOS[0];
  for (let i = 1; i < 9; i++) a += LANCZOS[i] / (y + i);
  const t = y + 7.5;
  return Math.sqrt(2 * Math.PI) * t ** (y + 0.5) * Math.exp(-t) * a;
}
export function lgammaFloat(x) {
  if (!(x > 0)) return NaN;
  if (x < 0.5) return Math.log(Math.PI / Math.sin(Math.PI * x)) - lgammaFloat(1 - x);
  const y = x - 1;
  let a = LANCZOS[0];
  for (let i = 1; i < 9; i++) a += LANCZOS[i] / (y + i);
  const t = y + 7.5;
  return 0.5 * Math.log(2 * Math.PI) + (y + 0.5) * Math.log(t) - t + Math.log(a);
}
export function digammaFloat(x) {
  if (Number.isInteger(x) && x <= 0) return NaN;
  let s = 0;
  while (x < 8) { s -= 1 / x; x += 1; }
  const i = 1 / (x * x);
  return s + Math.log(x) - 0.5 / x - i * (1 / 12 - i * (1 / 120 - i * (1 / 252 - i * (1 / 240 - i / 132))));
}
export function trigammaFloat(x) {
  if (Number.isInteger(x) && x <= 0) return NaN;
  let s = 0;
  while (x < 8) { s += 1 / (x * x); x += 1; }
  const i = 1 / (x * x);
  return s + 1 / x + i / 2 + (i / x) * (1 / 6 - i * (1 / 30 - i * (1 / 42 - i * (1 / 30 - (i * 5) / 66))));
}
/** J_n by the trapezoid rule on its integral over a period, which converges geometrically. */
export function besselJFloat(n, x) {
  const N = 2 * Math.ceil(Math.abs(x)) + 2 * Math.abs(n) + 48;
  let s = 0;
  for (let k = 0; k < N; k++) {
    const t = (2 * Math.PI * k) / N;
    s += Math.cos(n * t - x * Math.sin(t));
  }
  return s / N;
}
const GX = [0.1834346424956498, 0.525532409916329, 0.7966664774136267, 0.9602898564975363];
const GW = [0.362683783378362, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
function gauss(g, a, b, panels) {
  const h = (b - a) / panels;
  let s = 0;
  for (let k = 0; k < panels; k++) {
    const m = a + (k + 0.5) * h;
    for (let i = 0; i < 4; i++) s += GW[i] * (g(m - (GX[i] * h) / 2) + g(m + (GX[i] * h) / 2));
  }
  return (s * h) / 2;
}
export const siFloat = (x) => gauss((t) => (t === 0 ? 1 : Math.sin(t) / t), 0, x, Math.ceil(Math.abs(x) / 2) + 1);
export const fresnelSFloat = (x) => gauss((t) => Math.sin((Math.PI * t * t) / 2), 0, x, Math.ceil(x * x) + 2);
export const fresnelCFloat = (x) => gauss((t) => Math.cos((Math.PI * t * t) / 2), 0, x, Math.ceil(x * x) + 2);
