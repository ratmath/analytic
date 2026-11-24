// Internal closed intervals [lo, hi] with Rational endpoints. Exact arithmetic;
// the only widening is the explicit outward rounding in `roundOut`.
import { Rational, RationalInterval } from "@ratmath/core";
import { ZERO, ONE, lt, le, gt, min, max, toQ, log2Approx, floorDyadic, ceilDyadic, sign } from "./rat.js";
import { refuse } from "./errors.js";

export class Iv {
  constructor(lo, hi = lo) {
    if (gt(lo, hi)) [lo, hi] = [hi, lo];
    this.lo = lo;
    this.hi = hi;
  }
  static point(q) {
    return new Iv(q, q);
  }
  static sym(r) {
    const a = r.abs();
    return new Iv(a.negate(), a);
  }
  static from(v) {
    if (v instanceof Iv) return v;
    if (v instanceof RationalInterval) return new Iv(v.low, v.high);
    if (Array.isArray(v) && v.length === 2) return new Iv(toQ(v[0]), toQ(v[1]));
    if (v && typeof v === "object" && "low" in v && "high" in v && !(v instanceof Rational)) {
      return new Iv(toQ(v.low), toQ(v.high));
    }
    return Iv.point(toQ(v));
  }
  get isPoint() {
    return this.lo.compareTo(this.hi) === 0;
  }
  get width() {
    return this.hi.subtract(this.lo);
  }
  get mid() {
    return this.lo.add(this.hi).divide(new Rational(2n));
  }
  get rad() {
    return this.width.divide(new Rational(2n));
  }
  /** max |x| over the interval */
  get mag() {
    return max(this.lo.abs(), this.hi.abs());
  }
  /** min |x| over the interval */
  get mig() {
    if (le(this.lo, ZERO) && le(ZERO, this.hi)) return ZERO;
    return min(this.lo.abs(), this.hi.abs());
  }
  containsZero() {
    return le(this.lo, ZERO) && le(ZERO, this.hi);
  }
  contains(other) {
    const o = other instanceof Iv ? other : Iv.point(other);
    return le(this.lo, o.lo) && le(o.hi, this.hi);
  }
  add(o) {
    o = asIv(o);
    return new Iv(this.lo.add(o.lo), this.hi.add(o.hi));
  }
  sub(o) {
    o = asIv(o);
    return new Iv(this.lo.subtract(o.hi), this.hi.subtract(o.lo));
  }
  neg() {
    return new Iv(this.hi.negate(), this.lo.negate());
  }
  mul(o) {
    o = asIv(o);
    if (this.isPoint && o.isPoint) return Iv.point(this.lo.multiply(o.lo));
    const p = [this.lo.multiply(o.lo), this.lo.multiply(o.hi), this.hi.multiply(o.lo), this.hi.multiply(o.hi)];
    let lo = p[0];
    let hi = p[0];
    for (const v of p) {
      lo = min(lo, v);
      hi = max(hi, v);
    }
    return new Iv(lo, hi);
  }
  scale(q) {
    return new Iv(this.lo.multiply(q), this.hi.multiply(q));
  }
  recip() {
    if (this.containsZero()) refuse("division-by-zero", `cannot take the reciprocal of an interval containing 0 (${this})`);
    return new Iv(this.hi.reciprocal(), this.lo.reciprocal());
  }
  div(o) {
    return this.mul(asIv(o).recip());
  }
  /** Exact image of x ↦ x^n (n ≥ 0 integer). */
  pow(n) {
    if (n === 0) return Iv.point(ONE);
    const a = this.lo.pow(n);
    const b = this.hi.pow(n);
    if (n % 2 === 1) return new Iv(a, b);
    if (this.containsZero()) return new Iv(ZERO, max(a, b));
    return new Iv(min(a, b), max(a, b));
  }
  hull(o) {
    o = asIv(o);
    return new Iv(min(this.lo, o.lo), max(this.hi, o.hi));
  }
  intersect(o) {
    o = asIv(o);
    const lo = max(this.lo, o.lo);
    const hi = min(this.hi, o.hi);
    if (gt(lo, hi)) return null;
    return new Iv(lo, hi);
  }
  /**
   * Outward rounding to dyadic endpoints with about `bits` bits relative to
   * the magnitude of the interval (absolute floor 2^-(bits+absExtra)).
   * Never shrinks the interval.
   */
  roundOut(bits, absBits = bits * 2) {
    const m = this.mag;
    if (m.numerator === 0n) return this;
    const e = log2Approx(m);
    const b = Math.min(bits - e, absBits);
    const lo = floorDyadic(this.lo, b);
    const hi = ceilDyadic(this.hi, b);
    // Keep exact endpoints when they are already simpler than the rounding.
    return new Iv(
      this.lo.denominator <= lo.denominator ? this.lo : lo,
      this.hi.denominator <= hi.denominator ? this.hi : hi,
    );
  }
  toRationalInterval() {
    return new RationalInterval(this.lo, this.hi);
  }
  /** "[lo, hi]" with exact ends when they are short, else decimals rounded outward (for messages). */
  toString() {
    const show = (q, up) => {
      const exact = q.toString();
      if (exact.length <= 24) return exact;
      // 10 significant digits, rounded away from the interval
      const neg = q.numerator < 0n;
      const a = neg ? q.negate() : q;
      let e = 0;
      let scaled = a;
      const TEN = new Rational(10n);
      while (scaled.compareTo(new Rational(10n ** 10n)) >= 0) { scaled = scaled.divide(TEN); e++; }
      while (scaled.numerator !== 0n && scaled.compareTo(new Rational(10n ** 9n)) < 0) { scaled = scaled.multiply(TEN); e--; }
      let m = scaled.numerator / scaled.denominator;
      if (up !== neg && m * scaled.denominator !== scaled.numerator) m += 1n;
      const digits = m.toString();
      const exp = e + digits.length - 1;
      return `${neg ? "-" : ""}${digits[0]}.${digits.slice(1).replace(/0+$/, "") || "0"}${exp ? `e${exp}` : ""}`;
    };
    return `[${show(this.lo, false)}, ${show(this.hi, true)}]`;
  }
}

export function asIv(v) {
  return v instanceof Iv ? v : Iv.point(v);
}

export const IV_ZERO = Iv.point(ZERO);
export const IV_ONE = Iv.point(ONE);

export function signOf(iv) {
  if (gt(iv.lo, ZERO)) return 1;
  if (lt(iv.hi, ZERO)) return -1;
  return 0;
}

export { sign };
