// Small helpers on Core Rationals: coercion, comparisons, dyadic rounding.
import { Rational, Integer, Fraction } from "@ratmath/core";
import { refuse } from "./errors.js";

export const ZERO = new Rational(0n);
export const ONE = new Rational(1n);
export const TWO = new Rational(2n);
export const HALF = new Rational(1n, 2n);

export function rat(n, d = 1n) {
  return new Rational(BigInt(n), BigInt(d));
}

/** Coerce a Core number, bigint, integer JS number or string to a Rational. */
export function toQ(v) {
  if (v instanceof Rational) return v;
  if (typeof v === "bigint") return new Rational(v);
  if (typeof v === "number") {
    if (!Number.isSafeInteger(v)) {
      refuse("not-exact", `JS number ${v} is not an exact integer; pass a Rational (R\`...\`) or a string such as "1/10"`);
    }
    return new Rational(BigInt(v));
  }
  if (typeof v === "string") return Rational.from(v);
  if (v instanceof Integer) return new Rational(v.value);
  if (v instanceof Fraction) return new Rational(v.numerator, v.denominator);
  if (v && typeof v === "object" && typeof v.numerator === "bigint" && typeof v.denominator === "bigint") {
    return new Rational(v.numerator, v.denominator);
  }
  refuse("not-a-number", `expected a rational number, got ${describeValue(v)}`);
}

export function describeValue(v) {
  if (v === null || v === undefined) return String(v);
  if (typeof v === "object") return v.constructor?.name ?? "object";
  return `${typeof v} ${String(v)}`;
}

export const cmp = (a, b) => a.compareTo(b);
export const lt = (a, b) => a.compareTo(b) < 0;
export const le = (a, b) => a.compareTo(b) <= 0;
export const gt = (a, b) => a.compareTo(b) > 0;
export const ge = (a, b) => a.compareTo(b) >= 0;
export const eq = (a, b) => a.compareTo(b) === 0;
export const min = (a, b) => (le(a, b) ? a : b);
export const max = (a, b) => (ge(a, b) ? a : b);
export const isZero = (a) => a.numerator === 0n;
export const sign = (a) => (a.numerator > 0n ? 1 : a.numerator < 0n ? -1 : 0);

export function floorDiv(a, b) {
  // b > 0
  if (a >= 0n) return a / b;
  return -((-a + b - 1n) / b);
}

export function bitLen(n) {
  if (n < 0n) n = -n;
  return n === 0n ? 0 : n.toString(2).length;
}

/** Approximate base-2 exponent of |q| (floor(log2|q|) up to ±1); 0 → -Infinity. */
export function log2Approx(q) {
  if (q.numerator === 0n) return -Infinity;
  return bitLen(q.numerator) - bitLen(q.denominator);
}

/** Largest k/2^bits ≤ q. */
export function floorDyadic(q, bits) {
  if (bits < 0) {
    const s = 1n << BigInt(-bits);
    return new Rational(floorDiv(q.numerator, q.denominator * s) * s);
  }
  const s = 1n << BigInt(bits);
  return new Rational(floorDiv(q.numerator * s, q.denominator), s);
}

/** Smallest k/2^bits ≥ q. */
export function ceilDyadic(q, bits) {
  return floorDyadic(q.negate(), bits).negate();
}

/** Nearest-ish dyadic with denominator 2^bits (floor of q + 1/2 ulp). */
export function roundDyadic(q, bits) {
  // bits < 0 rounds to a multiple of 2^-bits (numbers too large to need a fraction)
  const half = bits >= 0 ? new Rational(1n, 1n << BigInt(bits + 1)) : new Rational(1n << BigInt(-bits - 1));
  return floorDyadic(q.add(half), bits);
}

export function factorial(n) {
  let f = 1n;
  for (let i = 2n; i <= BigInt(n); i++) f *= i;
  return f;
}

export function powQ(q, n) {
  let r = ONE;
  for (let i = 0; i < n; i++) r = r.multiply(q);
  return r;
}

/** Integer square root: largest s with s*s ≤ n (n ≥ 0). */
export function isqrt(n) {
  if (n < 0n) throw new RangeError("isqrt of negative");
  if (n < 2n) return n;
  let x = 1n << BigInt(Math.ceil(bitLen(n) / 2));
  while (true) {
    const y = (x + n / x) >> 1n;
    if (y >= x) break;
    x = y;
  }
  while (x * x > n) x -= 1n;
  while ((x + 1n) * (x + 1n) <= n) x += 1n;
  return x;
}
