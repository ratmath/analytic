import { Rational } from "@ratmath/core";
import { expect } from "bun:test";

/** Rational from a decimal string such as "-1.23e-5". */
export function dec(s) {
  let [m, e = "0"] = s.split("e");
  const neg = m.startsWith("-");
  if (neg) m = m.slice(1);
  const [i, f = ""] = m.split(".");
  let n = BigInt(i + f);
  let d = 10n ** BigInt(f.length);
  const ex = Number(e);
  if (ex > 0) n *= 10n ** BigInt(ex);
  else d *= 10n ** BigInt(-ex);
  return new Rational(neg ? -n : n, d);
}

/**
 * The enclosure must contain the reference (given to ≥ 35 significant digits,
 * so allow its last-digit error) and be narrower than `maxWidth`.
 */
export function expectEncloses(iv, ref, maxWidth = "1e-25") {
  const r = dec(ref);
  const slack = r.abs().multiply(dec("1e-34")).add(dec("1e-60"));
  const lo = iv.low ?? iv.lo;
  const hi = iv.high ?? iv.hi;
  expect(lo.compareTo(r.add(slack)) <= 0).toBe(true);
  expect(hi.compareTo(r.subtract(slack)) >= 0).toBe(true);
  expect(hi.subtract(lo).compareTo(dec(maxWidth)) <= 0).toBe(true);
}
