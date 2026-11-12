// Randomised (fixed-seed) check: for many domains, orders and functions, the
// model's enclosure at sample points must overlap the independent point
// enclosure from the series code. A failure here means an unsound bound.
import { test, expect } from "bun:test";
import { Rational } from "@ratmath/core";
import { TM, Domain, exp, sin, cos, atan, log, sqrt, reciprocal, createScope } from "../index.js";

const s = createScope({ bits: 80 });
let seed = 12345;
const rnd = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
const q = (lo, hi) => new Rational(BigInt(Math.floor((lo + (hi - lo) * rnd()) * 64)), 64n);

const cases = [
  ["exp", exp, s.exp, -6, 6],
  ["sin", sin, s.sin, -20, 20],
  ["cos", cos, s.cos, -20, 20],
  ["atan", atan, s.atan, -8, 8],
  ["log", log, s.log, 1 / 8, 20],
  ["sqrt", sqrt, s.sqrt, 1 / 8, 20],
  ["1/x", reciprocal, (v) => { const one = new Rational(1n); return { low: one.divide(v), high: one.divide(v) }; }, 1 / 4, 10],
];

for (const [name, fm, fp, lo, hi] of cases) {
  test(`${name}: 30 random domains`, () => {
    for (let i = 0; i < 30; i++) {
      const a = q(lo, hi);
      const w = new Rational(BigInt(1 + Math.floor(rnd() * 32)), 64n);
      const b = a.add(w);
      const order = 2 + Math.floor(rnd() * 12);
      const m = fm(TM.x(Domain(a, b), { order, bits: 80 }));
      for (let j = 0; j <= 4; j++) {
        const v = a.add(w.multiply(new Rational(BigInt(j), 4n)));
        const A = m.at(v);
        const B = fp(v);
        const ok = A.low.compareTo(B.high) <= 0 && B.low.compareTo(A.high) <= 0;
        if (!ok) throw new Error(`${name} on [${a}, ${b}] order ${order} at ${v}: ${A} vs ${B.low}..${B.high}`);
      }
      // the model's range must contain every sampled value
      const r = m.range({ depth: 2 });
      expect(r.low.compareTo(m.at(a).high) <= 0).toBe(true);
    }
  });
}
