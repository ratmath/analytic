import { describe, test, expect } from "bun:test";
import { R, Rational } from "@ratmath/core";
import {
  TM, Domain, exp, sin, cos, tan, log, log1p, atan, sqrt, sinh, cosh, tanh, power, series,
  createScope, AnalyticError,
} from "../index.js";
import { expectEncloses, dec } from "./helpers.js";

const D = Domain(R`0:1/2`);
const x = TM.x(D, { order: 12 });
const s = createScope({ digits: 30 });

const overlaps = (a, b) => a.low.compareTo(b.high) <= 0 && b.low.compareTo(a.high) <= 0;

describe("domains", () => {
  test("centre defaults to the midpoint and can be given", () => {
    expect(D.centre.toString()).toBe("1/4");
    expect(Domain(R`0:1`, { centre: R`0` }).centre.toString()).toBe("0");
    expect(Domain(0, 2).centre.toString()).toBe("1");
    expect(() => Domain(R`0:1`, { centre: 2 })).toThrow(AnalyticError);
  });
});

describe("exact polynomial arithmetic", () => {
  const p = TM.polynomial(D, [1, -2, R`1/3`]); // 1 − 2x + x²/3
  test("polynomials are exact and evaluate exactly", () => {
    expect(p.isExact).toBe(true);
    expect(p.at(R`1/2`).toString()).toBe(new Rational(1n).subtract(new Rational(1n)).add(new Rational(1n, 12n)).toString() + ":" + "1/12");
    expect(p.coefficientsInX.map(String)).toEqual(["1", "-2", "1/3"]);
  });
  test("products are exact below the order and match expansion", () => {
    const q = x.add(1).multiply(x.subtract(1));
    expect(q.isExact).toBe(true);
    expect(q.coefficientsInX.map(String)).toEqual(["-1", "0", "1"]);
    expect(x.pow(3).at(R`1/2`).low.toString()).toBe("1/8");
  });
  test("truncation past the order moves into the remainder", () => {
    const y = TM.x(D, { order: 3 });
    const q = y.pow(5);
    expect(q.degree).toBeLessThanOrEqual(3);
    expect(q.isExact).toBe(false);
    for (const v of [R`0`, R`1/7`, R`1/2`]) {
      const exact = v.pow(5);
      const iv = q.at(v);
      expect(iv.low.compareTo(exact) <= 0 && iv.high.compareTo(exact) >= 0).toBe(true);
    }
  });
  test("range of an exact polynomial is tight (Bernstein)", () => {
    const q = TM.polynomial(Domain(R`-1:1`), [0, -1, 0, 1]); // x³ − x, extremes ±2/(3√3) ≈ ±0.3849
    const r = q.range();
    expect(r.high.toNumber()).toBeGreaterThanOrEqual(0.38490017945975);
    expect(r.high.toNumber()).toBeLessThan(0.39);
  });
  test("exact derivative and integral of polynomials", () => {
    const q = TM.polynomial(Domain(R`0:1`), [0, 0, 3]);
    expect(q.derivative().coefficientsInX.map(String)).toEqual(["0", "6"]);
    expect(q.integral().toString()).toBe("1:1");
    expect(q.integral(R`0`, R`1/2`).toString()).toBe("1/8:1/8");
  });
});

describe("elementary models (30-digit references)", () => {
  test("exp(sin x)·x at 1/4, its range and integral on [0, 1/2]", () => {
    const f = exp(sin(x)).multiply(x);
    expectEncloses(f.at(R`1/4`), "0.3201740893610436814935847564882899024776", "1e-10");
    const r = f.range();
    expect(r.high.compareTo(dec("0.8075731482210418716585004627931453913091")) >= 0).toBe(true);
    expect(r.high.toNumber() - 0.80757314822104).toBeLessThan(1e-9);
    expectEncloses(f.integral(), "0.1740801318824638816807158502950383942545", "1e-10");
    // ∫ via the antiderivative model: F(1/2) − F(0)
    const F = f.integrate();
    const v = F.at(R`1/2`).subtract(F.at(R`0`));
    expectEncloses(v, "0.1740801318824638816807158502950383942545", "1e-9");
  });
  test("higher order on a smaller domain gives ~30 digits", () => {
    const y = TM.x(Domain(R`0:1/16`), { order: 24, bits: 120 });
    expectEncloses(exp(y).at(R`1/16`), "1.064494458917859429563390594642889673101", "1e-30");
  });
  test("log1p, atan, sqrt, tan, hyperbolics at 1/2", () => {
    expectEncloses(log1p(x).at(R`1/2`), "0.405465108108164381978013115464349136572", "1e-8");
    expectEncloses(atan(x).at(R`1/2`), "0.4636476090008061162142562314612144020", "1e-8");
    expectEncloses(sqrt(x.add(1)).at(R`1/2`), "1.224744871391589049098642037352945695983", "1e-8");
    expectEncloses(tan(x).at(R`1/2`), "0.5463024898437905132551794657802853832976", "1e-8");
    expectEncloses(tanh(x).at(R`1/2`), "0.4621171572600097585023184836436725487303", "1e-8");
    expectEncloses(cosh(x).at(R`1/2`), "1.127625965206380785226225161402672012547", "1e-8");
    expectEncloses(sinh(x).at(R`1/2`), "0.5210953054937473616224256264114915591059", "1e-8");
  });
  test("composition: log(1 + sqrt(1 + x)) at 1/4 and x^(3/2)", () => {
    const f = log(sqrt(x.add(1)).add(1));
    expectEncloses(f.at(R`1/4`), "0.7504882946188650330760446188149287013301", "1e-8");
    const g = power(TM.x(Domain(R`3/2:5/2`), { order: 12 }), R`3/2`);
    expectEncloses(g.at(R`2`), "2.828427124746190097603377448419396157139", "1e-5");
  });
  test("division and reciprocal", () => {
    const f = TM.constant(D, 1).divide(x.multiply(x).add(1));
    expectEncloses(f.integral(), "0.4636476090008061162142562314612144020", "1e-7"); // ∫_0^{1/2} 1/(1+x²) = atan(1/2)
  });
});

describe("refusals instead of invalid bounds", () => {
  test("log and sqrt near or below zero", () => {
    const y = TM.x(Domain(R`-1/4:1/4`));
    expect(() => log(y)).toThrow(/positive/);
    expect(() => sqrt(y)).toThrow(/above 0/);
    try {
      log(y);
    } catch (e) {
      expect(e).toBeInstanceOf(AnalyticError);
      expect(e.code).toBe("domain");
    }
  });
  test("division by a model whose range contains 0", () => {
    const y = TM.x(Domain(R`-1:1`));
    expect(() => TM.constant(y.domain, 1).divide(y)).toThrow(/contains 0/);
    expect(() => tan(TM.x(Domain(R`1:2`)))).toThrow(/contains 0/);
  });
  test("outside the domain, different domains, derivative of a non-exact model", () => {
    expect(() => x.at(R`1`)).toThrow(/outside/);
    expect(() => x.add(TM.x(Domain(R`0:1`)))).toThrow(/different domains/);
    expect(() => sin(x).derivative()).toThrow(/derivative/);
  });
});

describe("user series with tail rules", () => {
  test("ratio rule: Σ (x/2)^k = 2/(2 − x)", () => {
    const g = series(D, { coefficient: (k) => R`1/${2 ** k}`, rule: "ratio", q: R`1/4`, centre: R`0` });
    expectEncloses(g.at(R`1/2`), "1.333333333333333333333333333333333333333", "1e-7");
    expect(g.assumed).toBe(true);
    expect(g.describe()).toMatch(/assumed/);
  });
  test("ratio rule refuses when the checked terms violate it", () => {
    expect(() => series(Domain(R`0:3`, { centre: R`0` }), { coefficient: (k) => R`1/${2 ** k}`, rule: "ratio", q: R`1/2` })).toThrow(/ratio rule fails/);
  });
  test("alternating rule: atan series on [0, 1/2] about 0", () => {
    const g = series(Domain(R`0:1/2`, { centre: R`0` }), {
      coefficient: (k) => (k % 2 === 0 ? 0 : R`${(k % 4 === 1 ? 1 : -1)}/${k}`),
      order: 15,
      rule: "explicit",
      error: R`1/${17 * 2 ** 17}`,
    });
    expectEncloses(g.at(R`1/2`), "0.4636476090008061162142562314612144020", "1e-5");
    const alt = series(Domain(R`0:1/2`, { centre: R`0` }), { coefficient: (k) => R`${k % 2 ? -1 : 1}/${2 ** k}`, order: 10, rule: "alternating" });
    expectEncloses(alt.at(R`1/2`), "0.8", "1e-3"); // Σ (−x/2)^k at 1/2 = 1/(1 + 1/4)
    expect(() => series(Domain(R`-1/2:1/2`, { centre: R`0` }), { coefficient: (k) => R`${k % 2 ? -1 : 1}/${2 ** k}`, rule: "alternating" })).toThrow(/alternate/);
  });
  test("Lagrange rule (RatTree's eˣ preset: M = 3^⌈|x|⌉)", () => {
    const g = series(Domain(R`0:1`, { centre: R`0` }), { coefficient: (k) => R`1/${factorialN(k)}`, order: 14, rule: "lagrange", M: 3 });
    expectEncloses(g.at(R`1`), "2.718281828459045235360287471352662497757", "1e-11");
  });
});

describe("soundness sweep: models agree with independent point enclosures", () => {
  const fns = [
    ["exp(sin)", (m) => exp(sin(m)), (v) => s.exp(s.sin(v))],
    ["log(1+x²)", (m) => log(m.multiply(m).add(1)), null],
    ["atan(3x−1)", (m) => atan(m.multiply(3).subtract(1)), (v) => s.atan(v.multiply(new Rational(3n)).subtract(new Rational(1n)))],
    ["cos(5x)", (m) => cos(m.multiply(5)), (v) => s.cos(v.multiply(new Rational(5n)))],
  ];
  const doms = [R`0:1/2`, R`-1:-1/3`, R`2:9/4`];
  for (const [name, fm, fp] of fns) {
    if (!fp) continue;
    for (const d of doms) {
      test(`${name} on ${d}`, () => {
        const m = fm(TM.x(Domain(d), { order: 10 }));
        for (let i = 0; i <= 6; i++) {
          const v = d.low.add(d.high.subtract(d.low).multiply(new Rational(BigInt(i), 6n)));
          const a = m.at(v);
          const b = fp(v);
          expect(overlaps(a, b)).toBe(true);
        }
      });
    }
  }
});

describe("scope for function workers", () => {
  test("same names work on numbers, intervals and models", () => {
    expect(s.exp(R`1`).constructor.name).toBe("RationalInterval");
    expect(s.exp(TM.x(D)).constructor.name).toBe("TaylorModel");
    expect(s.bits).toBe(108);
  });
  test("model, integral and range helpers", () => {
    const f = (t) => s.exp(s.sin(t));
    expectEncloses(s.integral(f, 0, 1), "1.631869608418051348137161723744681088397", "1e-9");
    expectEncloses(s.integral((t) => s.TM.constant(t.domain, 1).divide(t.multiply(t).add(1)), 0, 1, { pieces: 8 }), "0.7853981633974483096156608458198757210493", "1e-9");
    const r = s.range(f, R`0:1`);
    expect(r.low.compareTo(new Rational(1n)) <= 0).toBe(true);
    expect(r.high.toNumber()).toBeGreaterThan(2.3197768);
    expect(r.high.toNumber()).toBeLessThan(2.31978);
  });
});

function factorialN(k) {
  let f = 1n;
  for (let i = 2n; i <= BigInt(k); i++) f *= i;
  return f;
}
