import { describe, test, expect } from "bun:test";
import { R } from "@ratmath/core";
import { enclose, fn, zeros, bernoulli, field } from "../index.js";

const num = (x) => x.toNumber();
const near = (iv, x, rel = 1e-14) => num(iv.low) <= x + Math.abs(x) * rel && num(iv.high) >= x - Math.abs(x) * rel && num(iv.high.subtract(iv.low)) <= Math.abs(x) * 1e-12 + 1e-25;

describe("gamma and its relatives", () => {
  test("exact at positive integers, certified elsewhere (values from mpmath)", () => {
    expect(enclose.gamma(R`5`).toString()).toBe("24:24");
    expect(near(enclose.gamma(R`1/2`), 1.7724538509055160273)).toBe(true);
    expect(near(enclose.gamma(R`7/3`), 1.1906393487589989483)).toBe(true);
    expect(near(enclose.gamma(R`-3/2`), 2.3632718012073547031)).toBe(true);
    expect(near(enclose.gamma(R`-7/3`), -1.3057565844468861163)).toBe(true);
    expect(near(enclose.lgamma(R`300`), 1409.2020674704117875)).toBe(true);
    expect(near(enclose.digamma(R`1/2`), -1.9635100260214234794)).toBe(true);
    expect(near(enclose.polygamma(1, R`5`), 0.22132295573711532536)).toBe(true);
    expect(near(enclose.polygamma(2, R`7/3`), -0.27837239940160755246, 1e-13)).toBe(true);
    expect(near(enclose.beta(R`2/3`, R`5/2`), 0.76760393515609169718, 1e-13)).toBe(true);
  });
  test("poles are refused", () => {
    expect(() => enclose.gamma(R`-2`)).toThrow(/pole/);
    expect(() => enclose.gamma(R`-1/2:1/2`)).toThrow(/pole/);
    expect(() => enclose.lgamma(R`-1`)).toThrow(/positive/);
  });
  test("over an interval the enclosure holds every value", () => {
    const g = enclose.gamma(R`1:2`);
    expect(num(g.low)).toBeLessThanOrEqual(0.8856031944108887);
    expect(num(g.high)).toBeGreaterThanOrEqual(1);
    const neg = enclose.gamma(R`-7/4:-5/4`);
    expect(num(neg.low)).toBeLessThanOrEqual(2.3632718012073547);
    expect(num(neg.high)).toBeGreaterThanOrEqual(3.6256099082219083);
  });
  test("Bernoulli numbers", () => {
    expect([0, 1, 2, 4, 12].map((m) => bernoulli(m).toString())).toEqual(["1", "-1/2", "1/6", "-1/30", "-691/2730"]);
    expect(bernoulli(7).toString()).toBe("0");
  });
});

describe("Bessel, sine and Fresnel integrals", () => {
  test("values (from mpmath)", () => {
    expect(near(enclose.besselJ(0, R`5`), -0.17759677131433830435)).toBe(true);
    expect(near(enclose.besselJ(2, R`-7/3`), 0.41981202559204988667)).toBe(true);
    expect(near(enclose.besselJ(-3, R`30`), -0.12921122875972498304, 1e-12)).toBe(true);
    expect(near(enclose.besselJ(7, R`1000`), -0.0053217830764436153538, 1e-10)).toBe(true);
    expect(enclose.besselJ(0, R`0`).toString()).toBe("1:1");
    expect(near(enclose.Si(R`5`), 1.5499312449446741373)).toBe(true);
    expect(near(enclose.Si(R`-7/3`), -1.73277587530360001, 1e-13)).toBe(true);
    expect(near(enclose.fresnelS(R`5`), 0.49919138191711688675, 1e-13)).toBe(true);
    expect(near(enclose.fresnelC(R`1/2`), 0.49234422587144639288, 1e-13)).toBe(true);
    expect(near(enclose.erfc(R`3`), 0.000022090496998585441373, 1e-10)).toBe(true);
  });
});

describe("special functions in formulas", () => {
  test("parsing, previews and derivatives", () => {
    expect(fn("gamma(x)").float(4.3)).toBeCloseTo(8.8553433604540349144, 9);
    expect(fn("besselJ(2, x)").float(7.7)).toBeCloseTo(-0.18746492781384411027, 10);
    expect(fn("beta(x, 2)").float(1.5)).toBeCloseTo(0.26666666666666666667, 10);
    expect(fn("erfc(x)").float(0.4)).toBeCloseTo(0.57160764495333152355, 10);
    expect(String(fn("gamma(x)").derivative())).toBe("gamma(x)*digamma(x)");
    expect(String(fn("besselJ(0, x)").derivative())).toBe("-besselJ(1, x)");
    expect(String(fn("fresnelS(x)").derivative())).toBe("sin(1/2*(pi*x^2))");
    expect(() => fn("besselJ(x, 2)")).toThrow(/whole number/);
    expect(() => fn("beta(x)")).toThrow(/two arguments/);
  });
  test("integrals, zeros and the gamma integral itself", () => {
    const j = fn("besselJ(0, x)").integral(0, 10).exact();
    expect(near(j, 1.0670113039567362, 1e-12)).toBe(true);
    const s = fn("Si(x)").integral(0, 5).exact();
    expect(num(s.low) <= 7.0333184101866 && num(s.high) >= 7.0333184101866).toBe(true);
    const z = zeros("besselJ(0, x)", [0, 10]).exact();
    expect(z.length).toBe(3);
    expect(Math.abs(num(z[0].lo) - 2.404825557695773)).toBeLessThan(1e-9);
    const g = fn("t^(3/2)*exp(-t)", { variable: "t" }).improperIntegral(0, "inf").exact();
    const direct = enclose.gamma(R`5/2`);
    expect(num(g.low) <= num(direct.low) && num(g.high) >= num(direct.high)).toBe(true);
  });
  test("in several variables", () => {
    const v = field("gamma(x)*besselJ(1, y)", ["x", "y"]).integral({ x: [1, 2], y: [0, 1] }, { digits: 4 }).exact();
    expect(num(v.low) <= 0.21666282 && num(v.high) >= 0.21666282).toBe(true);
  });
});

describe("incomplete gamma and beta functions", () => {
  const inside = (iv, q) => iv.low.compareTo(q) <= 0 && iv.high.compareTo(q) >= 0;
  const overlap = (a, b) => a.low.compareTo(b.high) <= 0 && b.low.compareTo(a.high) <= 0;
  const narrow = (iv, bits = 90) => iv.high.subtract(iv.low).compareTo(R`1`.divide(R`2`.pow(bits))) < 0;
  test("gammaP against closed forms", () => {
    // P(1, x) = 1 − e^(−x)
    const e = enclose.exp(R`-7/3`, 120);
    const p1 = enclose.gammaP(1, R`7/3`);
    expect(overlap(p1, { low: R`1`.subtract(e.high), high: R`1`.subtract(e.low) })).toBe(true);
    expect(narrow(p1)).toBe(true);
    // P(1/2, x²) = erf(x)
    expect(overlap(enclose.gammaP(R`1/2`, R`9/4`), enclose.erf(R`3/2`, 120))).toBe(true);
    // P(n, x) = 1 − e^(−x) Σ_{k<n} x^k/k!
    const x = R`13/2`;
    let s = R`0`;
    let t = R`1`;
    for (let k = 0; k < 6; k++) {
      s = s.add(t);
      t = t.multiply(x).divide(R`${k + 1}`);
    }
    const ex = enclose.exp(x.negate(), 120);
    expect(overlap(enclose.gammaP(6, x), { low: R`1`.subtract(ex.high.multiply(s)), high: R`1`.subtract(ex.low.multiply(s)) })).toBe(true);
    expect(near(enclose.gammaP(5, 3), 0.18473675547622792)).toBe(true);
    expect(near(enclose.gammaP(500, 480), 0.1862819731903246, 1e-12)).toBe(true);
  });
  test("gammaP at the ends, far out and over intervals", () => {
    expect(enclose.gammaP(R`7/2`, 0).toString()).toBe("0:0");
    const far = enclose.gammaP(3, 300);
    expect(far.high.toString()).toBe("1");
    expect(narrow(far)).toBe(true);
    const q = enclose.gammaQ(10, 50);
    expect(num(q.low)).toBeGreaterThan(1.2e-12);
    expect(num(q.high)).toBeLessThan(1.3e-12);
    const iv = enclose.gammaP(2, [1, 2]);
    expect(inside(iv, enclose.gammaP(2, R`3/2`).low)).toBe(true);
    expect(() => enclose.gammaP(0, 1)).toThrow(/positive shape/);
    expect(() => enclose.gammaP(1, -1)).toThrow(/x ≥ 0/);
    expect(() => enclose.gammaP([1, 2], 1)).toThrow(/exact number/);
  });
  test("betaI against closed forms", () => {
    // whole-number parameters give a binomial sum: I_x(2, 3) = 6x² − 8x³ + 3x⁴
    const x = R`1/3`;
    const exact = R`6`.multiply(x.pow(2)).subtract(R`8`.multiply(x.pow(3))).add(R`3`.multiply(x.pow(4)));
    expect(exact.toString()).toBe("11/27");
    expect(inside(enclose.betaI(x, 2, 3), exact)).toBe(true);
    expect(narrow(enclose.betaI(x, 2, 3))).toBe(true);
    // I_x(a, 1) = x^a
    expect(inside(enclose.betaI(R`4/5`, 3, 1), R`64/125`)).toBe(true);
    // I_x(1/2, 1/2) = (2/π)·asin(√x)
    expect(near(enclose.betaI(R`3/10`, R`1/2`, R`1/2`), 0.36901011956554536, 1e-13)).toBe(true);
    // reflection
    const a = enclose.betaI(R`7/10`, R`5/2`, R`4/3`);
    const b = enclose.betaI(R`3/10`, R`4/3`, R`5/2`);
    expect(overlap(a, { low: R`1`.subtract(b.high), high: R`1`.subtract(b.low) })).toBe(true);
    expect(near(enclose.betaI(R`1/4`, 100, 300), 0.5076806528982708, 1e-12)).toBe(true);
  });
  test("betaI at the ends, with large parameters and over intervals", () => {
    expect(enclose.betaI(0, 2, 3).toString()).toBe("0:0");
    expect(enclose.betaI(1, 2, 3).toString()).toBe("1:1");
    expect(narrow(enclose.betaI(R`997/1000`, 500, R`1/2`))).toBe(true);
    const iv = enclose.betaI([R`1/4`, R`1/3`], 2, 3);
    expect(inside(iv, R`11/27`)).toBe(true);
    expect(inside(iv, enclose.betaI(R`3/10`, 2, 3).high)).toBe(true);
    expect(() => enclose.betaI(R`3/2`, 2, 3)).toThrow(/0 ≤ x ≤ 1/);
    expect(() => enclose.betaI(R`1/2`, 0, 3)).toThrow(/positive parameters/);
  });
});
