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
