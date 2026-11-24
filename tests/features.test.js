// asin/acos/cbrt/erf, non-smooth ranges and integrals, tracked ODE steps, simplify, taylor, limit.
import { describe, test, expect } from "bun:test";
import { RationalInterval, Rational } from "@ratmath/core";
import { fn, zeros, ode, simplify, parse, format, enclose } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 0) => num(iv.low) <= x + slack && num(iv.high) >= x - slack;
const width = (iv) => num(iv.high.subtract(iv.low));

describe("asin, acos, odd roots, erf", () => {
  test("values, including the ends of the domain", () => {
    expect(holds(fn("asin(x)").value("1/2", { digits: 30 }).exact(), Math.asin(0.5), 1e-15)).toBe(true);
    expect(holds(fn("asin(x)").value(1).exact(), Math.PI / 2, 1e-15)).toBe(true);
    expect(holds(fn("acos(x)").value(-1).exact(), Math.PI, 1e-15)).toBe(true);
    expect(holds(fn("arccos(x)").value("1/3").exact(), Math.acos(1 / 3), 1e-15)).toBe(true);
    expect(() => fn("asin(x)").value(2).exact()).toThrow(/\[-1, 1\]/);
  });
  test("real odd roots of negative numbers are exact where they can be", () => {
    expect(fn("x^(1/3)").value(-8).exact().toString()).toBe("-2:-2");
    expect(fn("x^(2/3)").value(-8).exact().toString()).toBe("4:4");
    expect(fn("cbrt(x)").value("-27/8").exact().toString()).toBe("-3/2:-3/2");
    expect(fn("x^(1/3)").value(0).exact().toString()).toBe("0:0");
    expect(fn("x^(1/3)").float(-8)).toBeCloseTo(-2, 12);
    expect(() => fn("x^(1/4)").value(-8).exact()).toThrow(/even root/);
  });
  test("erf against known values", () => {
    // erf(1/2), erf(2) to 30 digits
    const half = enclose.erf(new Rational(1n, 2n), 110);
    expect(holds(half, 0.5204998778130465, 1e-16)).toBe(true);
    expect(width(half)).toBeLessThan(1e-30);
    expect(holds(enclose.erf(new Rational(2n), 80), 0.9953222650189527, 1e-16)).toBe(true);
    expect(holds(enclose.erf(new Rational(-12n), 80), -1, 1e-16)).toBe(true);
    expect(fn("erf(x)").float(0.5)).toBeCloseTo(0.5204998778130465, 14);
    expect(fn("erf(x)").float(-3.5)).toBeCloseTo(-0.9999992569016276, 14);
    // ∫_0^1 erf = erf(1) + (e^-1 − 1)/√π
    expect(holds(fn("erf(x)").integral(0, 1).exact(), 0.8427007929497149 + (Math.exp(-1) - 1) / Math.sqrt(Math.PI), 1e-12)).toBe(true);
    expect(fn("erf(x)").derivative().toString()).toBe("2*(exp(-x^2)/sqrt(pi))");
  });
  test("ranges, integrals, derivatives and zeros", () => {
    const r = fn("asin(x)").range(["-1/2", "1/2"]).exact();
    expect(holds(r, Math.asin(0.5)) && holds(r, -Math.asin(0.5))).toBe(true);
    expect(width(r)).toBeLessThan(2 * Math.asin(0.5) + 1e-5);
    expect(holds(fn("cbrt(x)").integral(1, 8).exact(), 11.25, 1e-10)).toBe(true);
    expect(fn("asin(2*x)").derivative().toString()).toBe("2/sqrt(1 - (2*x)^2)");
    expect(fn("cbrt(x)").derivative().toString()).toBe("1/3/cbrt(x)^2");
    expect(zeros("cbrt(x) - 1", [-2, 3]).exact()[0].kind).toBe("exact");
    const z = zeros("asin(x) - 1/2", [-1, 1]).exact();
    expect(z.length).toBe(1);
    expect(num(z[0].lo)).toBeCloseTo(Math.sin(0.5), 6);
  });
});

describe("ranges and integrals where no Taylor model exists", () => {
  test.each([
    ["sqrt(x)", [0, 4], 0, 2],
    ["abs(x)", [-1, 2], 0, 2],
    ["asin(x)", [-1, 1], -Math.PI / 2, Math.PI / 2],
    ["cbrt(x)", [-1, 8], -1, 2],
    ["exp(-1/(x+3)^2)", [-2, 2], Math.exp(-1), Math.exp(-1 / 25)],
  ])("range of %s on %j", (e, iv, lo, hi) => {
    const r = fn(e).range(iv).exact();
    expect(num(r.low)).toBeLessThanOrEqual(lo + 1e-15);
    expect(num(r.high)).toBeGreaterThanOrEqual(hi - 1e-15);
    expect(lo - num(r.low)).toBeLessThan(1e-4);
    expect(num(r.high) - hi).toBeLessThan(1e-4);
  });
  test.each([
    ["sqrt(x)", 0, 4, 16 / 3],
    ["abs(x)", -1, 2, 2.5],
    ["sin(x)/x", 0, 1, 0.946083070367183],
    ["sin(x)/x", -1, 1, 2 * 0.946083070367183],
    ["acos(x)", 0, 1, 1],
  ])("∫ %s from %d to %d", (e, a, b, value) => {
    const r = fn(e).integral(a, b);
    const iv = r.exact();
    expect(holds(iv, value, 1e-15)).toBe(true);
    expect(width(iv)).toBeLessThan(1e-9);
  });
  test("true singularities are still refused", () => {
    expect(() => fn("1/x").integral(-1, 1).exact()).toThrow();
    expect(() => fn("x^x").range([0, 1]).exact()).toThrow();
  });
});

describe("ODE steps that track the initial value", () => {
  test("a decaying solution keeps its digits", () => {
    const sol = ode.solve({ f: "-y", y0: 1, until: 10 }).exact();
    expect(sol.complete).toBe(true);
    expect(holds(sol.final, Math.exp(-10), 1e-18)).toBe(true);
    expect(width(sol.final)).toBeLessThan(1e-11); // was 5.5e-8
  });
  test("a rotation does not wrap", () => {
    const sol = ode.solve({ f: ["v", "-x"], y0: [1, 0], vars: ["x", "v"], until: 12 }).exact();
    const [x, v] = sol.final;
    expect(holds(x, Math.cos(12), 1e-15) && holds(v, -Math.sin(12), 1e-15)).toBe(true);
    expect(Math.max(width(x), width(v))).toBeLessThan(1e-9);
  });
  test("an interval of initial values comes out with its true width", () => {
    const y0 = new RationalInterval(new Rational(9n, 10n), new Rational(11n, 10n));
    const sol = ode.solve({ f: "-y", y0, until: 4 }).exact();
    const f = sol.final;
    expect(holds(f, 0.9 * Math.exp(-4)) && holds(f, 1.1 * Math.exp(-4))).toBe(true);
    expect(width(f)).toBeLessThan(0.2 * Math.exp(-4) * 1.0001);
  });
  test("track: false gives the plain interval steps", () => {
    const sol = ode.solve({ f: "-y", y0: 1, until: 2, track: false }).exact();
    expect(holds(sol.final, Math.exp(-2), 1e-15)).toBe(true);
  });
  test("backward in time", () => {
    const r = ode.solve({ f: "-y", y0: 1, t0: 0, until: -3 });
    const sol = r.exact();
    expect(sol.t0.toString()).toBe("0");
    expect(sol.t1.toString()).toBe("-3");
    expect(holds(sol.final, Math.exp(3), 1e-12)).toBe(true);
    expect(holds(sol.at(-1), Math.E, 1e-13)).toBe(true);
    expect(r.quick.value.y.at(-1)).toBeCloseTo(Math.exp(3), 5);
  });
});

describe("simplify, taylor, limit", () => {
  const s = (e) => format(simplify(parse(e)));
  test("products and sums are flattened and merged", () => {
    expect(s("3*(2*x)*x")).toBe("6*x^2");
    expect(s("2*x + 3*x - x/2")).toBe("9/2*x");
    expect(s("x - (x - 1)")).toBe("1");
    expect(s("(x+1)^2*(x+1)")).toBe("(x + 1)^3");
    expect(s("x/x")).toBe("x/x");
    expect(s("log(x) - log(x)")).toBe("0*log(x)");
    expect(fn("x^3*exp(-x)").derivative().toString()).toBe("3*x^2*exp(-x) - x^3*exp(-x)");
  });
  test("simplify keeps values", () => {
    for (const e of ["x^x", "atan(x)/x", "sin(x)^2*cos(3*x)/(1+x^2)", "-2*x*sin(x) - x^2/3 + 4"]) {
      const f = fn(e);
      const g = fn(simplify(f.ast));
      for (const x of [0.3, 1.7, 2.9]) expect(g.float(x)).toBeCloseTo(f.float(x), 10);
    }
  });
  test("taylor coefficients, exact when rational", () => {
    expect(fn("tan(x)").taylor(0, 7).map((v) => v.low.toString())).toEqual(["0", "1", "0", "1/3", "0", "2/15", "0", "17/315"]);
    expect(fn("1/(1-x)").taylor(0, 4).map((v) => v.low.toString())).toEqual(["1", "1", "1", "1", "1"]);
    const e = fn("exp(x)").taylor(1, 3);
    expect(holds(e[2], Math.E / 2, 1e-15)).toBe(true);
  });
  test("limits at removable points", () => {
    expect(fn("sin(x)/x").limit(0).toString()).toBe("1:1");
    expect(fn("(1 - cos(x))/x^2").limit(0).toString()).toBe("1/2:1/2");
    expect(fn("x^2 + 1").limit(2).toString()).toBe("5:5");
    expect(() => fn("1/x").limit(0)).toThrow();
  });
  test("parser: run-together names and double decimal points", () => {
    expect(format(parse("sinx + lnx"))).toBe("sin(x) + ln(x)");
    expect(() => parse("3.5.2")).toThrow(/two decimal points/);
    expect(format(parse("max(x, 1)"))).toBe("max(x, 1)");
  });
});
