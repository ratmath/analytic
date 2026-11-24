// Cases that once gave a wrong answer, a crash or an unhelpful "possible".
import { describe, test, expect } from "bun:test";
import { zeros, extrema, inflections, fn, simplify, parse, format } from "../index.js";

const num = (x) => x.toNumber();
const mid = (v) => (num(v.low) + num(v.high)) / 2;

describe("the zero function", () => {
  test.each(["x - x", "0", "0*x", "sin(x) - sin(x)", "0*sin(x)", "(x - x)/x"])("zeros of %s are everywhere", (e) => {
    const z = zeros(e, [0, 1]).exact();
    expect(z.length).toBe(1);
    expect(z[0].kind).toBe("everywhere");
    expect(num(z[0].lo)).toBe(0);
    expect(num(z[0].hi)).toBe(1);
  });
  test("a constant has no isolated extrema and no inflections", () => {
    const e = extrema("3", [-1, 1]).exact();
    expect(e.length).toBe(1);
    expect(e[0].kind).toBe("constant");
    expect(inflections("2*x + 1", [-1, 1]).exact()).toEqual([]);
  });
  test("simplify only cancels what is defined everywhere", () => {
    expect(format(simplify(parse("sin(x) - sin(x)")))).toBe("0");
    expect(format(simplify(parse("log(x) - log(x)")))).not.toBe("0");
    expect(format(simplify(parse("x/x")))).not.toBe("1");
  });
});

describe("large and tiny values", () => {
  test("exp(100) and exp(1000)", () => {
    const v = fn("exp(x)").value(100).exact();
    expect(mid(v) / Math.exp(100)).toBeCloseTo(1, 12);
    const big = fn("exp(x)").value(1000, { digits: 20 }).exact();
    expect(big.low.toString().split("/")[0].length).toBeGreaterThan(430);
  });
  test("2^400", () => {
    const v = fn("2^x").value(400).exact();
    expect(mid(v) / 2 ** 400).toBeCloseTo(1, 12);
  });
  test("exp(-500) keeps relative digits", () => {
    const v = fn("exp(x)").value(-500).exact();
    expect(num(v.low)).toBeGreaterThan(0);
    const rel = num(v.high.subtract(v.low).divide(v.low));
    expect(rel).toBeLessThan(1e-15);
  });
  test("log of 10^-100 and 10^-300", () => {
    expect(mid(fn("log(x)").value("1/1" + "0".repeat(100)).exact())).toBeCloseTo(-100 * Math.LN10, 9);
    expect(mid(fn("log(x)").value("1/1" + "0".repeat(300)).exact())).toBeCloseTo(-300 * Math.LN10, 9);
  });
  test("a high-precision call does not slow down later ones", () => {
    fn("sin(pi) + 0*x").value(0).exact(); // drives π to thousands of bits
    const t = Date.now();
    const z = zeros("x*sin(1/x)", ["1/50", 1]).exact();
    expect(z.length).toBe(15);
    expect(z.every((r) => r.unique)).toBe(true);
    expect(Date.now() - t).toBeLessThan(4000);
  });
});

describe("zeros that land on a bisection point", () => {
  test.each([
    ["exp(x) - e", [0, 2], [1]],
    ["sin(pi*x)", ["1/2", "7/2"], [1, 2, 3]],
    ["cos(pi*x/2)", [0, 4], [1, 3]],
    ["exp(2*x) - e", [0, 1], [0.5]],
  ])("%s is proven, not just possible", (e, iv, at) => {
    const z = zeros(e, iv).exact();
    expect(z.length).toBe(at.length);
    z.forEach((r, i) => {
      expect(r.unique).toBe(true);
      expect(num(r.lo)).toBeLessThanOrEqual(at[i] + 1e-9);
      expect(num(r.hi)).toBeGreaterThanOrEqual(at[i] - 1e-9);
    });
  });
  test("extrema of x*exp(-x) and inflections of exp(-x^2) are unique and not doubled", () => {
    const e = extrema("x*exp(-x)", [0, 5]).exact();
    expect(e.length).toBe(1);
    expect(e[0].kind).toBe("max");
    expect(e[0].unique).toBe(true);
    const f = inflections("exp(-x^2)", [-3, 3]).exact();
    expect(f.length).toBe(2);
  });
});
