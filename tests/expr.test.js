import { describe, test, expect } from "bun:test";
import { R, Rational } from "@ratmath/core";
import { parse, format, differentiate, compileFloat, fn, Domain, AnalyticError } from "../index.js";

const F = (text, x) => compileFloat(typeof text === "string" ? parse(text) : text)({ x });

describe("parser (graphics' grammar)", () => {
  test("precedence, implicit products, right-associative powers", () => {
    expect(F("2x + 3(x+1)", 2)).toBe(13);
    expect(F("-x^2", 3)).toBe(-9);
    expect(F("2^3^2", 0)).toBe(512);
    expect(F("2sin(x)", 0)).toBe(0);
    expect(F("x**2", 5)).toBe(25);
    expect(parse("0.1").value.toString()).toBe("1/10");
  });
  test("analytic adds atan, log1p, sinh, cosh, tanh", () => {
    expect(F("atan(1)", 0)).toBeCloseTo(Math.PI / 4, 15);
    expect(F("log1p(x) + sinh(x) + cosh(x) + tanh(x)", 0)).toBe(1);
  });
  test("format parses back to the same values", () => {
    const xs = [0.3, 1.7, 2.9];
    for (const t of ["x - (x - 1)", "x/(x/2)", "-(x+1)^2", "(-x)^3", "2^-x", "1/3 - x/7", "exp(sin(x))*x", "x - -2"]) {
      const back = format(parse(t));
      for (const x of xs) expect(F(back, x)).toBeCloseTo(F(t, x), 12);
    }
  });
});

describe("symbolic derivative", () => {
  const cases = [
    "x^3 + 2x - 1/x", "sin(x)^2", "exp(sin(x))*x", "sqrt(1 + x^2)", "atan(x^2)", "log(x)/x",
    "tan(x)", "x^x", "2^x", "x^(1/3)", "sinh(x)*cosh(x) - tanh(x)", "log1p(x^2)", "cos(pi*x)", "e^x",
  ];
  for (const text of cases) {
    test(`d/dx ${text} matches a central difference`, () => {
      const f = fn(text);
      const d = f.derivative();
      for (const x of [0.4, 0.9, 1.6]) {
        const h = 1e-5;
        const num = (f.float(x + h) - f.float(x - h)) / (2 * h);
        expect(Math.abs(d.float(x) - num)).toBeLessThan(1e-6 * Math.max(1, Math.abs(num)));
      }
    });
  }
  test("derivatives are simplified", () => {
    expect(fn("x^3 + 2x - 1/x").derivative().toString()).toBe("3*x^2 + 2 + 1/x^2");
    expect(fn("a*x^2", { params: { a: 3 } }).derivative().toString()).toBe("2*a*x");
    expect(fn("5").derivative().toString()).toBe("0");
  });
  test("d/dx of a certified model: derivative's model encloses the derivative", () => {
    const D = Domain(R`0:1`);
    const m = fn("exp(sin(x))*x").derivative().model(D);
    const at = m.at(R`1/2`);
    const ref = Math.exp(Math.sin(0.5)) * (Math.cos(0.5) * 0.5 + 1);
    expect(at.low.toNumber()).toBeLessThanOrEqual(ref + 1e-15);
    expect(at.high.toNumber()).toBeGreaterThanOrEqual(ref - 1e-15);
  });
});

describe("models from expressions", () => {
  test("parameters may be numbers, strings, Rationals or intervals", () => {
    const D = Domain(R`0:1`);
    const p = fn("a*x + b", { params: { a: "1/3", b: R`2` } }).model(D);
    expect(p.isExact).toBe(true);
    expect(p.at(R`1`).toString()).toBe("7/3:7/3");
    // a ∈ [1, 2] enters as 3/2 ± 1/2, so the enclosure is valid but not sharp
    const wide = fn("a*x", { params: { a: R`1:2` } }).model(D).range();
    expect(wide.low.toNumber()).toBeLessThanOrEqual(0);
    expect(wide.high.toNumber()).toBeGreaterThanOrEqual(2);
  });
  test("unbound names and non-smooth points are refused", () => {
    expect(() => fn("a*x")).toThrow(AnalyticError);
    expect(() => fn("abs(x)").model(Domain(R`-1:1`))).toThrow(AnalyticError);
    expect(fn("abs(x)").model(Domain(R`-2:-1`)).at(R`-3/2`).toString()).toBe("3/2:3/2");
    expect(() => fn("x^0").model(Domain(R`-1:1`))).toThrow(AnalyticError);
    expect(() => fn("log(x)").model(Domain(R`-1:1`))).toThrow(AnalyticError);
  });
  test("pi and e are certified constants", () => {
    const v = fn("pi + e + x").model(Domain(R`0:0`)).at(R`0`);
    expect(v.low.toNumber()).toBeLessThanOrEqual(Math.PI + Math.E + 1e-15);
    expect(v.high.toNumber()).toBeGreaterThanOrEqual(Math.PI + Math.E - 1e-15);
    expect(v.high.subtract(v.low).toNumber()).toBeLessThan(1e-25);
  });
});
