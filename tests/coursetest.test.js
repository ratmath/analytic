// Fixes found by the Course Test (ratmath/shelf#7).
import { describe, expect, test } from "bun:test";
import { readFileSync } from "node:fs";
import * as A from "../index.js";

describe("Course Test fixes", () => {
  test("starting values given exactly are read exactly", () => {
    const r = A.fixedPoint("cos(x)", "1/2").root;
    expect(r).not.toBe(null);
    expect(r.low.toNumber()).toBeCloseTo(0.7390851332151607, 12);
    expect(A.newton("x^2 - 2", "3/2").root.low.toNumber()).toBeCloseTo(Math.SQRT2, 12);
    expect(A.secant("x^2 - 2", "1", "3/2").root.low.toNumber()).toBeCloseTo(Math.SQRT2, 12);
    expect(A.bisection("x^2 - 2", ["1", "3/2"]).root.low.toNumber()).toBeCloseTo(Math.SQRT2, 12);
  });
  test("pointwise limits of x^n, including at x = 0 and x = 1", () => {
    const F = A.functionSequence("x^n");
    expect(F.pointwise("1/2").low.toNumber()).toBe(0);
    expect(F.pointwise("1").low.toNumber()).toBe(1);
    expect(F.pointwise("1").high.toNumber()).toBe(1);
    expect(F.pointwise("0").high.toNumber()).toBe(0);
    expect(F.pointwise("2")).toBe(Infinity);
    const G = A.functionSequence("n*x/(1 + n*x)");
    expect(G.pointwise("1/3").low.toNumber()).toBe(1);
  });
  test("sec, csc, cot and the inverse hyperbolic functions are read as functions", () => {
    expect(A.format(A.parse("sec(x)"))).toBe("1/cos(x)");
    expect(A.format(A.parse("cot(2x)"))).toBe("cos(2*x)/sin(2*x)");
    expect(A.format(A.parse("csc x"))).toBe("1/sin(x)");
    expect(A.format(A.parse("asinh(x)"))).toBe("log(x + sqrt(x^2 + 1))");
    expect(() => A.parse("foo(x)")).toThrow(/unknown function foo/);
    expect(A.format(A.parse("k(x + 1)"))).toBe("k*(x + 1)");
    expect(String(A.linearODE([1, 0, 1], "sec(x)").particular)).toBe("log(abs(cos(x)))*cos(x) + x*sin(x)");
  });
  test("a linear first-order equation whose integrating factor is 1/|x|", () => {
    const r = A.firstOrder("(x + y)/x");
    expect(r.type).toBe("linear");
    expect(String(r.general)).toBe("y = log(abs(x))*x + C*x");
    expect(String(A.firstOrder("-y/x + 1").general)).toBe("y = (1/2*x^2 + C)/x");
  });
  test("everything index.d.ts declares is exported", () => {
    const dts = readFileSync(new URL("../index.d.ts", import.meta.url), "utf8");
    const declared = [...dts.matchAll(/^export (?:declare )?(?:function|class|const) (\w+)/gm)].map((m) => m[1]);
    expect(declared.filter((name) => !(name in A))).toEqual([]);
  });
});
