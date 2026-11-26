import { describe, test, expect } from "bun:test";
import { Rational } from "@ratmath/core";
import { exactOf, nearestDouble, floatParts, floatOp, roundoff, bisection, newton, secant, fixedPoint, interpolate, equallySpaced, chebyshevNodes, spline, leastSquares, differences, richardson, quadratureRule, romberg, gaussLegendre, gaussRule, odeMethod, stepSizeStudy, stability } from "../index.js";
import { newton as newtonFromSubpath } from "@ratmath/analytic/methods";

const num = (x) => x.toNumber();

describe("floating point as exact rationals", () => {
  test("the value of a double and the error of an operation", () => {
    expect(exactOf(0.5).toString()).toBe("1/2");
    expect(exactOf(0.1).toString()).toBe("3602879701896397/36028797018963968");
    expect(exactOf(5e-324).equals(new Rational(1n, 1n << 1074n))).toBe(true);
    expect(nearestDouble(new Rational(1n, 3n))).toBe(1 / 3);
    const p = floatParts(0.1, "0.1");
    expect(p.exponent).toBe(-4);
    expect(p.error.toString()).toBe("1/180143985094819840");
    expect(p.bits.split(" ").map((s) => s.length)).toEqual([1, 11, 52]);
    const s = floatOp("+", 0.1, 0.2);
    expect(s.result).toBe(0.30000000000000004);
    expect(s.exactlyRepresentable).toBe(false);
    expect(num(s.error)).toBeCloseTo(2.7755575615628914e-17, 30);
    expect(floatOp("*", 0.5, 3).exactlyRepresentable).toBe(true);
    expect(() => exactOf(Infinity)).toThrow();
  });
  test("roundoff finds the operation that loses the digits", () => {
    const bad = roundoff("(1 - cos(x))/x^2", { x: 1e-8 });
    expect(bad.float).toBe(0);
    expect(bad.digitsLost).toBeGreaterThan(15);
    expect(bad.steps.find((s) => s.expression === "1 - cos(x)").relativeError).toBe(1);
    const good = roundoff("2*sin(x/2)^2/x^2", { x: 1e-8 });
    expect(good.relativeError).toBeLessThan(1e-15);
    expect(num(good.exact.low)).toBeCloseTo(0.5, 12);
  });
});

describe("root finding with true errors", () => {
  test("bisection halves, Newton squares, secant in between", () => {
    const b = bisection("x^2 - 2", [1, 2], { steps: 10 });
    expect(b.iterations.every((r) => r.error <= r.bound)).toBe(true);
    expect(num(b.root.low)).toBeCloseTo(Math.SQRT2, 14);
    const n = newton("x^2 - 2", 1);
    expect(n.order).toBeCloseTo(2, 2);
    expect(n.iterations.at(-1).error).toBeLessThan(1e-15);
    expect(n.derivative).toBe("2*x");
    expect(newtonFromSubpath).toBe(newton);
    const s = secant("x^3 - x - 1", 1, 2);
    expect(s.order).toBeGreaterThan(1.4);
    expect(s.order).toBeLessThan(1.8);
    expect(() => bisection("x^2 + 1", [0, 1])).toThrow();
  });
  test("fixed-point iteration converges at the rate of the multiplier", () => {
    const f = fixedPoint("cos(x)", 1, { steps: 30 });
    expect(num(f.root.low)).toBeCloseTo(0.7390851332151607, 14);
    expect(Math.abs(f.ratio)).toBeCloseTo(Math.abs(num(f.multiplier.low)), 2);
    expect(f.order).toBeCloseTo(1, 1);
  });
});

describe("interpolation", () => {
  test("exact divided differences, Newton and Lagrange forms", () => {
    const p = interpolate([[0, 1], [1, 3], [2, 2]]);
    expect(p.polynomial).toBe("-3/2*x^2 + 7/2*x + 1");
    expect(p.newton).toBe("1 + 2*x - 3/2*x*(x - 1)");
    expect(p.dividedDifferences.map((r) => r.map(String))).toEqual([["1", "3", "2"], ["2", "-1"], ["-3/2"]]);
    expect(p.at("1/2").toString()).toBe("19/8");
    expect(() => interpolate([[0, 1], [0, 2]])).toThrow();
  });
  test("the error formula against the true error; Runge's example", () => {
    const s = interpolate("sin(x)", { nodes: equallySpaced(0, 1, 4) }).maxError([0, 1]);
    expect(num(s.attained)).toBeLessThanOrEqual(num(s.value));
    expect(num(s.value)).toBeLessThan(num(s.textbook));
    const runge = interpolate("1/(1 + 25*x^2)", { nodes: equallySpaced(-1, 1, 9) }).maxError([-1, 1]);
    const cheb = interpolate("1/(1 + 25*x^2)", { nodes: chebyshevNodes(-1, 1, 9) }).maxError([-1, 1], { tolerance: 0.05 });
    expect(num(runge.attained)).toBeGreaterThan(1);
    expect(num(cheb.value)).toBeLessThan(0.2);
  });
  test("splines and least squares are exact", () => {
    const s = spline([[0, 0], [1, 1], [2, 0], [3, 1]]);
    expect(s.pieces[0].polynomial).toBe("-2/3*x^3 + 5/3*x");
    expect(s.moments.map(String)).toEqual(["0", "-4", "4", "0"]);
    expect(s.at("3/2").toString()).toBe("1/2");
    const l = leastSquares([[0, 1], [1, 2], [2, 2], [3, 4]], 1);
    expect(l.polynomial).toBe("9/10*x + 9/10");
    expect(l.residual.toString()).toBe("7/10");
  });
});

describe("differences and quadrature", () => {
  test("the error of a difference quotient falls, then rises", () => {
    const d = differences("exp(x)", 1, { kind: "central" });
    expect(d.best.h).toBeLessThan(1e-3);
    expect(d.best.h).toBeGreaterThan(1e-9);
    expect(d.rows[0].error / d.rows[0].truncation).toBeCloseTo(1, 2);
    expect(d.rows.at(-1).error).toBeGreaterThan(d.best.error * 1000);
    expect(richardson("exp(x)", 1).errors.at(-1).at(-1)).toBeLessThan(1e-12);
  });
  test("rules, their true errors and their textbook bounds", () => {
    const t = quadratureRule("exp(x)", [0, 1], { rule: "trapezoid", n: 4 });
    expect(num(t.error.low)).toBeCloseTo(0.0089400761, 9);
    expect(num(t.error.high)).toBeLessThan(num(t.bound));
    const s = quadratureRule("exp(x)", [0, 1], { rule: "simpson", n: 4 });
    expect(num(s.error.high)).toBeLessThan(num(s.bound));
    expect(num(quadratureRule("x^3", [0, 1], { rule: "simpson", n: 1 }).error.high)).toBe(0);
    const r = romberg("exp(x)", [0, 1], { levels: 4 });
    expect(r.errors[3][3]).toBeLessThan(1e-9);
    const g = gaussLegendre(3);
    expect(g.polynomial).toBe("5/2*x^3 - 3/2*x");
    expect(num(g.nodes[2].low)).toBeCloseTo(Math.sqrt(0.6), 14);
    expect(num(g.weights[1].low)).toBeCloseTo(8 / 9, 14);
    expect(Math.abs(num(gaussRule("x^5 + x^4", [0, 1], 3).error.high))).toBeLessThan(1e-20);
  });
});

describe("methods for differential equations", () => {
  test("global error against the validated solution; observed orders", () => {
    const r = odeMethod("y - t^2 + 1", { y0: "1/2", until: 2, steps: 4, method: "rk4" });
    expect(r.steps.length).toBe(5);
    expect(r.finalError).toBeCloseTo(0.0038667, 5);
    const e = stepSizeStudy("y - t^2 + 1", { y0: "1/2", until: 2, method: "euler", counts: [20, 40, 80] });
    expect(e.rows.at(-1).observedOrder).toBeGreaterThan(0.9);
    expect(e.rows.at(-1).observedOrder).toBeLessThan(1.1);
    const k = stepSizeStudy("y - t^2 + 1", { y0: "1/2", until: 2, method: "rk4", counts: [10, 20, 40] });
    expect(k.rows.at(-1).observedOrder).toBeGreaterThan(3.8);
    expect(() => odeMethod("y", { y0: 1, until: 1, method: "leapfrog" })).toThrow();
  });
  test("stability intervals", () => {
    expect(num(stability("rk4").interval[0].low)).toBeCloseTo(-2.785293563405282, 12);
    expect(stability("euler").largestStep(-100).low.toString()).toBe("1/50");
  });
});
