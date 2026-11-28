import { describe, test, expect } from "bun:test";
import { Rational } from "@ratmath/core";
import { sequence, recursive, sum, powerSeries, taylorRemainder, functionSequence, AnalyticError } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 0) => num(iv.low) <= x + slack && num(iv.high) >= x - slack;
const width = (iv) => num(iv.high.subtract(iv.low));

describe("sequences", () => {
  test("terms are exact where the formula is rational", () => {
    expect(sequence("(1 + 1/n)^n").terms(3).map(String)).toEqual(["2", "9/4", "64/27"]);
    expect(String(sequence("n!/2^n").term(5))).toBe("15/4");
  });
  test("limits", () => {
    expect(holds(sequence("(1 + 1/n)^n").limit(), Math.E, 1e-15)).toBe(true);
    expect(sequence("n^2/(n + 1)").limit()).toBe(Infinity);
    const zero = sequence("2^n/n!").limit();
    expect(zero.low.equals(zero.high) && zero.low.numerator === 0n).toBe(true);
    expect(() => sequence("sin(n)").limit()).toThrow(AnalyticError);
  });
  test("monotone from a proven index, and bounds for every term", () => {
    expect(sequence("n/(n^2 + 10)").monotone()).toEqual({ direction: "decreasing", from: 3, proven: "for every n ≥ 3" });
    expect(sequence("(n + 1)/n").monotone().direction).toBe("decreasing");
    const b = sequence("n/(n^2 + 10)").bounds();
    expect(b.bounded).toBe(true);
    expect(num(b.lower)).toBeGreaterThanOrEqual(0);
    expect(num(b.upper)).toBeGreaterThanOrEqual(3 / 19);
    expect(sequence("n^2").bounds().upper).toBe(null);
  });
});

describe("recursive sequences", () => {
  const heron = recursive("x/2 + 1/x", { start: 2 });
  test("exact terms", () => {
    expect(heron.terms(5).map(String)).toEqual(["2", "3/2", "17/12", "577/408", "665857/470832"]);
  });
  test("fixed points and their kind", () => {
    const [p] = heron.fixedPoints([1, 2]);
    expect(p.kind).toBe("attracting");
    expect(holds(p.point, Math.SQRT2)).toBe(true);
    const logistic = recursive("3.2*x*(1 - x)", { start: "1/2" }).fixedPoints([0, 1]);
    expect(logistic.map((q) => q.kind)).toEqual(["repelling", "repelling"]);
  });
  test("the limit is proven by contraction", () => {
    const r = heron.limit([1, 2]);
    expect(holds(r.limit, Math.SQRT2)).toBe(true);
    expect(num(r.rate)).toBeLessThan(1);
    expect(holds(recursive("cos(x)", { start: 1 }).limit([0, 1]).limit, 0.7390851332151607)).toBe(true);
    expect(() => recursive("3.2*x*(1 - x)", { start: "1/2" }).limit([0, 1])).toThrow(AnalyticError);
  });
});

describe("series: the tests", () => {
  const C = (s, from = 1) => sum(s, { from }).convergence();
  test("p-series by comparison and by the integral test", () => {
    expect(C("1/n^2").convergence).toBe("absolutely convergent");
    expect(C("1/n").convergence).toBe("divergent");
    expect(C("1/sqrt(n)").convergence).toBe("divergent");
    expect(C("1/(n*log(n))", 2).convergence).toBe("divergent");
    expect(C("1/(n*log(n)^2)", 2).convergence).toBe("absolutely convergent");
    const t = sum("1/n^2").comparisonTest();
    expect(t.like).toBe("n^-2");
    expect(String(t.exponent)).toBe("-2");
    expect(sum("1/n^2").integralTest().verdict).toBe("convergent");
    expect(sum("1/n").integralTest().verdict).toBe("divergent");
  });
  test("ratio and root tests with powers and factorials", () => {
    const r = sum("n/2^n").ratioTest();
    expect(r.verdict).toBe("convergent");
    expect(String(r.limit.low)).toBe("1/2");
    expect(sum("n/2^n").rootTest().verdict).toBe("convergent");
    expect(sum("2^n/n!").ratioTest().verdict).toBe("convergent");
    expect(String(sum("(2n)!/(n!)^2/5^n").ratioTest().limit.low)).toBe("4/5");
    expect(C("3^n/n^3").convergence).toBe("divergent");
    expect(sum("1/n^2").ratioTest().verdict).toBe("inconclusive");
  });
  test("alternating series, conditional convergence, the nth-term test", () => {
    const c = C("(-1)^n/n");
    expect(c.convergence).toBe("conditionally convergent");
    expect(c.by).toBe("alternating");
    expect(C("(-1)^(n+1)/n^2").convergence).toBe("absolutely convergent");
    const d = C("(-1)^n*n/(n + 1)");
    expect(d.convergence).toBe("divergent");
    expect(d.by).toBe("nth term");
    expect(sum("1/n").divergenceTest().verdict).toBe("inconclusive");
  });
});

describe("series: sums with a proven tail", () => {
  test("known sums lie in their enclosures", () => {
    const cases = [
      ["1/n^2", 1, Math.PI ** 2 / 6],
      ["n/2^n", 1, 2],
      ["2^n/n!", 1, Math.E ** 2 - 1],
      ["(-1)^n/n", 1, -Math.LN2],
      ["(-1)^(n+1)/n^2", 1, Math.PI ** 2 / 12],
      ["(2n)!/(n!)^2/5^n", 1, Math.sqrt(5) - 1],
      ["1/(n^2 + 1)", 1, (Math.PI / Math.tanh(Math.PI) - 1) / 2],
    ];
    for (const [s, from, value] of cases) {
      const r = sum(s, { from }).sum();
      expect(holds(r.enclosure, value, 1e-14)).toBe(true);
      expect(r.met).toBe(true);
      expect(width(r.enclosure)).toBeLessThan(1e-8);
      expect(typeof r.by).toBe("string");
    }
  });
  test("partial sums are exact", () => {
    expect(String(sum("1/n^2").partial(3))).toBe("49/36");
    expect(sum("1/n^2").partial(3)).toBeInstanceOf(Rational);
  });
  test("a divergent series has no sum", () => {
    expect(() => sum("1/n").sum()).toThrow(/diverges/);
  });
});

describe("power series", () => {
  test("radius and interval of convergence, ends examined", () => {
    const log = powerSeries("1/n", { from: 1 }).interval();
    expect(log.text).toBe("[-1, 1)");
    expect(log.left.convergence).toBe("conditionally convergent");
    expect(log.right.convergence).toBe("divergent");
    expect(powerSeries("1/n!").interval().text).toBe("(-inf, inf)");
    expect(powerSeries("n!").interval().text).toBe("{0}");
    expect(powerSeries("2^n/n^2", { from: 1 }).interval().text).toBe("[-1/2, 1/2]");
    expect(powerSeries("1", { centre: 3 }).interval().text).toBe("(2, 4)");
  });
  test("values, partial sums, term by term derivative", () => {
    const e = powerSeries("1/n!");
    expect(holds(e.value(1, { digits: 15 }).enclosure, Math.E, 1e-15)).toBe(true);
    expect(String(e.partial(3))).toBe("1 + x + 1/2*x^2 + 1/6*x^3");
    const geometric = powerSeries("1/n", { from: 1 }).derivative();
    expect(String(geometric.coefficient(7))).toBe("1");
    expect(geometric.interval().text).toBe("(-1, 1)");
  });
  test("Taylor's remainder against the true error", () => {
    const r = taylorRemainder("exp(x)", { about: 0, order: 4, on: [-1, 1] });
    expect(r.holds).toBe(true);
    expect(num(r.bound)).toBeCloseTo(Math.E / 120, 6);
    expect(holds(r.actual, Math.E - (1 + 1 + 1 / 2 + 1 / 6 + 1 / 24), 1e-9)).toBe(true);
  });
});

describe("sequences of functions", () => {
  const f = functionSequence("x^n");
  test("pointwise limits and the distance to the limit", () => {
    const p = f.pointwise("1/2");
    expect(num(p.low)).toBe(0);
    expect(holds(f.supDistance(5, [0, "9/10"]), 0.9 ** 5, 1e-9)).toBe(true);
  });
  test("uniform only with a proof", () => {
    expect(f.uniform(["1/10", "9/10"]).verdict).toBe("uniform");
    const whole = f.uniform([0, 1]);
    expect(whole.verdict).toBe("not uniform"); // now with a proof: the sup is at x = 1, where the distance tends to 1
    expect(whole.table.every((r) => num(r.sup.low) === 1)).toBe(true);
    expect(functionSequence("sin(n*x)/n").uniform([0, 1]).verdict).toBe("uniform");
  });
});
