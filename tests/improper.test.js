import { describe, test, expect } from "bun:test";
import { fn, AnalyticError } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 0) => num(iv.low) <= x + slack && num(iv.high) >= x - slack;
const width = (iv) => num(iv.high.subtract(iv.low));
const code = (f) => { try { f(); } catch (e) { return e instanceof AnalyticError ? e.code : `other: ${e.message}`; } return "no error"; };

describe("limits at infinity", () => {
  test("rational functions give the exact ratio of leading coefficients", () => {
    expect(fn("(2x^2+1)/(x^2-3)").limit("inf").toString()).toBe("2:2");
    expect(fn("(2x^2+1)/(x^2-3)").limit("-inf").toString()).toBe("2:2");
    expect(fn("(x+1)/(x^2+1)").limit(Infinity).toString()).toBe("0:0");
    expect(fn("x^3/(x^2+1)").limit("inf")).toBe(Infinity);
    expect(fn("x^3/(x^2+1)").limit("-inf")).toBe(-Infinity);
  });
  test("decay against oscillation and growth", () => {
    expect(fn("sin(x)/x").limit("inf").toString()).toBe("0:0");
    expect(fn("x*exp(-x)").limit("inf").toString()).toBe("0:0");
    expect(fn("log(x)/x").limit("inf").toString()).toBe("0:0");
    expect(fn("exp(x)/x^5").limit("inf")).toBe(Infinity);
    expect(fn("x^5*exp(-x^2)").limit("inf").toString()).toBe("0:0");
  });
  test("limits that are not rational", () => {
    expect(holds(fn("(1+1/x)^x").limit("inf"), Math.E, 1e-15)).toBe(true);
    expect(width(fn("(1+1/x)^x").limit("inf"))).toBeLessThan(1e-20);
    expect(holds(fn("atan(x)").limit("-inf"), -Math.PI / 2, 1e-15)).toBe(true);
    expect(fn("tanh(x)").limit("inf").toString()).toBe("1:1");
    expect(fn("x*sin(1/x)").limit("inf").toString()).toBe("1:1");
    expect(holds(fn("a*x/(x+1)", { params: { a: 3 } }).limit("inf"), 3)).toBe(true);
  });
  test("no limit is reported as such", () => {
    expect(code(() => fn("sin(x)").limit("inf"))).toBe("no-limit");
    expect(code(() => fn("x*sin(x)").limit("inf"))).toBe("no-limit");
    expect(code(() => fn("sqrt(x^2+x)-x").limit("inf"))).toBe("no-limit");
  });
  test("one-sided limits at a point", () => {
    expect(fn("1/x").limit(0, { side: "right" })).toBe(Infinity);
    expect(fn("1/x").limit(0, { side: "left" })).toBe(-Infinity);
    expect(code(() => fn("1/x").limit(0))).toBe("no-limit");
    expect(fn("1/x^2").limit(0)).toBe(Infinity);
    expect(fn("x*log(x)").limit(0, { side: "right" }).toString()).toBe("0:0");
    expect(fn("exp(-1/x)").limit(0, { side: "right" }).toString()).toBe("0:0");
    expect(holds(fn("(1+x)^(1/x)").limit(0, { side: "right" }), Math.E, 1e-15)).toBe(true);
    // the removable case still goes the old way
    expect(holds(fn("sin(x)/x").limit(0), 1, 1e-15)).toBe(true);
  });
  test("leading behaviour", () => {
    const a = fn("(3x^2+1)/(x-1)").asymptotic();
    expect(a.term).toBe("x");
    expect(a.coefficient.toString()).toBe("3:3");
    expect(fn("x^2*exp(-2x)").asymptotic().term).toBe("exp(-2*x)*x^2");
    expect(fn("sin(x)/x").asymptotic().oscillates).toBe(true);
  });
});

describe("improper integrals", () => {
  const exact = (r) => r.exactStage();
  test("power and exponential tails are closed forms", () => {
    const a = exact(fn("1/x^2").improperIntegral(1, "inf"));
    expect(holds(a.value, 1)).toBe(true);
    expect(width(a.value)).toBeLessThan(1e-10);
    expect(holds(exact(fn("exp(-x)").improperIntegral(0, Infinity)).value, 1)).toBe(true);
    expect(holds(exact(fn("x*exp(-x)").improperIntegral(0, "inf")).value, 1)).toBe(true);
    expect(holds(exact(fn("1/(x*log(x)^2)").improperIntegral(2, "inf")).value, 1 / Math.log(2), 1e-14)).toBe(true);
  });
  test("the p-test", () => {
    expect(exact(fn("1/x").improperIntegral(1, "inf")).value).toBe(Infinity);
    expect(holds(exact(fn("1/x^(101/100)").improperIntegral(1, "inf")).value, 100)).toBe(true);
    expect(exact(fn("1/sqrt(x)").improperIntegral(1, "inf")).value).toBe(Infinity);
    expect(exact(fn("-1/sqrt(x)").improperIntegral(1, "inf")).value).toBe(-Infinity);
  });
  test("the whole line", () => {
    const g = exact(fn("exp(-x^2)").improperIntegral("-inf", "inf")).value;
    expect(holds(g, Math.sqrt(Math.PI), 1e-15)).toBe(true);
    expect(width(g)).toBeLessThan(1e-9);
    const c = exact(fn("1/(1+x^2)").improperIntegral("-inf", "inf")).value;
    expect(holds(c, Math.PI, 1e-15)).toBe(true);
    expect(Number.isNaN(exact(fn("x").improperIntegral("-inf", "inf")).value)).toBe(true);
  });
  test("singular endpoints", () => {
    expect(holds(exact(fn("1/sqrt(x)").improperIntegral(0, 1)).value, 2)).toBe(true);
    expect(holds(exact(fn("log(x)").improperIntegral(0, 1)).value, -1)).toBe(true);
    expect(exact(fn("1/x").improperIntegral(0, 1)).value).toBe(Infinity);
    const a = exact(fn("1/sqrt(1-x^2)").improperIntegral(-1, 1)).value;
    expect(holds(a, Math.PI, 1e-15)).toBe(true);
    expect(width(a)).toBeLessThan(1e-9);
    expect(exact(fn("1/x^2").improperIntegral(-1, 1, { singular: [0] })).value).toBe(Infinity);
    expect(holds(exact(fn("1/cbrt(x)^2").improperIntegral(-1, 1, { singular: [0] })).value, 6, 1e-9)).toBe(true);
  });
  test("reversed ends change the sign", () => {
    expect(holds(exact(fn("exp(-x)").improperIntegral("inf", 0)).value, -1)).toBe(true);
  });
  test("oscillating tails: bounded ones converge, the rest is refused", () => {
    const s = exact(fn("sin(x)/x^2").improperIntegral(1, "inf", { digits: 2 }));
    expect(holds(s.value, 0.5040670619069)).toBe(true);
    expect(code(() => fn("sin(x)/x").improperIntegral(1, "inf").exact())).toBe("undecided");
  });
  test("a preview comes first", () => {
    const r = fn("exp(-x^2)").improperIntegral("-inf", "inf");
    expect(r.quick.value).toBeCloseTo(Math.sqrt(Math.PI), 6);
    expect(r.quick.trust).toBe("rough");
  });
});
