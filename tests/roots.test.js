import { describe, test, expect } from "bun:test";
import { R, Rational } from "@ratmath/core";
import { zeros, poles, extrema, inflections, simplestBetween, fn } from "../index.js";

const S = (r) => r.toString();
const num = (x) => x.toNumber();
const holds = (r, x, slack = 1e-15) => num(r.lo) <= x + slack && num(r.hi) >= x - slack;

describe("simplestBetween", () => {
  test("Stern–Brocot descent", () => {
    expect(S(simplestBetween(R`1/3`, R`1/2`))).toBe("1/2");
    expect(S(simplestBetween(R`0.3`, R`0.35`))).toBe("1/3");
    expect(S(simplestBetween(R`-2.45`, R`-2.1`))).toBe("-7/3");
    expect(S(simplestBetween(R`-1`, R`1`))).toBe("0");
  });
});

describe("rational functions: exact engine", () => {
  test("rational roots come out exactly, irrational ones as brackets", () => {
    const z = zeros("x^2 - 4", [-3, 3]).exact();
    expect(z.map((r) => [r.kind, S(r.at)])).toEqual([["exact", "-2"], ["exact", "2"]]);
    const w = zeros("x^2 - 2", [0, 2]).exact();
    expect(w.length).toBe(1);
    expect(w[0].kind).toBe("sign-change");
    expect(w[0].unique).toBe(true);
    expect(holds(w[0], Math.SQRT2)).toBe(true);
  });
  test("multiplicities from the square-free decomposition", () => {
    const z = zeros("(x-1)^2*(x+2)^3*(x^2-2)", [-3, 3]).exact();
    expect(z.map((r) => r.multiplicity)).toEqual([3, 1, 2, 1]);
    expect(S(z[0].at)).toBe("-2");
    expect(S(z[2].at)).toBe("1");
    expect(z.every((r) => r.unique)).toBe(true);
  });
  test("tolerance sets bracket width; parameters are exact", () => {
    const z = zeros("x^2 - a", [0, 2], { params: { a: "3" }, tolerance: "1e-12" }).exact();
    expect(num(z[0].hi) - num(z[0].lo)).toBeLessThan(1e-12);
    expect(holds(z[0], Math.sqrt(3))).toBe(true);
  });
  test("poles with order, holes with their limit, and holes are not zeros", () => {
    const f = "(x^2-1)/((x-1)*x^2)";
    const p = poles(f, [-3, 3]).exact();
    expect(p.map((r) => [r.kind, S(r.at)])).toEqual([["pole", "0"], ["hole", "1"]]);
    expect(p[0].order).toBe(2);
    expect(S(p[1].value)).toBe("2:2");
    expect(zeros(f, [-3, 3]).exact().map((r) => S(r.at))).toEqual(["-1"]);
  });
  test("extrema and inflections", () => {
    const e = extrema("x^3 - 3x", [-3, 3]).exact();
    expect(e.map((r) => [r.kind, S(r.at), S(r.value)])).toEqual([["max", "-1", "2:2"], ["min", "1", "-2:-2"]]);
    expect(extrema("x^4", [-1, 1]).exact().map((r) => r.kind)).toEqual(["min"]);
    expect(extrema("x^3", [-1, 1]).exact().map((r) => r.kind)).toEqual(["flat"]);
    const i = inflections("x^3 - 3x", [-3, 3]).exact();
    expect(i.map((r) => S(r.at))).toEqual(["0"]);
    expect(inflections("x^4", [-1, 1]).exact()).toEqual([]);
  });
});

describe("general functions: Krawczyk engine", () => {
  test("simple zeros are proven unique and narrowed", () => {
    const z = zeros("cos(x) - x", [0, 1]).exact();
    expect(z.length).toBe(1);
    expect(z[0]).toMatchObject({ kind: "sign-change", unique: true });
    expect(holds(z[0], 0.7390851332151607)).toBe(true);
    expect(num(z[0].hi) - num(z[0].lo)).toBeLessThan(1e-6);
  });
  test("sin on [-1, 7]: 0 exactly, π and 2π in brackets", () => {
    const z = zeros("sin(x)", [-1, 7]).exact();
    expect(z.map((r) => r.kind)).toEqual(["exact", "sign-change", "sign-change"]);
    expect(S(z[0].at)).toBe("0");
    expect(z[0].multiplicity).toBe(1);
    expect(holds(z[1], Math.PI)).toBe(true);
    expect(holds(z[2], 2 * Math.PI)).toBe(true);
  });
  test("a double root: sin(x)^2 is searched as sin(x), so π is proven too", () => {
    const z = zeros("sin(x)^2", [-1, 4]).exact();
    expect(z[0]).toMatchObject({ kind: "exact", multiplicity: 2 });
    expect(z[1]).toMatchObject({ kind: "isolated", unique: true });
    expect(holds(z[1], Math.PI)).toBe(true);
    expect(z.length).toBe(2);
  });
  test("a double root without a visible square stays 'at most 2'", () => {
    const z = zeros("1 - cos(x)", [1, 8]).exact();
    expect(z.length).toBe(1);
    expect(z[0]).toMatchObject({ kind: "possible", atMost: 2 });
    expect(holds(z[0], 2 * Math.PI)).toBe(true);
  });
  test("domain gaps are reported, not searched forever", () => {
    const z = zeros("log(x)", [-1, 3]).exact();
    expect(z[0].kind).toBe("undefined");
    expect(z.at(-1)).toMatchObject({ kind: "exact" });
    expect(S(z.at(-1).at)).toBe("1");
  });
  test("extrema and inflections of sin", () => {
    const e = extrema("sin(x)", [0, 7]).exact();
    expect(e.map((r) => r.kind)).toEqual(["max", "min"]);
    expect(holds(e[0], Math.PI / 2)).toBe(true);
    expect(e[1].value.low.toNumber()).toBe(-1);
    const i = inflections("sin(x)", [-1, 7]).exact();
    expect(i.map((r) => r.kind)).toEqual(["inflection", "inflection", "inflection"]);
  });
  test("poles from denominators, tan included", () => {
    const p = poles("tan(x)", [0, 4]).exact();
    expect(p.length).toBe(1);
    expect(holds(p[0], Math.PI / 2)).toBe(true);
    const q = poles("1/sin(x) + x", [1, 7]).exact();
    expect(q.map((r) => r.kind)).toEqual(["pole", "pole"]);
  });
  test("float guesses come first", () => {
    const r = zeros("cos(x) - x", [0, 1]);
    expect(r.quick.trust).toBe("rough");
    expect(Math.abs(r.quick.value[0].at - 0.7390851332151607)).toBeLessThan(1e-12);
    const e = extrema("x^3 - 3x", [-3, 3]).quick.value.map((g) => Math.round(g.at));
    expect(e).toEqual([-1, 1]);
  });

  test("flat functions: e^(-1/x²) near 0 is 'possible' with a size bound, never a proven zero", () => {
    const z = zeros("exp(-1/x^2)", [-1, 1]).exact();
    expect(z.map((r) => r.kind)).toEqual(["possible", "undefined", "possible"]);
    expect(z.every((r) => r.kind !== "exact" && r.kind !== "sign-change")).toBe(true);
    expect(z[0].bound.toNumber()).toBeLessThan(1e-90);
    expect(z[0].atMost).toBeUndefined(); // every derivative is flat there too
    expect(z[0].lo.toNumber()).toBeGreaterThan(-0.1); // away from 0 it is proven positive
    const shifted = zeros("exp(-1/x^2) - 1/1000000", ["1/1000", 1]).exact();
    expect(shifted.length).toBe(1);
    expect(holds(shifted[0], 1 / Math.sqrt(Math.log(1e6)))).toBe(true);
  });
  test("a division inside exp is not a pole of f", () => {
    expect(poles("exp(-1/x^2)", [-1, 1]).exact().map((r) => r.kind)).toEqual(["undefined"]);
    expect(poles("exp(1/x)", [-1, 1]).exact().map((r) => r.kind)).toEqual(["undefined"]);
    expect(poles("x/(x-1) + exp(x)", [-1, 2]).exact().map((r) => r.kind)).toEqual(["pole"]);
    expect(poles("2*tan(x)^2", [0, 2]).exact().map((r) => r.kind)).toEqual(["pole"]);
  });
});

describe("holes in rational summands", () => {
  const f = "(x^2 - 1)/(x - 1) + sin(2x)/2";
  test("inflections near a hole settle: 11 at kπ/2 on [-8, 8]", () => {
    const list = inflections(f, R`-8:8`, { tolerance: "1/10000" }).exact();
    expect(list.length).toBe(11);
    for (const [i, r] of list.entries()) {
      expect(r.kind).toBe("inflection");
      const k = i - 5;
      const c = (r.lo.toNumber() + r.hi.toNumber()) / 2;
      expect(Math.abs(c - (k * Math.PI) / 2)).toBeLessThan(1e-4);
    }
  });
  test("the hole is reported with its limit", () => {
    const list = poles(f, R`-2:2`).exact();
    expect(list.map((r) => r.kind)).toEqual(["hole"]);
    expect(list[0].at.toString()).toBe("1");
    const lim = 2 + Math.sin(2) / 2;
    expect(list[0].value.low.toNumber()).toBeLessThanOrEqual(lim);
    expect(list[0].value.high.toNumber()).toBeGreaterThanOrEqual(lim);
  });
  test("integral across the hole", () => {
    const iv = fn(f).integral(0, 2, { digits: 10 }).exact();
    const ref = 4 + (1 - Math.cos(4)) / 4; // ∫0^2 (x + 1) + sin(2x)/2
    expect(iv.low.toNumber()).toBeLessThanOrEqual(ref + 1e-12);
    expect(iv.high.toNumber()).toBeGreaterThanOrEqual(ref - 1e-12);
  });
  test("the value at the hole is still refused", () => {
    expect(() => fn(f).value(1).exact()).toThrow();
  });
});

describe("work budget", () => {
  test("a capped search reports possible brackets and says so", () => {
    const job = extrema("sin(x)/x", R`-1:1`, { maxBoxes: 20 });
    const list = job.exact();
    expect(list.some((r) => r.kind === "possible")).toBe(true);
    expect(job.exactStage().via).toContain("budget");
  });
});

describe("graphics' feature cases", () => {
  const near = (r, x) => (r.at ? Math.abs(r.at.toNumber() - x) : Math.abs((r.lo.toNumber() + r.hi.toNumber()) / 2 - x)) < 1e-3;
  test("sin(x)/x: a certified hole at 0 with limit 1, no extrema, two inflections", () => {
    const I = R`-4:4`;
    const p = poles("sin(x)/x", I).exact();
    expect(p.map((r) => r.kind)).toEqual(["hole"]);
    expect(p[0].at.toString()).toBe("0");
    expect(p[0].value.low.toString()).toBe("1");
    expect(p[0].value.high.toString()).toBe("1");
    expect(extrema("sin(x)/x", I, { tolerance: "1/10000" }).exact()).toEqual([]);
    const inf = inflections("sin(x)/x", I, { tolerance: "1/10000" }).exact();
    expect(inf.map((r) => r.kind)).toEqual(["inflection", "inflection"]);
    expect(near(inf[1], 2.0815759778)).toBe(true);
    const z = zeros("sin(x)/x", I).exact();
    expect(z.map((r) => r.kind)).toEqual(["sign-change", "sign-change"]);
  });
  test("scaled and shifted quotients: holes found through products and sums", () => {
    for (const [f, lim] of [["sin(x)/x * 4", "4"], ["4*sin(x)/x", "4"], ["sin(x)/x + x", "1"]]) {
      const p = poles(f, [-8, 8]).exact();
      expect(p.map((r) => `${r.kind} ${r.at} ${r.value.low}`)).toEqual([`hole 0 ${lim}`]);
    }
    const e = extrema("sin(x)/x * 4", [-8, 8], { tolerance: "1/10000" }).exact();
    expect(e.map((r) => r.kind)).toEqual(["max", "min", "min", "max"]);
  });
  test("flat touches of f′ are marked", () => {
    const e = extrema("(x^2 - 1)/(x - 1) + sin(2x)/2", [-2, 2], { tolerance: "1/10000" }).exact();
    expect(e).toHaveLength(2);
    for (const r of e) expect(r).toMatchObject({ kind: "possible", touching: true });
  });
  test("ln(x): a vertical asymptote at 0", () => {
    const p = poles("ln(x)", [-1, 1]).exact();
    expect(p).toHaveLength(1);
    expect(p[0]).toMatchObject({ kind: "pole", source: "log" });
    expect(p[0].at.toString()).toBe("0");
    expect(poles("x*ln(x)", [-1, 1]).exact()).toEqual([]); // x·ln x → 0
  });
  test("sqrt(9 - x^2): exact zeros ±3 and nothing else", () => {
    const z = zeros("sqrt(9 - x^2)", [-4, 4]).exact();
    expect(z.map((r) => `${r.kind} ${r.at}`)).toEqual(["exact -3", "exact 3"]);
  });
});
