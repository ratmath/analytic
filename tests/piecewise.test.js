import { describe, test, expect } from "bun:test";
import { R } from "@ratmath/core";
import { fn, where, piecewise, Region, zeros, extrema, AnalyticError } from "../index.js";

const S = (x) => (x === null ? null : x.toString());

describe("regions", () => {
  test("chains with strict ends and open sides", () => {
    const r = where`2:!x:8`;
    expect([2, 3, 8, 9].map((x) => r.test(x))).toEqual([false, true, true, false]);
    expect(new Region(":x:8").test(-1000)).toBe(true);
    expect(new Region(":x:!8").test(8)).toBe(false);
    expect(new Region("2:x:").test("2")).toBe(true);
    expect(new Region("all").test(5)).toBe(true);
    expect(new Region(":x:!-1 | 1:!x:").test(0)).toBe(false);
  });
  test("integer variables: 2n :x:! 2n+1 and 2n+1 :x:! 2n+2", () => {
    const even = new Region("2n :x:! 2n+1");
    const odd = new Region("2n+1 :x:! 2n+2");
    const xs = ["-2", "-3/2", "-1", "-1/2", "0", "1/2", "1", "3/2", "2"];
    expect(xs.map((x) => even.test(x))).toEqual([true, true, false, false, true, true, false, false, true]);
    expect(xs.map((x) => odd.test(x))).toEqual(xs.map((x) => !even.test(x)));
    expect(even.match("5/2").n).toBe(1);
    expect(even.breakpoints(0, 3).map(S)).toEqual(["0", "1", "2", "3"]);
  });
  test("parameters in bounds, function regions, bad bounds", () => {
    expect(new Region("a:x:b", { params: { a: 1, b: "5/2" } }).test("5/2")).toBe(true);
    expect(new Region((x) => x.numerator % 2n === 0n).test(R`4`)).toBe(true);
    expect(() => new Region("n^2:x:n^2+1")).toThrow(AnalyticError);
    expect(() => new Region("pi:x:4")).toThrow(AnalyticError);
    expect(() => new Region("1:y:2")).toThrow(AnalyticError);
  });
});

describe("piecewise functions", () => {
  const abs = fn("-x if :x:!0; x if 0:x:");
  test("text and pair forms agree", () => {
    const p = piecewise([[":x:!0", "-x"], ["0:x:", "x"]]);
    for (const x of [-2.5, 0, 1.75]) expect(p.float(x)).toBe(abs.float(x));
    expect(abs.toString()).toBe("-x if :x:!0; x if 0:x:");
  });
  test("first match wins; gaps are undefined", () => {
    const f = fn("1 if 0:x:2; 2 if 1:x:3");
    expect(f.float(1.5)).toBe(1);
    expect(f.float(2.5)).toBe(2);
    expect(Number.isNaN(f.float(5))).toBe(true);
    expect(() => f.value(5).exact()).toThrow(AnalyticError);
  });
  test("value, range and integral are certified across pieces", () => {
    expect(S(abs.value("-3/2").exact())).toBe("3/2:3/2");
    expect(S(abs.integral(-1, 2).exact())).toBe("5/2:5/2");
    expect(S(abs.range(R`-1:2`).exact())).toBe("0:2");
    const saw = fn("x - n if n:x:!n+1");
    expect(S(saw.integral(0, 3).exact())).toBe("3/2:3/2");
    expect(saw.float(1.25)).toBe(0.25);
  });
  test("alternating pieces with an integer variable", () => {
    const sq = fn("1 if 2n:x:!2n+1; -1 if 2n+1:x:!2n+2");
    expect([0.5, 1.5, 2, 2.5, -0.5].map((x) => sq.float(x))).toEqual([1, -1, 1, 1, -1]);
    expect(S(sq.integral(0, "5/2").exact())).toBe("1/2:1/2");
  });
  test("breaks: jumps, continuity, closed side", () => {
    const f = fn("x^2 if :x:1; 3 - x if 1:!x:2; 5 otherwise");
    const b = f.breaks([-1, 4]).exact();
    expect(b.map((r) => [S(r.at), r.kind, S(r.value), S(r.left), S(r.right)])).toEqual([
      ["1", "jump", "1:1", "1:1", "2:2"],
      ["2", "jump", "1:1", "1:1", "5:5"],
    ]);
    const c = fn("x^2 if :x:1; 2x - 1 if 1:!x:").breaks([0, 2]).exact();
    expect(c[0].kind).toBe("continuous");
    const hole = fn("x if :x:!1; x if 1:!x:").breaks([0, 2]).exact();
    expect(hole[0]).toMatchObject({ kind: "removable", defined: false });
  });
  test("zeros and extrema piece by piece", () => {
    const z = zeros("x^2 - 2 if :x:0; x - 1 if 0:!x:", [-3, 3]).exact();
    expect(z.map((r) => [r.kind, r.piece])).toEqual([["sign-change", 0], ["exact", 1]]);
    expect(z[0].lo.toNumber()).toBeCloseTo(-Math.SQRT2, 5);
    const saw = fn("x - n if n:x:!n+1").zeros([-2, 2]).exact();
    expect(saw.map((r) => S(r.at))).toEqual(["-2", "-1", "0", "1", "2"]);
    const e = extrema("x^3 - 3x if :x:0; x if 0:!x:", [-3, 3]).exact();
    expect(e.map((r) => [r.kind, S(r.at)])).toEqual([["max", "-1"]]);
  });
  test("derivative is taken rule by rule", () => {
    const d = fn("x^2 if :x:1; 3x otherwise").derivative();
    expect(d.float(0.5)).toBe(1);
    expect(d.float(2)).toBe(3);
  });
});
