// Helpers added for the Course Test roadmap, batch A6 (ratmath/shelf course-test/ROADMAP.md).
// Each is checked against an independent computation.
import { describe, expect, test } from "bun:test";
import { Rational } from "@ratmath/core";
import * as A from "../index.js";

const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));

describe("termsForError on alternating series", () => {
  test("Σ (-1)^(n+1)/n² to within 1/1000: 31 terms, and the partial sum is that close to π²/12", () => {
    const s = A.sum("(-1)^(n+1)/n^2", { from: 1 });
    const r = s.termsForError("1/1000");
    expect(r.terms).toBe(31);
    expect(r.last).toBe(31);
    // independent: the first n with 1/(n+1)² ≤ 1/1000 is n = 31 (32² = 1024)
    expect(1 / 32 ** 2 <= 1 / 1000 && 1 / 31 ** 2 > 1 / 1000).toBe(true);
    expect(r.bound.equals(Q(1, 1024))).toBe(true);
    let partial = Q(0);
    for (let n = 1; n <= 31; n++) partial = partial.add(Q(n % 2 ? 1 : -1, n * n));
    const err = Math.abs(partial.toNumber() - Math.PI ** 2 / 12);
    expect(err).toBeLessThan(1 / 1000);
    // one term fewer is not enough by the bound
    expect(1 / 31 ** 2).toBeGreaterThan(1 / 1000);
  });
  test("the alternating harmonic series needs n with 1/(n+1) ≤ ε", () => {
    const r = A.sum("(-1)^n/n", { from: 1 }).termsForError("1/100");
    expect(r.last).toBe(99);
    expect(r.terms).toBe(99);
  });
  test("a series that does not alternate is refused", () => {
    expect(() => A.sum("1/n^2", { from: 1 }).termsForError("1/100")).toThrow(/alternating/);
  });
});

describe("exact Newton", () => {
  test("x² − 2 from 1 gives the fractions 3/2, 17/12, 577/408, 665857/470832", () => {
    const r = A.newton("x^2 - 2", "1", { exact: true, steps: 4 });
    expect(r.iterations.map((row) => row.x.toString())).toEqual(["1", "3/2", "17/12", "577/408", "665857/470832"]);
    expect(r.exact).toBe(true);
    // independent: the recurrence x ← (x + 2/x)/2 by hand with bigints
    let [p, q] = [1n, 1n];
    for (let i = 0; i < 4; i++) [p, q] = [p * p + 2n * q * q, 2n * p * q];
    expect(r.estimate.equals(new Rational(p, q))).toBe(true);
    // the floats agree with the exact iterates to double precision
    r.iterations.forEach((row, i) => expect(r.floats[i]).toBeCloseTo(row.x.toNumber(), 14));
    expect(r.root.low.toNumber()).toBeCloseTo(Math.SQRT2, 14);
    expect(r.order).toBeGreaterThan(1.9);
  });
  test("an exact root stops the iteration", () => {
    const r = A.newton("x^2 - 4", "3", { exact: true, steps: 3 });
    expect(r.iterations.at(-1).x.toNumber()).toBeCloseTo(2, 3);
    const s = A.newton("2*x - 1", "5", { exact: true });
    expect(s.iterations.length).toBe(2);
    expect(s.estimate.equals(Q(1, 2))).toBe(true);
  });
  test("a function with sin is refused", () => {
    expect(() => A.newton("sin(x)", "3", { exact: true })).toThrow(/exact Newton/);
  });
});

describe("Darboux sums", () => {
  test("x² on [0, 1] with 4 pieces: 7/32 and 15/32, exactly", () => {
    const r = A.darboux("x^2", { interval: ["0", "1"], n: 4 });
    expect(r.exact).toBe(true);
    expect(r.lower.equals(Q(7, 32))).toBe(true);
    expect(r.upper.equals(Q(15, 32))).toBe(true);
    // independent: Σ (i/4)²/4 for i = 0..3 and 1..4
    let [lo, hi] = [Q(0), Q(0)];
    for (let i = 0; i < 4; i++) {
      lo = lo.add(Q(i * i, 64));
      hi = hi.add(Q((i + 1) * (i + 1), 64));
    }
    expect(r.lower.equals(lo) && r.upper.equals(hi)).toBe(true);
    expect(r.lower.lessThanOrEqual(r.integral.low) && r.integral.high.lessThanOrEqual(r.upper)).toBe(true);
  });
  test("a decreasing piece takes its inf at the right end", () => {
    const r = A.darboux("x^2", ["-1", "0", "1/2", "1"]);
    expect(r.pieces.map((p) => p.monotone)).toEqual(["decreasing", "increasing", "increasing"]);
    expect(r.lower.equals(Q(1, 8))).toBe(true);
    expect(r.upper.equals(Q(13, 8))).toBe(true);
  });
  test("sin on [0, 3]: an enclosure around the peak, lower ≤ integral ≤ upper", () => {
    const r = A.darboux("sin(x)", { interval: ["0", "3"], n: 3 });
    expect(r.exact).toBe(false);
    expect(r.pieces[1].monotone).toBe(null);
    // the middle piece [1, 2] has sup sin(π/2) = 1 and inf min(sin 1, sin 2) = sin 1
    expect(r.pieces[1].sup.low.toNumber()).toBeCloseTo(1, 12);
    expect(r.pieces[1].inf.low.toNumber()).toBeCloseTo(Math.sin(1), 12);
    const lower = Math.sin(0) + Math.sin(1) + Math.sin(3);
    const upper = Math.sin(1) + 1 + Math.sin(2);
    expect(r.lower.low.toNumber()).toBeCloseTo(lower, 12);
    expect(r.upper.high.toNumber()).toBeCloseTo(upper, 12);
    expect(r.lower.high.lessThanOrEqual(r.integral.low)).toBe(true);
    expect(r.integral.high.lessThanOrEqual(r.upper.low)).toBe(true);
  });
  test("bad partitions are refused", () => {
    expect(() => A.darboux("x", ["1", "0"])).toThrow(/increase/);
    expect(() => A.darboux("x", ["1"])).toThrow(/two points/);
  });
});

describe("classifying second-order PDEs", () => {
  test("the three model equations", () => {
    expect(A.classifyPDE({ A: "1", C: "-1" }).type).toBe("hyperbolic"); // wave
    expect(A.classifyPDE({ A: "1" }).type).toBe("parabolic"); // heat
    expect(A.classifyPDE({ A: "1", C: "1" }).type).toBe("elliptic"); // Laplace
    expect(A.pde.classify([1, 2, 1]).type).toBe("parabolic"); // B² = 4AC
  });
  test("Tricomi y·u_xx + u_yy changes type across y = 0", () => {
    const t = A.classifyPDE({ A: "y", C: "1" });
    expect(t.type).toBe(null);
    expect(t.discriminant).toBe("-4*y");
    expect(t.regions).toEqual({ hyperbolic: "y < 0", parabolic: "y = 0", elliptic: "y > 0" });
    expect(t.at("0", "-1")).toBe("hyperbolic");
    expect(t.at("5", "0")).toBe("parabolic");
    expect(t.at("0", "1/3")).toBe("elliptic");
    expect(t.on([["-1", "1"], ["1", "2"]])).toBe("elliptic");
    expect(t.on([["-1", "1"], ["-1", "1"]])).toBe(null);
  });
  test("a discriminant in both variables is given as a condition and checked at points", () => {
    const t = A.classifyPDE({ A: "x", B: "y", C: "1" });
    expect(t.regions.hyperbolic).toBe("y^2 - 4*x > 0");
    // independent: B² − 4AC at (1, 2) is 4 − 4 = 0, at (1, 3) is 5
    expect(t.at("1", "2")).toBe("parabolic");
    expect(t.at("1", "3")).toBe("hyperbolic");
    expect(t.at("1", "1")).toBe("elliptic");
    const e = A.classifyPDE({ A: "exp(x)", C: "1" });
    expect(e.at("0", "0")).toBe("elliptic");
  });
});
