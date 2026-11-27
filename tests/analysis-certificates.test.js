// Course Test roadmap, Fable items B2 to B5 (ratmath/shelf course-test/ROADMAP.md):
// certified limits of power forms, N for ε, δ for ε, suprema, limsup/liminf,
// uniform convergence. Each result is checked against a value known by hand.
import { describe, expect, test } from "bun:test";
import { Rational } from "@ratmath/core";
import * as A from "../index.js";

const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const mid = (iv) => (typeof iv === "number" ? iv : iv.low.add(iv.high).divide(Q(2)).toNumber());
const width = (iv) => iv.high.subtract(iv.low).toNumber();

describe("B2: limits of f(n)^g(n)", () => {
  const cases = [
    ["(1 + 1/n)^n", Math.E],
    ["(n/(n + 1))^n", 1 / Math.E],
    ["(1 - 1/n^2)^n", 1],
    ["((n + 1)/(n - 1))^n", Math.E ** 2],
    ["(1 + 3/n + 1/n^2)^n", Math.E ** 3],
    ["(1 + 1/n^2)^(n^2 + n)", Math.E],
    ["n^n/(n + 1)^(n + 1)*(n + 1)", 1 / Math.E],
    ["((n + 1)/(2n))^n", 0],
    ["n!/n^n", 0],
  ];
  for (const [text, want] of cases) {
    test(`${text} → ${want}`, () => {
      const L = A.sequence(text).limit({ digits: 12 });
      expect(mid(L)).toBeCloseTo(want, 9);
      expect(width(L)).toBeLessThan(1e-9);
    });
  }
  test("powers that outgrow every bound are proven to tend to infinity through their reciprocal", () => {
    expect(A.sequence("(1 + 1/n)^(n^2)").limit()).toBe(Infinity);
    expect(A.sequence("((2n + 1)/(n + 3))^n").limit()).toBe(Infinity);
    expect(A.sequence("n^n/n!").limit()).toBe(Infinity);
    expect(A.sequence("-(1 + 1/n)^(n^2)").limit()).toBe(-Infinity);
  });
  test("the limit encloses the terms far out (an independent check)", () => {
    const L = A.sequence("(n/(n + 1))^n").limit({ digits: 12 });
    const far = (1e7 / (1e7 + 1)) ** 1e7;
    expect(Math.abs(mid(L) - far)).toBeLessThan(1e-7);
  });
  test("the ratio test on Σ n!/nⁿ finds the limit 1/e", () => {
    const r = A.sum("n!/n^n").ratioTest();
    expect(r.verdict).toBe("convergent");
    expect(mid(r.limit)).toBeCloseTo(1 / Math.E, 12);
    const r2 = A.sum("n^n/n!").ratioTest();
    expect(r2.verdict).toBe("divergent");
    expect(mid(r2.limit)).toBeCloseTo(Math.E, 12);
  });
  test("(1 + 1/n)^n is proven increasing, (1 + 1/n)^(n + 1) decreasing", () => {
    const up = A.sequence("(1 + 1/n)^n").monotone();
    expect(up.direction).toBe("increasing");
    expect(up.from).toBe(1);
    expect(up.reason).toMatch(/tends to 0/);
    expect(A.sequence("(1 + 1/n)^(n + 1)").monotone().direction).toBe("decreasing");
    expect(A.sequence("(1 + 1/n)^(n + 1/2)").monotone().direction).toBe("decreasing");
    expect(A.sequence("(1 - 1/n)^n", { from: 2 }).monotone().direction).toBe("increasing");
    // the first terms agree with the proof
    const t = A.sequence("(1 + 1/n)^n").terms(6).map((x) => (x instanceof Rational ? x.toNumber() : mid(x)));
    for (let i = 1; i < t.length; i++) expect(t[i]).toBeGreaterThan(t[i - 1]);
  });
});
