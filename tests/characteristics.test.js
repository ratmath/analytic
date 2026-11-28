// First-order equations by characteristics and exact finite-mode Laplace
// solutions. Each answer is checked a second way: the closed formula is put
// back into the equation, a foot is tested against the conserved quantity of
// the characteristic, or the value against the implicit relation.
import { test, expect, describe } from "bun:test";
import { Rational } from "@ratmath/core";
import { transport, pde, laplaceDisc, laplaceRectangle } from "../index.js";

const n = (q) => q.toNumber();
const mid = (iv) => (n(iv.low) + n(iv.high)) / 2;
const has = (iv, x, slack = 1e-12) => n(iv.low) - slack <= x && x <= n(iv.high) + slack;

describe("transport: linear equations", () => {
  test("constant speed: u_t + 2u_x = 0", () => {
    const u = pde.transport({ speed: 2, initial: "exp(-x^2)" });
    expect(u.kind).toBe("constant speed");
    expect(u.formula).toBe("exp(-(x - 2*t)^2)");
    expect(u.characteristics).toBe("x - 2*t = const");
    const p = u.at(1, "1/2");
    expect(p.value.low.equals(new Rational(1n))).toBe(true);
    expect(p.value.high.equals(new Rational(1n))).toBe(true);
    expect(p.foot.low.equals(new Rational(0n))).toBe(true);
    expect(u.crossing.never).toBe(true);
    for (const [x, t] of [["3/10", "7/5"], [-2, "1/3"]]) expect(has(u.residual(x, t), 0, 0)).toBe(true);
  });
  test("decay and source", () => {
    const u = transport({ speed: -1, decay: 3, source: 2, initial: "sin(x)" });
    const v = u.at(1, "1/2").value;
    const want = Math.sin(1.5) * Math.exp(-1.5) + (2 / 3) * (1 - Math.exp(-1.5));
    expect(has(v, want)).toBe(true);
    expect(n(v.high) - n(v.low)).toBeLessThan(1e-12);
    const r = u.residual("3/10", "7/5");
    expect(has(r, 0, 0)).toBe(true);
    expect(n(r.high) - n(r.low)).toBeLessThan(1e-12);
  });
  test("source without decay", () => {
    const u = transport({ speed: 1, source: 5, initial: "x" });
    expect(has(u.at(3, 2).value, 1 + 10, 0)).toBe(true);
    expect(has(u.residual(3, 2), 0, 0)).toBe(true);
  });
  test("speed a*x + b: a closed foot", () => {
    const u = transport({ speed: "x", initial: "1/(1+x^2)" });
    expect(u.kind).toBe("linear speed");
    expect(u.foot).toBe("x*exp(-t)");
    expect(has(u.at(1, 1).value, 1 / (1 + Math.exp(-2)))).toBe(true);
    expect(has(u.residual("3/10", "7/5"), 0, 0)).toBe(true);
    const w = transport({ speed: "2*x - 3", initial: "x" });
    expect(has(w.at(2, 1).foot, (2 - 1.5) * Math.exp(-2) + 1.5)).toBe(true);
    expect(has(w.residual(2, 1), 0, 0)).toBe(true);
  });
  test("variable speed: the foot by a validated solve", () => {
    // dx/dt = t·x keeps x·e^(−t²/2): the foot of (1, 1) is e^(−1/2), and u = ξ² = e^(−1)
    const u = transport({ speed: "t*x", initial: "x^2" });
    expect(u.kind).toBe("variable speed");
    const p = u.at(1, 1);
    expect(has(p.value, Math.exp(-1))).toBe(true);
    expect(n(p.value.high) - n(p.value.low)).toBeLessThan(1e-9);
    expect(u.crossing.never).toBe(true);
    // dx/dt = 1/(1 + x²) keeps x + x³/3 − t
    const w = transport({ speed: "1/(1+x^2)", initial: "x" });
    const xi = mid(w.at(1, 1).foot);
    expect(Math.abs(xi + xi ** 3 / 3 - 1 / 3)).toBeLessThan(1e-9);
    expect(() => w.residual(1, 1)).toThrow();
  });
  test("refusals", () => {
    expect(() => transport({ speed: "u*x", initial: "x" })).toThrow();
    expect(() => transport({ speed: "u", decay: 1, initial: "x" })).toThrow();
    expect(() => transport({ speed: "a", initial: "x" })).toThrow();
    expect(() => transport({ speed: 1, initial: "x*y" })).toThrow();
  });
});

describe("transport: Burgers and its relatives", () => {
  test("breaking time of u_t + u·u_x = 0 from a Gaussian is sqrt(e/2)", () => {
    const u = transport({ speed: "u", initial: "exp(-x^2)", interval: [-4, 4] });
    expect(u.kind).toBe("quasilinear");
    expect(u.crossing.never).toBe(false);
    expect(has(u.crossing.time, Math.sqrt(Math.E / 2), 0)).toBe(true);
    expect(n(u.crossing.time.high) - n(u.crossing.time.low)).toBeLessThan(1e-5);
    // before breaking: the value satisfies u = f(x − u·t)
    const v = mid(u.at(1, "1/2").value);
    expect(Math.abs(v - Math.exp(-((1 - v / 2) ** 2)))).toBeLessThan(1e-12);
    expect(() => u.at(1, 2)).toThrow(/crossed/);
  });
  test("without an interval the bracket itself must be shown free of crossings", () => {
    const u = transport({ speed: "u", initial: "exp(-x^2)" });
    expect(u.crossing.never).toBe(null);
    const v = mid(u.at(1, "1/2").value);
    expect(Math.abs(v - Math.exp(-((1 - v / 2) ** 2)))).toBeLessThan(1e-12);
    expect(() => u.at(1, "3/2")).toThrow(/crossed/);
  });
  test("a speed that never decreases: no crossing, any time", () => {
    const u = transport({ speed: "u", initial: "atan(x)" });
    expect(u.crossing.never).toBe(true);
    const p = u.at(1, 3);
    const xi = mid(p.foot);
    expect(Math.abs(xi + 3 * Math.atan(xi) - 1)).toBeLessThan(1e-12);
    expect(has(p.value, Math.atan(xi), 1e-12)).toBe(true);
  });
  test("speed u^2", () => {
    // F = 1/(1+ξ²)², F′ = −4ξ/(1+ξ²)³, least at ξ = 1/√5: −4/√5·(5/6)³
    const u = transport({ speed: "u^2", initial: "1/(1+x^2)", interval: [-5, 5] });
    const least = (-4 / Math.sqrt(5)) * (5 / 6) ** 3;
    expect(has(u.crossing.time, -1 / least, 1e-9)).toBe(true);
  });
});

describe("Laplace with finitely many modes is exact", () => {
  test("disc: cos(theta) on the unit circle gives r*cos(theta)", () => {
    const u = laplaceDisc({ boundary: "cos(theta)" });
    expect(u.exact).toBe(true);
    expect(u.closedForm).toBe("r*cos(theta)");
    const p = u.at("1/2", 0);
    expect(p.value.low.equals(new Rational(1n, 2n))).toBe(true);
    expect(p.value.high.equals(new Rational(1n, 2n))).toBe(true);
    expect(p.tail.numerator).toBe(0n);
  });
  test("disc: powers and products are expanded", () => {
    // cos² = 1/2 + cos(2θ)/2; on radius 2 at r = 1, θ = π/4: 1/2 − 1/4 + 3·(1/4)·1 + 0
    const u = laplaceDisc({ boundary: "cos(theta)^2 + 3*sin(2*theta) - 1/4", radius: 2 });
    expect(u.exact).toBe(true);
    const p = u.at(1, "1/8").value;
    expect(p.low.equals(new Rational(1n))).toBe(true);
    expect(p.high.equals(new Rational(1n))).toBe(true);
    // sin³ = (3 sin θ − sin 3θ)/4
    const w = laplaceDisc({ boundary: "sin(theta)^3" });
    expect(w.modes.map((m) => [m.n, String(m.b)])).toEqual([[1, "3/4"], [3, "-1/4"]]);
    const v = w.at("1/2", "1/12").value; // θ = π/6
    expect(has(v, (3 / 4) * 0.5 * 0.5 - (1 / 4) * 0.125 * 1, 0)).toBe(true);
  });
  test("disc: other boundary values still use the series", () => {
    const u = laplaceDisc({ boundary: "abs(sin(theta))" });
    expect(u.exact).toBeUndefined();
    expect(u.at("1/2", 0).value).not.toBe(null);
  });
  test("rectangle: a finite sine sum on the top edge", () => {
    const u = laplaceRectangle({ top: "sin(pi*x) + 2*sin(3*pi*x)" });
    expect(u.exact).toBe(true);
    expect(u.closedForm).toBe("sinh(pi*y)/sinh(pi)*sin(pi*x) + 2*sinh(3*pi*y)/sinh(3*pi)*sin(3*pi*x)");
    const v = u.at("1/2", "1/2").value;
    const want = Math.sinh(Math.PI / 2) / Math.sinh(Math.PI) - (2 * Math.sinh(1.5 * Math.PI)) / Math.sinh(3 * Math.PI);
    expect(has(v, want)).toBe(true);
    expect(n(v.high) - n(v.low)).toBeLessThan(1e-12);
    const top = u.at("1/2", 1).value; // sin(π/2) + 2 sin(3π/2) = −1 exactly
    expect(top.low.equals(new Rational(-1n))).toBe(true);
    expect(top.high.equals(new Rational(-1n))).toBe(true);
    expect(laplaceRectangle({ top: "x*(1-x)" }).exact).toBeUndefined();
    // a width other than 1 changes the basic angle
    expect(laplaceRectangle({ width: 2, top: "sin(pi*x/2)" }).exact).toBe(true);
    expect(laplaceRectangle({ width: 2, top: "sin(pi*x/3)" }).exact).toBeUndefined();
  });
});
