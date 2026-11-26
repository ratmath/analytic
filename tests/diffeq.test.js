import { describe, test, expect } from "bun:test";
import { firstOrder, exactEquation, linearODE, laplace, inverseLaplace, linearSystem, planarSystem, seriesSolution, heat, wave, laplaceRectangle, laplaceDisc, sturmLiouville, antiderivative, parse, format } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 1e-9, maxWidth = 1e-3) => num(iv.low) <= x + slack && num(iv.high) >= x - slack && num(iv.high) - num(iv.low) < maxWidth;

describe("antiderivatives", () => {
  const int = (s, v = "x") => {
    const r = antiderivative(parse(s), v);
    return r && format(r.tree);
  };
  test("the table, partial fractions, substitution", () => {
    expect(int("x^2 + 3*x")).toBe("1/3*x^3 + 3/2*x^2");
    expect(int("1/(y*(1 - y))", "y")).toBe("log(abs(y)) - log(abs(y - 1))");
    expect(int("x*exp(x^2)")).toBe("1/2*exp(x^2)");
    expect(int("exp(2*x)*sin(3*x)")).toBe("-3/13*cos(3*x)*exp(2*x) + 2/13*sin(3*x)*exp(2*x)");
    expect(int("1/(x^2 + 4)")).toBe("1/2*atan(1/2*x)");
    expect(int("cos(x)/sin(x)")).toBe("log(abs(sin(x)))");
    expect(int("exp(-x^2)")).toBe(null);
    expect(antiderivative(parse("x*cos(x)"), "x").trust).toBe("proven");
  });
});

describe("first-order equations", () => {
  test("linear, with steps and a check against the validated solution", () => {
    const s = firstOrder("x - 2*y");
    expect(s.type).toBe("linear");
    expect(s.general).toBe("y = 1/2*x - 1/4 + C*exp(-2*x)");
    expect(s.steps.length).toBe(4);
    const p = s.through(0, 1);
    expect(p.solution).toBe("1/2*x - 1/4 + 5/4*exp(-2*x)");
    const c = p.check(1);
    expect(c.agree).toBe(true);
    expect(holds(p.at(1), 0.25 + 1.25 * Math.exp(-2))).toBe(true);
  });
  test("separable, Bernoulli, homogeneous", () => {
    const sep = firstOrder("x*y", { method: "separable" });
    expect(sep.implicit).toBe("log(abs(y)) - 1/2*x^2 = C");
    expect(sep.general).toBe("y = C*exp(1/2*x^2)");
    expect(sep.singular).toEqual(["y = 0"]);
    expect(firstOrder("x*y").types).toEqual(["linear", "separable"]);
    const logistic = firstOrder("y*(1 - y)");
    expect(logistic.type).toBe("bernoulli");
    expect(logistic.general).toBe("y = exp(x)/(C + exp(x))");
    expect(logistic.through(0, "1/2").check(1).agree).toBe(true);
    expect(firstOrder("1 + y^2").through(0, 0).solution).toBe("tan(x)");
    const hom = firstOrder("(x^2 + y^2)/(x*y)", { method: "homogeneous" });
    expect(hom.implicit).toBe("(1/2*y^2 - x^2*log(abs(x)))/x^2 = C");
    expect(hom.through(1, 1).relation.endsWith("= 1/2")).toBe(true);
    expect(firstOrder("sin(x*y)").type).toBe(null);
    expect(() => firstOrder("sin(x*y)", { method: "linear" })).toThrow();
  });
  test("exact equations and integrating factors", () => {
    const e = exactEquation("2*x*y + 1", "x^2 + 3*y^2");
    expect(e.exact).toBe(true);
    expect(e.potential).toBe("y*x^2 + x + y^3");
    expect(e.through(0, 1).relation).toBe("y*x^2 + x + y^3 = 1");
    const f = exactEquation("3*x*y + y^2", "x^2 + x*y");
    expect(f.exact).toBe(false);
    expect(f.factor).toBe("x");
    expect(f.potential).toBe("y*x^3 + 1/2*y^2*x^2");
    expect(exactEquation("y", "x^2*y + sin(x)").potential).toBe(null);
  });
});

describe("constant coefficients", () => {
  test("roots, undetermined coefficients with resonance, initial values", () => {
    const s = linearODE([1, -3, 2], "exp(x)");
    expect(s.roots.map((r) => r.root)).toEqual(["1", "2"]);
    expect(s.particular).toBe("-(x*exp(x))");
    expect(s.method).toBe("undetermined coefficients");
    expect(s.verified).toBe(true);
    expect(s.general).toBe("y = C1*exp(x) + C2*exp(2*x) - x*exp(x)");
    const i = s.initial([1, 0]);
    expect(i.constants).toEqual(["1", "0"]);
    expect(i.check(1).agree).toBe(true);
    const r = linearODE([1, 0, 4], "cos(2*x) + x");
    expect(r.particular).toBe("1/4*x*sin(2*x) + 1/4*x");
    expect(r.initial([0, 0]).check(1).agree).toBe(true);
  });
  test("complex, repeated and irrational roots; variation of parameters", () => {
    expect(linearODE([1, 2, 5]).basis).toEqual(["cos(2*x)*exp(-x)", "sin(2*x)*exp(-x)"]);
    expect(linearODE([1, 0, -2, 0, 1]).basis).toEqual(["exp(x)", "x*exp(x)", "exp(-x)", "x*exp(-x)"]);
    expect(linearODE([1, -2, -1]).roots.map((r) => r.root)).toEqual(["1 + sqrt(2)", "1 - sqrt(2)"]);
    const v = linearODE([1, -2, 1], "exp(x)/x");
    expect(v.method).toBe("variation of parameters");
    expect(v.verified).toBe(true);
    expect(() => linearODE([1, 0, 1, 1])).toThrow(/square roots/);
    expect(() => linearODE([1, 1]).initial([1, 2])).toThrow();
  });
});

describe("Laplace transforms", () => {
  test("forward and inverse", () => {
    expect(laplace("t^2*exp(-t)")).toBe("2/(s + 1)^3");
    expect(laplace("cos(2*t)")).toBe("s/(s^2 + 4)");
    expect(laplace("t*sin(3*t)")).toBe("6*s/(s^2 + 9)^2");
    expect(laplace("t", { delay: 2 })).toBe("exp(-2*s)/s^2");
    expect(inverseLaplace("1/(s^2*(s + 1))").result).toBe("-1 + t + exp(-t)");
    expect(inverseLaplace("(s + 3)/(s^2 + 2*s + 5)").result).toBe("cos(2*t)*exp(-t) + sin(2*t)*exp(-t)");
    expect(inverseLaplace("1/((s^2 + 1)*(s^2 + 4))").result).toBe("1/3*sin(t) - 1/6*sin(2*t)");
    expect(() => laplace("log(t)")).toThrow();
    expect(() => inverseLaplace("s^2/(s + 1)")).toThrow(/impulses/);
  });
});

describe("systems", () => {
  test("linear systems are classified and solved", () => {
    const s = linearSystem([[1, 2], [3, 2]]);
    expect(s.eigenvalues).toEqual(["-1", "4"]);
    expect(s.kind).toBe("saddle");
    expect(linearSystem([[0, 1], [-1, 0]]).exponential).toEqual([["cos(t)", "sin(t)"], ["-sin(t)", "cos(t)"]]);
    expect(linearSystem([[0, 1], [-1, 0]]).kind).toBe("centre");
    expect(linearSystem([[-1, 1], [0, -1]]).kind).toBe("stable degenerate node");
    expect(linearSystem([[-1, -2], [2, -1]]).kind).toBe("stable spiral");
    expect(linearSystem([[2, 0], [0, 2]]).kind).toBe("unstable star node");
    expect(linearSystem([[-2, 0], [0, -1]]).solution([1, 1])).toEqual(["exp(-2*t)", "exp(-t)"]);
  });
  test("equilibria of a damped pendulum are found, proven and classified", () => {
    const s = planarSystem(["y", "-sin(x) - y/2"]);
    const e = s.equilibria({ x: [-4, 4], y: [-2, 2] });
    expect(e.complete).toBe(true);
    expect(e.map((p) => p.kind)).toEqual(["saddle", "stable spiral", "saddle"]);
    expect(holds(e[2].point[0], Math.PI)).toBe(true);
    expect(s.jacobian()).toEqual([["0", "1"], ["-cos(x)", "-1/2"]]);
    const lv = planarSystem(["x*(1 - y)", "y*(x - 1)"]);
    expect(lv.conserves("x - log(x) + y - log(y)")).toBe(true);
    expect(lv.conserves("x + y")).toBe(false);
    expect(lv.equilibria({ x: [-1, 3], y: [-1, 3] }).length).toBe(2);
  });
});

describe("series solutions", () => {
  test("ordinary points and Frobenius", () => {
    const airy = seriesSolution({ q: "-x", order: 7 });
    expect(airy.kind).toBe("ordinary");
    expect(airy.solutions[0].text).toBe("1 + 1/6*x^3 + 1/180*x^6 + …");
    const b = seriesSolution({ p: "1/x", q: "(x^2 - 1/4)/x^2", order: 6 });
    expect(b.kind).toBe("regular singular");
    expect(b.exponents.map(String)).toEqual(["1/2", "-1/2"]);
    expect(b.solutions.length).toBe(2);
    const j0 = seriesSolution({ p: "1/x", q: "1", order: 6 });
    expect(j0.solutions[0].coefficients.map(String)).toEqual(["1", "0", "-1/4", "0", "1/64", "0", "-1/2304"]);
    expect(j0.notes.length).toBe(1);
    expect(seriesSolution({ p: "-2*x/(1 - x^2)", q: "6/(1 - x^2)" }).radius).toBeCloseTo(1, 6);
    expect(seriesSolution({ p: "1/x^2", q: "1" }).kind).toBe("irregular singular");
  });
});

describe("partial differential equations", () => {
  test("heat equation with a proven tail", () => {
    const h = heat({ initial: "x*(1 - x)", terms: 6 });
    const u = h.at("1/2", "1/10");
    const ref = (8 / Math.PI ** 3) * (Math.exp(-(Math.PI ** 2) / 10) - Math.exp(-0.9 * Math.PI ** 2) / 27);
    expect(holds(u.value, ref, 1e-9)).toBe(true);
    expect(num(u.tail)).toBeLessThan(1e-15);
    expect(h.at("1/2", 0).value).toBe(null);
    expect(holds(heat({ initial: "x", ends: "insulated", terms: 6 }).at("1/4", "1/20").value, 0.32541889, 1e-6)).toBe(true);
  });
  test("Laplace on a rectangle and a disc", () => {
    const r = laplaceRectangle({ top: "sin(pi*x)", terms: 4 }).at("1/2", "1/2");
    expect(holds(r.value, Math.sinh(Math.PI / 2) / Math.sinh(Math.PI), 1e-9, 1e-2)).toBe(true);
    const d = laplaceDisc({ boundary: "cos(theta)^2", terms: 4 });
    expect(holds(d.mean, 0.5)).toBe(true);
    expect(holds(d.at("1/2", 0).partial, 0.625, 1e-9)).toBe(true);
  });
  test("wave equation by d'Alembert, on an interval and on the line", () => {
    const w = wave({ length: 1, position: "sin(pi*x)" });
    expect(holds(w.at("1/4", "1/3"), Math.sin(Math.PI / 4) * Math.cos(Math.PI / 3))).toBe(true);
    expect(holds(w.at("1/4", "7/3"), Math.sin(Math.PI / 4) * Math.cos((7 * Math.PI) / 3))).toBe(true);
    expect(holds(wave({ length: 1, velocity: "sin(pi*x)" }).at("1/2", "1/2"), 1 / Math.PI)).toBe(true);
    expect(holds(wave({ c: 2, position: "exp(-x^2)" }).at(1, "1/2"), (1 + Math.exp(-4)) / 2)).toBe(true);
    expect(holds(w.modes(2)[0].cos, 1)).toBe(true);
  });
  test("Sturm-Liouville eigenvalues are bracketed by validated solutions", () => {
    const e = sturmLiouville({ interval: [0, 1], count: 2 });
    expect(e.map((v) => v.proven)).toEqual([true, true]);
    expect(holds(e[0].eigenvalue, Math.PI ** 2, 0)).toBe(true);
    expect(holds(e[1].eigenvalue, 4 * Math.PI ** 2, 0)).toBe(true);
    expect(sturmLiouville({ q: "x", interval: [0, 1], count: 1, certify: false })[0].proven).toBe(false);
  });
});
