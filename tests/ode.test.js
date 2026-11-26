import { describe, test, expect } from "bun:test";
import { R } from "@ratmath/core";
import { ode, exp, AnalyticError } from "../index.js";
import { expectEncloses } from "./helpers.js";

const contains = (iv, x, slack = 0) => iv.low.toNumber() <= x + slack && iv.high.toNumber() >= x - slack;
const width = (iv) => iv.high.subtract(iv.low).toNumber();

describe("validated ODE steps", () => {
  test("y' = y from 1 gives e at t = 1", () => {
    const r = ode.solve({ f: "y", y0: 1, until: 1, order: 12 });
    expect(Math.abs(r.quick.value.y.at(-1) - Math.E)).toBeLessThan(1e-9);
    const sol = r.exact();
    expect(sol.complete).toBe(true);
    expectEncloses(sol.final, "2.718281828459045235360287471352662497757", "1e-10");
    expect(contains(sol.at("1/2"), Math.exp(0.5), 1e-15)).toBe(true);
  });
  test("y' = -2ty gives exp(-t²)", () => {
    const sol = ode.solve({ f: "-2*t*y", y0: 1, until: 1 }).exact();
    for (const t of ["1/4", "1/2", "1"]) {
      const x = Number(eval(t));
      expect(contains(sol.at(t), Math.exp(-x * x), 1e-15)).toBe(true);
    }
    expect(width(sol.final)).toBeLessThan(1e-9);
  });
  test("a system: the harmonic oscillator", () => {
    const sol = ode.solve({ f: ["v", "-x"], vars: ["x", "v"], y0: [1, 0], until: 3, order: 12 }).exact();
    const [x, v] = sol.final;
    expect(contains(x, Math.cos(3), 1e-15)).toBe(true);
    expect(contains(v, -Math.sin(3), 1e-15)).toBe(true);
    expect(width(x)).toBeLessThan(1e-8);
  });
  test("interval initial values are carried", () => {
    const sol = ode.solve({ f: "y", y0: R`1:101/100`, until: "1/2" }).exact();
    expect(contains(sol.final, Math.exp(0.5))).toBe(true);
    expect(contains(sol.final, 1.01 * Math.exp(0.5))).toBe(true);
  });
  test("a Riccati equation matches a fine RK4 run", () => {
    const r = ode.solve({ f: "y^2 + t", y0: "1/2", until: "1/2", previewSteps: 4000 });
    const sol = r.exact();
    expect(contains(sol.final, r.quick.value.y.at(-1), 1e-12)).toBe(true);
    expect(width(sol.final)).toBeLessThan(1e-9);
  });
  test("function right-hand sides take models", () => {
    const sol = ode.solve({ f: (t, y) => exp(y.negate()), float: (t, y) => Math.exp(-y), y0: 0, until: "1/2", order: 8, tol: "1e-9" }).exact();
    // y = log(1 + t)
    expect(contains(sol.final, Math.log(1.5), 1e-15)).toBe(true);
  });
  test("blow-up stops with a reason instead of a wrong enclosure", () => {
    const sol = ode.solve({ f: "y^2", y0: 1, until: 2, maxSteps: 60 }).exact();
    expect(sol.complete).toBe(false);
    expect(sol.t1.toNumber()).toBeLessThan(1);
    // y = 1/(1 − t)
    const t = sol.t1.toNumber();
    expect(contains(sol.final, 1 / (1 - t), 1e-9 / (1 - t) ** 2)).toBe(true);
  }, 20000);
  test("single steps and refusals", () => {
    const s = ode.step({ f: "y", y0: 1, step: "1/4" });
    expect(contains(s.model.at(R`1/4`), Math.exp(0.25), 1e-15)).toBe(true);
    expect(() => ode.step({ f: "y^2", y0: 1, step: 4 })).toThrow(AnalyticError);
    expect(() => ode.solve({ f: "y + k", y0: 1, until: 1 })).toThrow(AnalyticError);
  });
  test("progress ticks carry the solution so far", () => {
    const ticks = [...ode.solve({ f: "-y", y0: 1, until: 2, step: "1/2" }).stages()].filter((s) => s.stage === "progress");
    expect(ticks.length).toBeGreaterThan(1);
    expect(ticks.at(-1).done).toBe(1000);
    expect(ticks[0].partial.steps.length).toBe(1);
  });
});
