import { describe, test, expect } from "bun:test";
import { R } from "@ratmath/core";
import { fn, live, Refinement } from "../index.js";
import { expectEncloses } from "./helpers.js";

const contains = (iv, x, slack = 0) => iv.low.toNumber() <= x + slack && iv.high.toNumber() >= x - slack;

describe("fast first, certified last", () => {
  const f = fn("exp(sin(x))*x");
  test("value: float preview, then an enclosure with the requested digits", () => {
    const r = f.value("1/3", { digits: 30 });
    expect(r).toBeInstanceOf(Refinement);
    expect(r.quick.stage).toBe("float");
    expect(r.quick.trust).toBe("good");
    // exp(sin(1/3))/3 to 40 digits
    expectEncloses(r.exact(), "0.462357169757048936144153527638614114932385013516615408658", "1e-29");
    expect(r.exactStage().via).toContain("bits");
    expect(contains(r.exact(), r.quick.value, 1e-15)).toBe(true);
  });
  test("rational-only formulas give exact points", () => {
    const r = fn("x^2 - 1/3").value("1/2");
    expect(r.exact().toString()).toBe("-1/12:-1/12");
    expect(r.exactStage().via).toBe("exact rational arithmetic");
  });
  test("range: sampled preview, certified outer bound tight to the digits", () => {
    const r = fn("x*cos(x)").range(R`0:3`, { digits: 6 });
    expect(r.quick.trust).toBe("rough");
    const iv = r.exact();
    // max of x cos x on [0, 3] is at x ≈ 0.8603335890, value 0.5610963381; min at 3: 3cos 3
    expect(contains(iv, 0.5610963381910451)).toBe(true);
    expect(contains(iv, 3 * Math.cos(3))).toBe(true);
    expect(iv.high.toNumber() - 0.5610963381910451).toBeLessThan(1e-5);
    expect(3 * Math.cos(3) - iv.low.toNumber()).toBeLessThan(1e-5);
  });
  test("integral: Gauss–Legendre preview, certified enclosure", () => {
    const r = fn("exp(-x^2)").integral(0, 1, { digits: 20 });
    expect(Math.abs(r.quick.value - 0.7468241328124271)).toBeLessThan(1e-14);
    // ∫_0^1 e^{-x²} = √π/2 · erf(1)
    expectEncloses(r.exact(), "0.7468241328124270253994674361318530053544", "1e-19");
    const back = fn("x").integral(1, 0).exact();
    expect(back.toString()).toBe("-1/2:-1/2");
  });
  test("progress ticks carry partial enclosures that shrink", () => {
    const widths = [...fn("exp(sin(x))*x").range(R`0:3`, { digits: 4 }).stages()]
      .filter((s) => s.stage === "progress")
      .map((s) => s.partial.high.subtract(s.partial.low).toNumber());
    expect(widths.length).toBeGreaterThan(0);
    for (let i = 1; i < widths.length; i++) expect(widths[i]).toBeLessThanOrEqual(widths[i - 1] + 1e-12);
  });
  test("live: previews at once, only the latest question settles", async () => {
    const seen = [];
    const g = fn("a*sin(x)", { params: { a: 1 } });
    const update = live((a) => g.with({ a }).value("1/2", { digits: 25 }), (s) => seen.push(s), { idleMs: 30 });
    update("1");
    update("2");
    const last = update("3");
    await last.settle();
    await new Promise((r) => setTimeout(r, 120));
    expect(seen.filter((s) => s.stage === "float").length).toBe(3);
    const exacts = seen.filter((s) => s.exact);
    expect(exacts.length).toBe(1);
    expect(contains(exacts[0].value, 3 * Math.sin(0.5), 1e-15)).toBe(true);
  });
});
