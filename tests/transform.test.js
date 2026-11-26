import { describe, test, expect } from "bun:test";
import { Rational } from "@ratmath/core";
import { fourierTransform, inverseFourier, convolution, heatLine, cyclotomic, rootOfUnity, dft, fft, alias, sinusoidSamples, sample } from "../index.js";

const mid = (iv) => (iv.low.toNumber() + iv.high.toNumber()) / 2;
// the expected values are doubles, so allow for their own rounding
const has = (iv, x) => iv.low.toNumber() - 1e-12 <= x && x <= iv.high.toNumber() + 1e-12;

describe("Fourier transform", () => {
  test("Gaussian: certified values and the checked formula", () => {
    const t = fourierTransform("exp(-x^2)");
    expect(t.formula.text).toBe("sqrt(pi)*exp(-1/4*w^2)");
    expect(t.pairs).toEqual(["Gaussian"]);
    const v = t.at(2);
    expect(has(v.re, Math.sqrt(Math.PI) * Math.exp(-1))).toBe(true);
    expect(has(v.im, 0)).toBe(true);
    expect(t.check("1/3").agrees).toBe(true);
  });
  test("shift, multiplication by x, two-sided exponential, Lorentzian", () => {
    const s = fourierTransform("exp(-(x-1)^2)");
    expect(s.formula.re).toBe("sqrt(pi)*exp(-1/4*w^2)*cos(w)");
    expect(fourierTransform("x*exp(-x^2)").formula.text.startsWith("i*(")).toBe(true);
    expect(fourierTransform("3*exp(-2*abs(x))").formula.text).toBe("12/(w^2 + 4)");
    const l = fourierTransform("1/(1+x^2)");
    expect(l.formula.text).toBe("pi*exp(-abs(w))");
    expect(has(l.at(1).re, Math.PI / Math.E)).toBe(true);
  });
  test("support: box and one-sided exponential", () => {
    expect(fourierTransform("1", { support: [-1, 1] }).formula.text).toBe("2*(sin(w)/w)");
    const e = fourierTransform("exp(-x)", { support: [0, "inf"] });
    const v = e.at(2);
    expect(has(v.re, 1 / 5)).toBe(true);
    expect(has(v.im, -2 / 5)).toBe(true);
    expect(e.formula.re).toBe("1/(w^2 + 1)");
  });
  test("no pair: values without a formula", () => {
    const t = fourierTransform("exp(-x^4)");
    expect(t.formula).toBe(null);
    expect(mid(t.at(0).re)).toBeCloseTo(1.8128049541, 8);
    expect(() => t.parseval()).toThrow();
  });
  test("conventions", () => {
    const f = fourierTransform("exp(-x^2)", { convention: "frequency" });
    expect(has(f.at("1/2").re, Math.sqrt(Math.PI) * Math.exp(-Math.PI * Math.PI / 4))).toBe(true);
    expect(f.check("1/2").agrees).toBe(true);
    const u = fourierTransform("exp(-x^2/2)", { convention: "unitary" });
    expect(has(u.at(1).re, Math.exp(-0.5))).toBe(true);
    expect(() => fourierTransform("exp(-x^2)", { convention: "other" })).toThrow();
  });
  test("inversion, Parseval, convolution theorem", () => {
    const t = fourierTransform("exp(-x^2)");
    const inv = t.inversion("1/2");
    expect(inv.agrees).toBe(true);
    expect(has(inv.value, Math.exp(-0.25))).toBe(true);
    const p = t.parseval();
    expect(p.agrees).toBe(true);
    expect(has(p.time, Math.sqrt(Math.PI / 2))).toBe(true);
    const c = convolution("exp(-x^2)", "exp(-abs(x))").theorem(1);
    expect(c.agrees).toBe(true);
    expect(has(inverseFourier("pi*exp(-abs(w))").at(0).re, 1)).toBe(true);
  });
  test("integrals that do not converge absolutely are refused", () => {
    expect(() => fourierTransform("1/(1+abs(x))").at(1)).toThrow();
  });
  test("heat equation on the line", () => {
    const h = heatLine({ initial: "exp(-x^2)" });
    // u = exp(-x²/(1+4t))/√(1+4t)
    expect(has(h.at(1, "1/2"), Math.exp(-1 / 3) / Math.sqrt(3))).toBe(true);
    expect(h.check(1, "1/2").agrees).toBe(true);
    expect(has(h.at("1/2", 0), Math.exp(-0.25))).toBe(true);
    expect(has(h.heat(), Math.sqrt(Math.PI))).toBe(true);
    expect(() => h.at(0, -1)).toThrow();
  });
});

describe("discrete Fourier transform", () => {
  test("cyclotomic polynomials", () => {
    expect(cyclotomic(1).map(String)).toEqual(["-1", "1"]);
    expect(cyclotomic(6).map(String)).toEqual(["1", "-1", "1"]);
    expect(cyclotomic(12).map(String)).toEqual(["1", "0", "-1", "0", "1"]);
  });
  test("roots of unity are exact", () => {
    const z = rootOfUnity(5);
    let sum = rootOfUnity(5, 0);
    for (let k = 1; k < 5; k++) sum = sum.add(rootOfUnity(5, k));
    expect(sum.rational().equals(new Rational(0n))).toBe(true);
    expect(z.multiply(z.conjugate()).rational().equals(new Rational(1n))).toBe(true);
    expect(rootOfUnity(8, 2).multiply(rootOfUnity(8, 2)).rational().equals(new Rational(-1n))).toBe(true);
    const e = z.enclose(12);
    expect(has(e.re, Math.cos((2 * Math.PI) / 5))).toBe(true);
    expect(has(e.im, Math.sin((2 * Math.PI) / 5))).toBe(true);
  });
  test("definition, inverse, Parseval", () => {
    const d = dft([1, 2, 3, 4]);
    expect(d.text).toEqual(["10", "-2 + 2ζ", "-2", "-2 - 2ζ"]);
    const x = [1, 2, 0, 0, 1, "1/3"];
    const X = dft(x);
    const back = dft(X.values, { inverse: true });
    expect(back.values.map((z) => z.rational().toString())).toEqual(["1", "2", "0", "0", "1", "1/3"]);
    const energy = X.values.reduce((s, z) => s.add(z.norm2()), rootOfUnity(6, 0).scale(0)).rational();
    expect(energy.equals(new Rational(6n).multiply(new Rational(55n, 9n)))).toBe(true);
  });
  test("fast transform agrees exactly and counts its work", () => {
    const f = fft([1, 2, 3, 4, 5, 6, 7, 8]);
    expect(f.agrees).toBe(true);
    expect(f.multiplications).toBe(12);
    expect(f.definition).toBe(64);
    expect(f.levels).toBe(3);
    const back = fft(f.values, { inverse: true });
    expect(back.values.map((z) => z.rational().toString())).toEqual(["1", "2", "3", "4", "5", "6", "7", "8"]);
    expect(() => fft([1, 2, 3])).toThrow();
  });
  test("aliasing", () => {
    const a = alias(7, 8);
    expect(a.alias.toString()).toBe("1");
    expect(a.sign).toBe(-1);
    expect(a.aliased).toBe(true);
    expect(alias(3, 8).aliased).toBe(false);
    expect(alias("9/2", 4).alias.toString()).toBe("1/2");
    const seven = sinusoidSamples({ frequency: 7, rate: 8, count: 8 });
    const one = sinusoidSamples({ frequency: 1, rate: 8, count: 8 });
    expect(seven.every((z, i) => z.equals(one[i]))).toBe(true);
    expect(dft(seven).text).toEqual(["0", "4", "0", "0", "0", "0", "0", "4"]);
    const s7 = sinusoidSamples({ frequency: 7, rate: 8, count: 8, kind: "sin" });
    const s1 = sinusoidSamples({ frequency: 1, rate: 8, count: 8, kind: "sin" });
    expect(s7.every((z, i) => z.equals(s1[i].scale(-1)))).toBe(true);
    expect(() => sinusoidSamples({ frequency: 1, rate: 3, count: 8 })).toThrow();
    const s = sample("cos(2*pi*7*t)", { rate: 8, count: 3 });
    expect(s.times.map(String)).toEqual(["0", "1/8", "1/4"]);
    expect(has(s.values[1], Math.SQRT1_2)).toBe(true);
  });
});
