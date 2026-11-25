import { describe, test, expect } from "bun:test";
import { fourier, FourierSeries, bvp, fn } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 0) => num(iv.low) <= x + slack && num(iv.high) >= x - slack;
const width = (iv) => num(iv.high.subtract(iv.low));

describe("Fourier series", () => {
  test("the sawtooth x on [-1, 1]: bₙ = 2·(−1)^(n+1)/(nπ)", () => {
    const r = fourier("x", [-1, 1], { terms: 6 });
    expect(r.quick.value.b[1]).toBeCloseTo(2 / Math.PI, 10);
    const F = r.exact();
    expect(F).toBeInstanceOf(FourierSeries);
    for (let n = 1; n <= 6; n++) {
      expect(holds(F.b[n], (2 * (-1) ** (n + 1)) / (n * Math.PI), 1e-15)).toBe(true);
      expect(width(F.b[n])).toBeLessThan(1e-9);
      expect(holds(F.a[n], 0)).toBe(true);
    }
    expect(num(F.period)).toBe(2);
    expect(F.toString(2, 4)).toBe("0.6366*sin(pi*x) - 0.3183*sin(2*pi*x)");
  });
  test("a square wave given piecewise: only odd sines, 4/(nπ)", () => {
    const F = fourier("-1 if -1:x:!0; 1 if 0:x:1", [-1, 1], { terms: 5 }).exact();
    expect(holds(F.b[1], 4 / Math.PI, 1e-15)).toBe(true);
    expect(holds(F.b[2], 0)).toBe(true);
    expect(holds(F.b[3], 4 / (3 * Math.PI), 1e-15)).toBe(true);
    // the partial sum is a function to plot
    const S = F.partial(5);
    expect(S.float(0.5)).toBeCloseTo((4 / Math.PI) * (1 - 1 / 3 + 1 / 5), 9);
    expect(holds(F.value("1/2", 5), (4 / Math.PI) * (1 - 1 / 3 + 1 / 5), 1e-12)).toBe(true);
  });
  test("Parseval gives the mean-square error of a partial sum", () => {
    const F = fourier("x^2", [-1, 1], { terms: 6 }).exact();
    expect(holds(F.a[0], 2 / 3, 1e-15)).toBe(true);
    expect(holds(F.a[1], -4 / Math.PI ** 2, 1e-15)).toBe(true);
    expect(holds(F.meanSquare(), 1 / 5, 1e-15)).toBe(true);
    // (1/2)·∫(x² − S_N)² = ½·Σ_{n>N} (4/(n²π²))²
    let tail = 0;
    for (let n = 7; n < 200000; n++) tail += 0.5 * (4 / (n * n * Math.PI ** 2)) ** 2;
    const e = F.meanSquareError();
    expect(holds(e, tail, 1e-9)).toBe(true);
    expect(num(F.meanSquareError(2).low)).toBeGreaterThan(num(e.high));
  });
  test("half-range sine and cosine series", () => {
    const s = fourier("1", [0, 1], { terms: 3, kind: "sine" }).exact();
    expect(holds(s.b[1], 4 / Math.PI, 1e-15)).toBe(true);
    expect(holds(s.b[2], 0)).toBe(true);
    expect(num(s.period)).toBe(2);
    const c = fourier("x", [0, 1], { terms: 3, kind: "cosine" }).exact();
    expect(holds(c.a[0], 1, 1e-15)).toBe(true);
    expect(holds(c.a[1], -4 / Math.PI ** 2, 1e-15)).toBe(true);
    expect(c.b[1].toString()).toBe("0:0");
  });
  test("bad input is refused", () => {
    expect(() => fourier("x", [1, 0])).toThrow();
    expect(() => fourier("x", [0, 1], { kind: "other" })).toThrow();
  });
});

describe("boundary value problems", () => {
  test("y″ = −y, y(0) = 0, y(1) = 1 is sin(x)/sin(1)", () => {
    const r = bvp({ f: "-y", interval: [0, 1], left: { y: 0 }, right: { y: 1 } });
    expect(r.quick.value.start).toBeCloseTo(1 / Math.sin(1), 8);
    const s = r.exact();
    expect(s.unique).toBe(true);
    expect(s.unknown).toBe("dy");
    expect(holds(s.start, 1 / Math.sin(1))).toBe(true);
    expect(holds(s.at("1/2"), Math.sin(0.5) / Math.sin(1))).toBe(true);
    expect(width(s.at("1/2"))).toBeLessThan(1e-6);
    expect(holds(s.slopeAt(1), Math.cos(1) / Math.sin(1))).toBe(true);
  });
  test("a slope condition on the left and on the right", () => {
    // y″ = 6x, y(0) = 0, y′(2) = 12: y = x³
    const a = bvp({ f: "6x", interval: [0, 2], left: { y: 0 }, right: { dy: 12 } }).exact();
    expect(holds(a.at(1), 1)).toBe(true);
    // y″ = y + x, y′(0) = 0, y(1) = 1
    const b = bvp({ f: "y + x", interval: [0, 1], left: { dy: 0 }, right: { y: 1 } }).exact();
    expect(b.unknown).toBe("y");
    // y = A·cosh(x) + sinh(x) − x with A = (2 − sinh 1)/cosh 1
    const A = (2 - Math.sinh(1)) / Math.cosh(1);
    expect(holds(b.at("1/2"), A * Math.cosh(0.5) + Math.sinh(0.5) - 0.5)).toBe(true);
  });
  test("a nonlinear problem is enclosed without a uniqueness claim", () => {
    const r = bvp({ f: "-y^2", interval: [0, "1/4"], left: { y: 0 }, right: { y: 1 } });
    const s = r.exact();
    expect(s.unique).toBe(false);
    expect(holds(s.start, r.quick.value.start, 1e-9)).toBe(true);
    expect(width(s.start)).toBeLessThan(1e-6);
    // the tube ends on the right-hand condition
    expect(holds(s.at("1/4"), 1)).toBe(true);
    expect(width(s.at("1/8"))).toBeLessThan(1e-6);
  }, 30000);
  test("bad input is refused", () => {
    expect(() => bvp({ f: "-y", interval: [1, 0], left: { y: 0 }, right: { y: 1 } })).toThrow();
    expect(() => bvp({ f: "-y + k", interval: [0, 1], left: { y: 0 }, right: { y: 1 } })).toThrow(/no value/);
    expect(() => bvp({ f: "-y", interval: [0, 1], left: { z: 0 }, right: { y: 1 } })).toThrow();
  });
});
