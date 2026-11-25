import { describe, test, expect } from "bun:test";
import { MultiRegion } from "@ratmath/core";
import { field, ScalarField, divergence, curl, jacobian, lineIntegral, surfaceIntegral } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 0) => num(iv.low) <= x + slack && num(iv.high) >= x - slack;
const width = (iv) => num(iv.high.subtract(iv.low));
const exact = (r) => r.exactStage().value;

describe("fields", () => {
  const f = field("x^2*y + sin(x*y)", ["x", "y"]);
  test("symbolic partials", () => {
    expect(f).toBeInstanceOf(ScalarField);
    expect(String(field("x^2*y", ["x", "y"]).partial("x"))).toBe("2*x*y");
    expect(String(field("x^2*y", ["x", "y"]).partial("x", "y"))).toBe("2*x");
    expect(String(field("x^2 + y^2 + z^2", ["x", "y", "z"]).laplacian())).toBe("6");
    expect(f.gradient().length).toBe(2);
    expect(f.hessian()[0][1].float([1, 2])).toBeCloseTo(f.hessian()[1][0].float([1, 2]), 12);
  });
  test("an unbound name is refused", () => {
    expect(() => field("x + a", ["x"])).toThrow(/no value/);
    expect(field("x + a", ["x"], { params: { a: 2 } }).float([1])).toBe(3);
  });
  test("values and jets are certified", () => {
    const v = exact(f.value({ x: 1, y: "1/2" }));
    expect(holds(v, 0.5 + Math.sin(0.5))).toBe(true);
    expect(width(v)).toBeLessThan(1e-18);
    const j = f.jet([1, "1/2"]);
    expect(holds(j.gradient[0], 1 + 0.5 * Math.cos(0.5), 1e-15)).toBe(true);
    expect(holds(j.gradient[1], 1 + Math.cos(0.5), 1e-15)).toBe(true);
    expect(holds(j.hessian[0][1], 2 + Math.cos(0.5) - 0.5 * Math.sin(0.5), 1e-15)).toBe(true);
    expect(exact(field("x*y", ["x", "y"]).value([3, "2/3"])).low.toString()).toBe("2");
  });
  test("a kink is reported, not differentiated", () => {
    const j = field("abs(x) + y", ["x", "y"]).jet({ x: [-1, 1], y: 0 });
    expect(j.smooth).toBe(false);
    expect(j.gradient).toBe(null);
    expect(holds(j.value, 0.5)).toBe(true);
  });
  test("directional derivative and tangent plane", () => {
    const d = exact(field("x^2 + y^2", ["x", "y"]).directional([1, 2], [3, 4]));
    expect(holds(d, (2 * 3 + 4 * 4) / 5, 1e-15)).toBe(true);
    const L = field("x^2 + y^2", ["x", "y"]).linearization([1, 2]);
    expect(L.float([1, 2])).toBeCloseTo(5, 12);
    expect(L.float([2, 2])).toBeCloseTo(7, 12);
  });
  test("substitution gives a function of what is left", () => {
    const g = f.substitute({ y: 2 });
    expect(g.float(1)).toBeCloseTo(2 + Math.sin(2), 12);
    const along = field("x^2 + y^2", ["x", "y"]).along({ x: "cos(t)", y: "sin(t)" });
    expect(along.float(0.7)).toBeCloseTo(1, 12);
  });
});

describe("integrals over regions", () => {
  test("polynomials over boxes and simplices are exact", () => {
    expect(exact(field("x*y*z", ["x", "y", "z"]).integral({ x: [0, 1], y: [0, 1], z: [0, 1] })).toString()).toBe("1/8:1/8");
    expect(exact(field("x*y", ["x", "y"]).integral("0:x:1 && 0:y:x")).low.toString()).toBe("1/8");
    expect(exact(field("1", ["x", "y", "z"]).integral("0:x:1 && 0:y:1-x && 0:z:1-x-y")).low.toString()).toBe("1/6");
    expect(exact(field("x + y", ["x", "y"]).integral({ x: [0, 1], y: ["0", "x^2"] })).low.toString()).toBe("7/20");
  });
  test("a polygon with two upper sides, as text and as a Core region", () => {
    const text = "0:x:_ && 0:y:_ && _:y:4-x && _:y:3-x/2";
    const g = field("x^2 + y", ["x", "y"]);
    const a = exact(g.integral(text));
    expect(a.low.toString()).toBe("85/3");
    const b = exact(g.integral(MultiRegion.parse(text, { variables: ["x", "y"] })));
    expect(b.low.toString()).toBe("85/3");
  });
  test("smooth integrands are enclosed to the digits asked", () => {
    const r = exact(field("x^2*y + sin(x*y)", ["x", "y"]).integral({ x: [0, 1], y: [0, 1] }));
    expect(holds(r, 0.40647838067)).toBe(true);
    expect(width(r)).toBeLessThan(2e-6);
    const g = exact(field("exp(-x^2-y^2)", ["x", "y"]).integral({ x: [-2, 2], y: [-2, 2] }, { digits: 4 }));
    expect(holds(g, 3.1122703125608)).toBe(true);
    expect(width(g)).toBeLessThan(1e-3);
  });
  test("the area of a disc, with square-root sides", () => {
    const r = field("1", ["x", "y"]).integral({ x: [-1, 1], y: ["-sqrt(1-x^2)", "sqrt(1-x^2)"] }, { digits: 4 });
    expect(r.quick.trust).toBe("rough");
    const a = exact(r);
    expect(holds(a, Math.PI)).toBe(true);
    expect(width(a)).toBeLessThan(1e-3);
  });
  test("parameters and progress", () => {
    const g = field("a*x*y", ["x", "y"], { params: { a: 3 } });
    expect(exact(g.integral({ x: [0, 1], y: [0, 2] })).low.toString()).toBe("3");
    expect(exact(g.with({ a: 1 }).integral({ x: [0, 1], y: [0, 2] })).low.toString()).toBe("1");
    expect(g.integral({ x: [0, 1], y: [0, 2] }).quick.value).toBeCloseTo(3, 10);
  });
  test("overlapping alternatives are refused", () => {
    expect(() => field("1", ["x", "y"]).integral("(0:x:1 && 0:y:1) || (0:x:2 && 0:y:1/2)")).toThrow();
  });
});

describe("ranges", () => {
  test("over a box and over a triangle", () => {
    const r = exact(field("x^2*y + sin(x*y)", ["x", "y"]).range({ x: [0, 1], y: [0, 1] }));
    expect(num(r.low)).toBeLessThanOrEqual(0);
    expect(num(r.low)).toBeGreaterThan(-1e-5);
    expect(holds({ low: r.high, high: r.high }, 1 + Math.sin(1), 1e-5)).toBe(true);
    const t = exact(field("x^2 - y^2 + x*y", ["x", "y"]).range("0:x:1 && 0:y:x"));
    expect(Math.abs(num(t.low))).toBeLessThan(1e-5);
    expect(Math.abs(num(t.high) - 1.25)).toBeLessThan(1e-5);
    expect(num(t.high)).toBeGreaterThanOrEqual(1.25);
  });
});

describe("critical points", () => {
  const kinds = (records) => records.map((r) => `${r.kind} ${r.point.map((p) => num(p.low).toFixed(3)).join(",")}`.replace(/-0\.000/g, "0.000"));
  test("a saddle and a minimum", () => {
    const r = exact(field("x^3 - 3x + y^2", ["x", "y"]).criticalPoints({ x: [-2, 2], y: [-2, 2] }));
    expect(kinds(r)).toEqual(["saddle -1.000,0.000", "min 1.000,0.000"]);
    expect(r.every((p) => p.unique)).toBe(true);
    expect(holds(r[1].value, -2, 1e-12)).toBe(true);
  });
  test("a saddle whose Hessian has a zero diagonal", () => {
    const r = exact(field("x^4 + y^4 - 4x*y + 1", ["x", "y"]).criticalPoints({ x: [-2, 2], y: [-2, 2] }));
    expect(r.map((p) => p.kind)).toEqual(["min", "saddle", "min"]);
  });
  test("three variables", () => {
    const r = exact(field("x^2 + y^2 - z^2 + x*y", ["x", "y", "z"]).criticalPoints({ x: [-1, 1], y: [-1, 1], z: [-1, 1] }));
    expect(r.length).toBe(1);
    expect(r[0].kind).toBe("saddle");
  });
  test("a curve of critical points is one undecided record", () => {
    const r = exact(field("x^2*y^2", ["x", "y"]).criticalPoints({ x: [-1, 1], y: [-1, 1] }, { maxBoxes: 200 }));
    expect(r.length).toBe(1);
    expect(r[0].kind).toBe("possible");
    expect(r[0].unique).toBe(false);
  });
  test("the preview finds the same points", () => {
    const q = field("x^3 - 3x + y^2", ["x", "y"]).criticalPoints({ x: [-2, 2], y: [-2, 2] }).quick;
    expect(q.value.length).toBe(2);
  });
});

describe("vector calculus", () => {
  test("divergence, curl, Jacobian", () => {
    expect(String(divergence(["x*y", "y*z", "z*x"], ["x", "y", "z"]))).toBe("y + z + x");
    expect(curl(["-y", "x", "0"], ["x", "y", "z"]).map(String)).toEqual(["0", "0", "2"]);
    expect(String(curl(["-y", "x"], ["x", "y"]))).toBe("2");
    expect(jacobian(["x*y", "x + y"], ["x", "y"]).map((row) => row.map(String))).toEqual([["y", "x"], ["1", "1"]]);
  });
  test("work around the unit circle", () => {
    const w = exact(lineIntegral(["-y", "x"], ["x", "y"], { x: "cos(t)", y: "sin(t)" }, [0, 1]));
    expect(holds(w, 1, 1e-12)).toBe(true);
    const len = exact(lineIntegral("1", ["x", "y"], { x: "3t", y: "4t" }, [0, 1]));
    expect(holds(len, 5, 1e-12)).toBe(true);
  });
  test("flux through a flat patch and the area of a cylinder", () => {
    const flux = exact(surfaceIntegral(["0", "0", "z + x"], ["x", "y", "z"], { x: "u", y: "w", z: "1" }, ["u", "w"], { u: [0, 1], w: [0, 2] }));
    expect(flux.low.toString()).toBe("3");
    const area = exact(surfaceIntegral("1", ["x", "y", "z"], { x: "cos(u)", y: "sin(u)", z: "w" }, ["u", "w"], { u: [0, 1], w: [0, 2] }, { digits: 4 }));
    expect(holds(area, 2)).toBe(true);
    expect(width(area)).toBeLessThan(1e-3);
  });
});
