import { describe, test, expect } from "bun:test";
import { greens, stokes, divergenceTheorem, changeOfVariables, potential, lagrange } from "../index.js";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 0) => num(iv.low) <= x + slack && num(iv.high) >= x - slack;

describe("Green's theorem", () => {
  test("both sides enclosed on a square, a triangle and a curved region", () => {
    const sq = greens(["-y^3", "x^3"], ["x", "y"], { x: [0, 1], y: [0, 1] });
    expect(sq.agree).toBe(true);
    expect(holds(sq.left.value, 2) && holds(sq.right.value, 2)).toBe(true);
    expect(sq.left.pieces.length).toBe(4);
    const tri = greens(["x*y", "x^2"], ["x", "y"], { x: [0, 1], y: [0, "x"] });
    expect(tri.agree).toBe(true);
    expect(tri.left.pieces.length).toBe(3); // the side x = 0 has no length
    expect(holds(tri.right.value, 1 / 3, 1e-12)).toBe(true);
    const curved = greens(["exp(x)*y", "sin(x) + x*y"], ["x", "y"], { x: [0, 1], y: ["x^2", "x"] }, { digits: 6 });
    expect(curved.agree).toBe(true);
    expect(curved.overlap).not.toBe(null);
  });
  test("area by a line integral, and the flux form", () => {
    const area = greens(["-y/2", "x/2"], ["x", "y"], { x: [0, 1], y: [0, "1 - x"] });
    expect(holds(area.left.value, 1 / 2, 1e-12)).toBe(true);
    const flux = greens(["x^2", "y^2"], ["x", "y"], { x: [0, 1], y: [0, 2] }, { flux: true });
    expect(flux.agree).toBe(true);
    expect(holds(flux.right.value, 6, 1e-12)).toBe(true);
  });
});

describe("Stokes and the divergence theorem", () => {
  test("Stokes on a graph and on a paraboloid in polar parameters", () => {
    const a = stokes(["-y", "x", "z"], ["x", "y", "z"], { x: "u", y: "v", z: "1 - u^2 - v^2" }, ["u", "v"], { u: [-1, 1], v: [-1, 1] });
    expect(a.agree).toBe(true);
    expect(holds(a.right.value, 8, 1e-9)).toBe(true);
    const b = stokes(["z", "x", "y"], ["x", "y", "z"], { x: "u*cos(v)", y: "u*sin(v)", z: "u^2" }, ["u", "v"], { u: [0, 1], v: [0, "2*pi"] }, { digits: 5 });
    expect(b.agree).toBe(true);
    expect(holds(b.left.value, Math.PI, 1e-6)).toBe(true);
  });
  test("the divergence theorem on a box, a tetrahedron and under a paraboloid", () => {
    const box = divergenceTheorem(["x*y", "y*z", "z*x"], ["x", "y", "z"], { x: [0, 1], y: [0, 2], z: [0, 3] });
    expect(box.agree).toBe(true);
    expect(holds(box.left.value, 18, 1e-9)).toBe(true);
    expect(box.left.pieces.length).toBe(6);
    const tet = divergenceTheorem(["x", "y^2", "z"], ["x", "y", "z"], { x: [0, 1], y: [0, "1 - x"], z: [0, "1 - x - y"] }, { digits: 4 });
    expect(tet.agree).toBe(true);
    expect(holds(tet.right.value, 5 / 12, 1e-6)).toBe(true);
    const par = divergenceTheorem(["x", "y", "z^2"], ["x", "y", "z"], { x: [-1, 1], y: [-1, 1], z: [0, "2 - x^2 - y^2"] }, { digits: 4 });
    expect(par.agree).toBe(true);
  });
});

describe("change of variables", () => {
  test("polar coordinates show the factor r", () => {
    const r = changeOfVariables("x^2 + y^2", ["x", "y"], { x: "r*cos(t)", y: "r*sin(t)" }, ["r", "t"], { r: [0, 1], t: [0, "2*pi"] });
    expect(r.determinant).toBe("r");
    expect(r.integrand).toBe("r^3");
    expect(holds(r.value, Math.PI / 2, 1e-9)).toBe(true);
  });
  test("a negative determinant is used by its size, and the direct integral agrees", () => {
    const lin = changeOfVariables("x + y", ["x", "y"], { x: "u + v", y: "u - v" }, ["u", "v"], { u: [0, 1], v: [0, 1] });
    expect(lin.determinant).toBe("-2");
    expect(lin.factor).toBe("2");
    const sc = changeOfVariables("x + y", ["x", "y"], { x: "2*u", y: "3*v" }, ["u", "v"], { u: [0, 1], v: [0, 1] }, { original: { x: [0, 2], y: [0, 3] } });
    expect(sc.agree).toBe(true);
    expect(holds(sc.value, 15)).toBe(true);
  });
});

describe("potentials and Lagrange multipliers", () => {
  test("a polynomial gradient field has its potential found and checked", () => {
    const p = potential(["2*x*y + z", "x^2", "x + 3*z^2"], ["x", "y", "z"]);
    expect(p.conservative).toBe(true);
    expect(String(p.potential)).toBe("x^2*y + x*z + z^3");
    expect(p.check).toEqual(["0", "0", "0"]);
    expect(holds(p.value([1, 2, 3]), 32, 1e-9)).toBe(true);
  });
  test("a rotation is proven not to be a gradient", () => {
    const p = potential(["-y", "x"], ["x", "y"]);
    expect(p.conservative).toBe(false);
    expect(p.witness.curl.low.toNumber()).toBe(2);
    expect(p.potential).toBe(null);
  });
  test("a field with sines is recognised and its potential evaluated", () => {
    const p = potential(["y*cos(x*y)", "x*cos(x*y)"], ["x", "y"]);
    expect(p.conservative).toBe(true);
    expect(holds(p.value([1, 2]), Math.sin(2), 1e-9)).toBe(true);
  });
  test("Lagrange candidates are certified", () => {
    const r = lagrange("x*y", "x^2 + y^2 - 1", ["x", "y"], { x: [-2, 2], y: [-2, 2] });
    expect(r.candidates.length).toBe(4);
    expect(r.complete).toBe(true);
    expect(holds(r.max.value, 1 / 2, 1e-9)).toBe(true);
    expect(holds(r.min.value, -1 / 2, 1e-9)).toBe(true);
    expect(r.max.at.length).toBe(2);
    const s = lagrange("x + 2*y", "x^2 + 4*y^2 - 8", ["x", "y"], { x: [-4, 4], y: [-4, 4] });
    expect(holds(s.max.value, 4, 1e-9)).toBe(true);
    expect(holds(s.max.at[0].x, 2, 1e-9)).toBe(true);
  });
});
