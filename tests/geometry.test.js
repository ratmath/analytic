import { describe, test, expect } from "bun:test";
import { curve, surface, metric, tidy, parse, format } from "../index.js";
import { Surface } from "@ratmath/analytic/geometry";

const num = (x) => x.toNumber();
const holds = (iv, x, slack = 1e-9) => num(iv.low) <= x + slack && num(iv.high) >= x - slack && num(iv.high) - num(iv.low) < 1e-4;

describe("tidy", () => {
  test("a normal form for quotients of polynomials in letters and calls", () => {
    const t = (s) => format(tidy(parse(s)));
    expect(t("sin(u)^2*sin(v)^2 + cos(u)^2*sin(v)^2")).toBe("sin(v)^2");
    expect(t("(x^2 - 1)/(x - 1)")).toBe("x + 1");
    expect(t("sqrt(1 + u^2)^3/(1 + u^2)")).toBe("sqrt(u^2 + 1)");
    expect(t("(x + y)^3/(x^2 + 2*x*y + y^2)")).toBe("x + y");
    expect(t("sqrt(4*x^2)")).toBe("2*abs(x)");
    expect(t("1/(2*x) - 1/(2*x)")).toBe("0");
    expect(t("cosh(x)^2 - sinh(x)^2")).toBe("1");
    expect(t("2^x")).toBe("2^x");
  });
});

describe("curves", () => {
  test("a helix has constant curvature and torsion", () => {
    const h = curve(["cos(t)", "sin(t)", "t/2"], "t");
    expect(h.curvature()).toBe("4/5");
    expect(h.torsion()).toBe("2/5");
    expect(holds(h.length([0, "2*pi"]), Math.PI * Math.sqrt(5))).toBe(true);
    const a = h.at(1);
    expect(holds(a.curvature, 0.8) && holds(a.torsion, 0.4)).toBe(true);
    expect(holds(a.binormal[2], 2 / Math.sqrt(5))).toBe(true);
    expect(holds(a.centre[2], 0.5)).toBe(true);
    expect(holds(a.radius, 1.25)).toBe(true);
  });
  test("a parabola: signed curvature, osculating circle, evolute", () => {
    const p = curve(["t", "t^2"], "t");
    const a = p.at(0);
    expect(holds(a.curvature, 2) && holds(a.radius, 0.5)).toBe(true);
    expect(a.centre.map((c) => num(c.low))).toEqual([0, 0.5]);
    expect(p.evolute().position).toEqual(["-4*t^3", "3*t^2 + 1/2"]);
    expect(num(curve(["t", "-t^2"], "t").at(0).curvature.low)).toBe(-2);
  });
  test("total curvature of an ellipse is 2π; a line has no circle", () => {
    expect(holds(curve(["2*cos(t)", "sin(t)"]).totalCurvature([0, "2*pi"]), 2 * Math.PI)).toBe(true);
    const line = curve(["t", "2*t"]).at(1);
    expect(line.radius).toBe(null);
    expect(() => curve(["t^2", "t^3"]).at(0)).toThrow();
    expect(() => curve(["t"])).toThrow();
    expect(() => curve(["t", "a*t"])).toThrow();
    expect(holds(curve(["t", "a*t^2"], "t", { params: { a: 3 } }).at(0).curvature, 6)).toBe(true);
  });
});

describe("surfaces", () => {
  const sphere = surface(["cos(u)*sin(v)", "sin(u)*sin(v)", "cos(v)"], ["u", "v"]);
  test("the sphere: forms, curvatures, Christoffel symbols", () => {
    expect(sphere).toBeInstanceOf(Surface);
    expect(sphere.first()).toEqual({ E: "sin(v)^2", F: "0", G: "1" });
    expect(sphere.gaussian()).toBe("1");
    expect(sphere.intrinsicGaussian()).toBe("1");
    expect(sphere.christoffel().u_uv).toBe("cos(v)/sin(v)");
    expect(sphere.christoffel().v_uu).toBe("-(sin(v)*cos(v))");
    const a = sphere.at(1, 1);
    expect(a.kind).toBe("elliptic");
    expect(holds(a.gaussian, 1) && holds(a.mean, 1)).toBe(true);
    expect(holds(sphere.area({ u: [0, 1], v: [1, 2] }), Math.cos(1) - Math.cos(2), 1e-7)).toBe(true);
    expect(() => sphere.at(0, 0)).toThrow();
  });
  test("saddle, cylinder, plane and torus are classified", () => {
    const saddle = surface(["u", "v", "u^2 - v^2"]).at(0, 0);
    expect(saddle.kind).toBe("hyperbolic");
    expect(saddle.principal.map((k) => num(k.low))).toEqual([-2, 2]);
    expect(surface(["cos(u)", "sin(u)", "v"]).at(0, 0).kind).toBe("parabolic");
    expect(surface(["u", "v", "u + v"]).at(0, 0).kind).toBe("planar");
    const torus = surface(["(2 + cos(v))*cos(u)", "(2 + cos(v))*sin(u)", "sin(v)"]);
    expect(torus.gaussian()).toBe("cos(v)/(cos(v) + 2)");
    expect(torus.at(0, 0).kind).toBe("elliptic");
    expect(torus.at(0, "pi").kind).toBe("hyperbolic");
  });
  test("Gauss-Bonnet on patches of a sphere, a torus and the hyperbolic plane", () => {
    const g = sphere.gaussBonnet({ u: [0, 1], v: [1, 2] });
    expect(g.agree).toBe(true);
    expect(g.boundary.pieces.length).toBe(4);
    expect(holds(g.total, 2 * Math.PI, 1e-6)).toBe(true);
    const hyp = metric({ E: "1/v^2", F: 0, G: "1/v^2" }, ["u", "v"]);
    expect(hyp.gaussian()).toBe("-1");
    const h = hyp.gaussBonnet({ u: [0, 1], v: [1, "2 + u"] });
    expect(h.agree).toBe(true);
    expect(num(h.curvature.value.high)).toBeLessThan(0);
  });
  test("geodesic curvature, transport around a latitude, geodesics", () => {
    expect(holds(sphere.geodesicCurvature({ u: "t", v: "pi/2" }, 0), 0)).toBe(true); // the equator is a geodesic
    expect(holds(sphere.geodesicCurvature({ u: "t", v: "1" }, 0), -Math.cos(1) / Math.sin(1))).toBe(true);
    const r = sphere.transport({ u: "2*pi*t", v: "1" }, [0, 1], [0, 1]);
    expect(holds(r.angle, 2 * Math.PI * (1 - Math.cos(1)), 1e-6)).toBe(true);
    expect(holds(r.lengthAfter, 1, 1e-6)).toBe(true);
    const hyp = metric({ E: "1/v^2", F: 0, G: "1/v^2" }, ["u", "v"]);
    const geo = hyp.geodesic({ from: [0, 1], direction: [1, 0], until: "1/4" });
    // unit speed from (0, 1) heading right: u = tanh s, v = sech s
    expect(Math.abs(geo.quick.value.y[0].at(-1) - Math.tanh(0.25))).toBeLessThan(1e-8);
    const sol = geo.exact();
    expect(sol.complete).toBe(true);
    expect(holds(sol.final[0], Math.tanh(0.25), 1e-6) && holds(sol.final[1], 1 / Math.cosh(0.25), 1e-6)).toBe(true);
  });
});
