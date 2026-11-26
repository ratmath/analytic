// Differential geometry of curves and surfaces.
//
// A curve is a list of formulas in one parameter, a surface a list of three
// formulas in two. Everything a first course computes comes out twice: as a
// formula, by differentiating the description, and as a certified enclosure
// at a point, by evaluating that formula in interval arithmetic. Lengths and
// areas are certified integrals. Geodesics and parallel transport are
// validated solutions of their differential equations, and the Gauss-Bonnet
// theorem is a checked statement: the three terms are enclosed separately and
// their sum must contain 2π.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, toQ, roundDyadic } from "./rat.js";
import { toAst, format, derivative, simplify, freeVariables, constantRational, num, v as variable, op, call, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { quad1 } from "./quad.js";
import { ScalarField } from "./multi.js";
import { solve as odeSolve } from "./ode.js";
import { tidy, vanishesIdentically } from "./tidy.js";

const A = (x) => (typeof x === "number" ? num(toRational(x)) : typeof x === "bigint" || x instanceof Rational ? num(toQ(x)) : toAst(x));
const subst = (ast, map) => {
  if (ast.type === "var") return map[ast.name] ?? ast;
  if (ast.args) return { ...ast, args: ast.args.map((a) => subst(a, map)) };
  return ast;
};
const D = (ast, name) => tidy(derivative(ast, name));
const add = (a, b) => op("+", a, b);
const sub = (a, b) => op("-", a, b);
const mul = (a, b) => op("*", a, b);
const div = (a, b) => op("/", a, b);
const pow = (a, n) => op("^", a, num(n));
const sqrt = (a) => call("sqrt", a);
const neg = (a) => op("neg", a);
const S = tidy;
const sum = (list) => list.reduce(add);
const dot = (a, b) => S(sum(a.map((x, i) => mul(x, b[i]))));
const cross = (a, b) => [sub(mul(a[1], b[2]), mul(a[2], b[1])), sub(mul(a[2], b[0]), mul(a[0], b[2])), sub(mul(a[0], b[1]), mul(a[1], b[0]))].map(S);
const isZero = vanishesIdentically;
const bitsOf = (opts) => bitsForDigits(opts?.digits ?? 15) + 16;
const tolOf = (digits) => new Rational(1n, 10n ** BigInt(digits));
/** a point given as a number, a Rational, an interval or a constant formula such as "pi/4" */
const pointIv = (x, bits) => {
  if (x instanceof Iv) return x;
  if (x instanceof RationalInterval) return Iv.from(x);
  if (typeof x === "string") {
    const ast = toAst(x);
    const c = constantRational(ast);
    return c !== null ? Iv.point(c) : encloseAst(ast, {}, bits);
  }
  return Iv.point(typeof x === "number" ? toRational(x) : toQ(x));
};
const out = (iv) => iv.toRationalInterval();
const evalAt = (ast, env, bits) => {
  try {
    return encloseAst(ast, env, bits);
  } catch (err) {
    refuse("not-regular", `the formula ${format(ast)} has no value there: ${err.message}`);
  }
};
const ivSqrt = (iv, bits) => encloseAst(sqrt(variable("s_")), { s_: iv }, bits);
const sign = (iv) => (iv.lo.numerator > 0n ? 1 : iv.hi.numerator < 0n ? -1 : iv.lo.numerator === 0n && iv.hi.numerator === 0n ? 0 : null);

// ---------------------------------------------------------------- curves

/**
 * A parametrised curve in the plane or in space.
 *
 *     curve(["cos(t)", "sin(t)", "t/2"], "t")
 */
export class Curve {
  constructor(components, parameter = "t", opts = {}) {
    if (!Array.isArray(components) || (components.length !== 2 && components.length !== 3)) refuse("bad-dimension", "a curve needs two or three component formulas");
    this.parameter = parameter;
    this.params = opts.params ?? {};
    this.r = components.map(A);
    for (const c of this.r) for (const name of freeVariables(c)) if (name !== parameter && !(name in this.params)) refuse("unbound", `${name} has no value: pass it in params`);
    this.dimension = this.r.length;
    this.d1 = this.r.map((c) => D(c, parameter));
    this.d2 = this.d1.map((c) => D(c, parameter));
    this.d3 = this.d2.map((c) => D(c, parameter));
    this.speed2 = dot(this.d1, this.d1);
  }
  #env(t, bits) {
    const env = { [this.parameter]: pointIv(t, bits) };
    for (const [k, val] of Object.entries(this.params)) env[k] = pointIv(val, bits);
    return env;
  }
  /** the formulas of position, velocity and acceleration */
  get position() { return this.r.map(format); }
  get velocity() { return this.d1.map(format); }
  get acceleration() { return this.d2.map(format); }
  /** |r′(t)| as a formula */
  speed() { return format(S(sqrt(this.speed2))); }
  /** the numerator whose size gives the curvature: x′y″ − y′x″, or r′ × r″ */
  #turn() {
    if (this.dimension === 2) return S(sub(mul(this.d1[0], this.d2[1]), mul(this.d1[1], this.d2[0])));
    return cross(this.d1, this.d2);
  }
  /** Curvature as a formula: signed for a plane curve (positive turning left). */
  curvatureAst() {
    const w = this.#turn();
    const denom = op("^", this.speed2, num(new Rational(3n, 2n)));
    return S(this.dimension === 2 ? div(w, denom) : div(sqrt(dot(w, w)), denom));
  }
  curvature() { return format(this.curvatureAst()); }
  /** Torsion of a space curve as a formula: (r′ × r″)·r‴ / |r′ × r″|². */
  torsionAst() {
    if (this.dimension !== 3) refuse("bad-dimension", "torsion belongs to curves in space");
    const w = this.#turn();
    return S(div(dot(w, this.d3), dot(w, w)));
  }
  torsion() { return format(this.torsionAst()); }
  /** The evolute of a plane curve, the path of its centres of curvature, as a new Curve. */
  evolute() {
    if (this.dimension !== 2) refuse("bad-dimension", "the evolute here is for plane curves");
    const w = this.#turn();
    const k = div(this.speed2, w);
    return new Curve([S(sub(this.r[0], mul(this.d1[1], k))), S(add(this.r[1], mul(this.d1[0], k)))].map(format), this.parameter, { params: this.params });
  }
  /** Arc length over [a, b]: a certified integral of the speed. */
  length([a, b], opts = {}) {
    const digits = opts.digits ?? 12;
    const bits = bitsForDigits(digits) + 24;
    const env = this.#env(0, bits);
    delete env[this.parameter];
    const lo = pointIv(a, bits);
    const hi = pointIv(b, bits);
    if (!lo.isPoint || !hi.isPoint) {
      // irrational ends such as 2π: rescale to [0, 1]
      const s = variable("s_");
      const map = S(add(A(a), mul(sub(A(b), A(a)), s)));
      const inner = S(mul(sqrt(subst(this.speed2, { [this.parameter]: map })), sub(A(b), A(a))));
      return out(quad1(inner, "s_", env, ZERO, ONE, { tol: tolOf(digits), bits }).iv);
    }
    return out(quad1(S(sqrt(this.speed2)), this.parameter, env, lo.lo, hi.lo, { tol: tolOf(digits), bits }).iv);
  }
  /** The integral of the curvature against arc length over [a, b] (rational ends). */
  totalCurvature([a, b], opts = {}) {
    const digits = opts.digits ?? 10;
    const bits = bitsForDigits(digits) + 24;
    const env = this.#env(0, bits);
    delete env[this.parameter];
    const s = variable("s_");
    const map = S(add(A(a), mul(sub(A(b), A(a)), s)));
    const integrand = S(mul(subst(S(mul(this.curvatureAst(), sqrt(this.speed2))), { [this.parameter]: map }), sub(A(b), A(a))));
    return out(quad1(integrand, "s_", env, ZERO, ONE, { tol: tolOf(digits), bits }).iv);
  }
  /**
   * Everything at one parameter value, each number a RationalInterval:
   * { point, velocity, speed, tangent, normal, binormal?, curvature, torsion?,
   *   radius, centre } where radius and centre describe the osculating circle
   * (null where the curvature may vanish).
   */
  at(t, opts = {}) {
    const bits = bitsOf(opts);
    const env = this.#env(t, bits);
    const ev = (ast) => evalAt(ast, env, bits);
    const p = this.r.map(ev);
    const v1 = this.d1.map(ev);
    const v2 = this.d2.map(ev);
    const s2 = v1.map((c) => c.mul(c)).reduce((x, y) => x.add(y));
    if (sign(s2) !== 1) refuse("not-regular", "the velocity may vanish there, so the curve has no certain tangent");
    const speed = ivSqrt(s2, bits);
    const T = v1.map((c) => c.div(speed));
    const res = { point: p.map(out), velocity: v1.map(out), speed: out(speed), tangent: T.map(out) };
    let kappa;
    let N;
    if (this.dimension === 2) {
      const w = v1[0].mul(v2[1]).sub(v1[1].mul(v2[0]));
      kappa = w.div(speed.mul(s2));
      N = [T[1].neg(), T[0]];
      res.normal = N.map(out);
    } else {
      const w = [v1[1].mul(v2[2]).sub(v1[2].mul(v2[1])), v1[2].mul(v2[0]).sub(v1[0].mul(v2[2])), v1[0].mul(v2[1]).sub(v1[1].mul(v2[0]))];
      const w2 = w.map((c) => c.mul(c)).reduce((x, y) => x.add(y));
      const wn = sign(w2) === 1 ? ivSqrt(w2, bits) : null;
      kappa = wn ? wn.div(speed.mul(s2)) : Iv.from(new RationalInterval(ZERO, ivSqrt(Iv.point(w2.hi), bits).div(speed.mul(s2)).hi));
      if (wn) {
        const B = w.map((c) => c.div(wn));
        N = [B[1].mul(T[2]).sub(B[2].mul(T[1])), B[2].mul(T[0]).sub(B[0].mul(T[2])), B[0].mul(T[1]).sub(B[1].mul(T[0]))];
        const v3 = this.d3.map(ev);
        res.normal = N.map(out);
        res.binormal = B.map(out);
        res.torsion = out(w.map((c, i) => c.mul(v3[i])).reduce((x, y) => x.add(y)).div(w2));
      } else {
        res.normal = null;
        res.binormal = null;
        res.torsion = null;
      }
    }
    res.curvature = out(kappa);
    const ks = sign(kappa);
    if (ks === 1 || ks === -1) {
      const rho = Iv.point(ONE).div(kappa);
      res.radius = out(ks === 1 ? rho : rho.neg());
      res.centre = N ? p.map((c, i) => out(c.add(N[i].mul(rho)))) : null;
    } else {
      res.radius = null;
      res.centre = null;
    }
    return res;
  }
}

export function curve(components, parameter, opts) {
  return new Curve(components, parameter, opts);
}

// ---------------------------------------------------------------- metrics

const T_ = variable("t");
const along = (from, to) => S(add(from, mul(sub(to, from), T_)));

/**
 * A metric E du² + 2F du dv + G dv² on a patch of the (u, v) plane: the
 * intrinsic geometry of a surface, with or without a surface behind it.
 *
 *     metric({ E: "1/v^2", F: 0, G: "1/v^2" }, ["u", "v"])   // the hyperbolic half-plane
 */
export class Metric {
  constructor(g, parameters = ["u", "v"], opts = {}) {
    if (parameters.length !== 2) refuse("bad-dimension", "a surface has two parameters");
    this.parameters = parameters;
    this.params = opts.params ?? {};
    this.E = S(A(g.E));
    this.F = S(A(g.F ?? 0));
    this.G = S(A(g.G));
    this.det = S(sub(mul(this.E, this.G), mul(this.F, this.F)));
    this._gamma = null;
    this._K = null;
  }
  _env(point, bits) {
    const env = {};
    this.parameters.forEach((name, i) => (env[name] = pointIv(point[i], bits)));
    for (const [k, val] of Object.entries(this.params)) env[k] = pointIv(val, bits);
    return env;
  }
  /** { E, F, G } as formulas */
  first() { return { E: format(this.E), F: format(this.F), G: format(this.G) }; }
  /** Christoffel symbols as formula trees: gamma[k][i][j] = Γᵏᵢⱼ. */
  christoffelAst() {
    if (this._gamma) return this._gamma;
    const g = [[this.E, this.F], [this.F, this.G]];
    const inv = [[div(this.G, this.det), neg(div(this.F, this.det))], [neg(div(this.F, this.det)), div(this.E, this.det)]];
    const dg = (i, j, k) => D(g[i][j], this.parameters[k]);
    const gamma = [0, 1].map((k) => [0, 1].map((i) => [0, 1].map((j) => S(mul(num(new Rational(1n, 2n)), sum([0, 1].map((l) => mul(inv[k][l], sub(add(dg(l, i, j), dg(l, j, i)), dg(i, j, l))))))))));
    return (this._gamma = gamma);
  }
  /** Christoffel symbols as formulas, keyed "u_uv" for Γᵘ_uv and so on. */
  christoffel() {
    const gamma = this.christoffelAst();
    const [u, v] = this.parameters;
    const names = [u, v];
    const res = {};
    for (const k of [0, 1]) for (const i of [0, 1]) for (const j of [i, 1]) res[`${names[k]}_${names[i]}${names[j]}`] = format(gamma[k][i][j]);
    return res;
  }
  /** Gaussian curvature from the metric alone (the Theorema Egregium), as a formula tree. */
  gaussianAst() {
    if (this._K) return this._K;
    const G = this.christoffelAst();
    const [u, v] = this.parameters;
    const g = [this.E, this.F];
    // R^l_{212} = ∂u Γ^l_22 − ∂v Γ^l_21 + Γ^l_1m Γ^m_22 − Γ^l_2m Γ^m_21, K = g_1l R^l_212 / det g
    const Rl = [0, 1].map((l) => sum([D(G[l][1][1], u), neg(D(G[l][1][0], v)), ...[0, 1].map((m) => sub(mul(G[l][0][m], G[m][1][1]), mul(G[l][1][m], G[m][1][0])))]));
    return (this._K = S(div(add(mul(g[0], Rl[0]), mul(g[1], Rl[1])), this.det)));
  }
  gaussian() { return format(this.gaussianAst()); }
  /** Area of a region { u: [a, b], v: [lo(u), hi(u)] }: the integral of √(EG − F²). */
  area(region, opts = {}) {
    return new ScalarField(S(sqrt(this.det)), this.parameters).integral(region, { digits: opts.digits ?? 8 }).exact();
  }
  /** The integral of the Gaussian curvature over a region. */
  totalCurvature(region, opts = {}) {
    const integrand = S(mul(this.gaussianAst(), sqrt(this.det)));
    if (isZero(integrand)) return new RationalInterval(ZERO, ZERO);
    return new ScalarField(integrand, this.parameters).integral(region, { digits: opts.digits ?? 8 }).exact();
  }
  #velocityNames() {
    const [u, v] = this.parameters;
    return [`d${u}_`, `d${v}_`];
  }
  /**
   * The geodesic from a point in a direction, as a validated solution of
   *     u″ = −Γᵘᵢⱼ uⁱ′ uʲ′,   v″ = −Γᵛᵢⱼ uⁱ′ uʲ′.
   * Returns a Refinement like ode.solve: `.quick` samples, `.exact()` an
   * ODESolution whose `.at(s)` is [u, v, u′, v′] as enclosures (seconds per
   * unit of length: the preview is immediate). With
   * { unit: true } the direction is scaled to unit speed first, so the
   * parameter is arc length.
   */
  geodesic({ from, direction, until, unit = false, ...rest }) {
    const G = this.christoffelAst();
    const [u, v] = this.parameters;
    const [p, q] = this.#velocityNames();
    const vel = [variable(p), variable(q)];
    const rhs = [0, 1].map((k) => S(neg(sum([0, 1].flatMap((i) => [0, 1].map((j) => mul(G[k][i][j], mul(vel[i], vel[j]))))))));
    let dir = direction.map((x) => pointIv(x, 96));
    if (unit) {
      const env = this._env(from, 96);
      const [E, F, Gv] = [this.E, this.F, this.G].map((a) => evalAt(a, env, 96));
      const n2 = E.mul(dir[0]).mul(dir[0]).add(F.mul(dir[0]).mul(dir[1]).scale(new Rational(2n))).add(Gv.mul(dir[1]).mul(dir[1]));
      const n = ivSqrt(n2, 96);
      // rounded to a nearby exact direction: unit speed to about 24 digits
      dir = dir.map((c) => Iv.point(roundDyadic(c.div(n).mid, 80)));
    }
    const y0 = [...from.map((x) => pointIv(x, 96)), ...dir].map((iv) => (iv.isPoint ? iv.lo : iv.toRationalInterval()));
    // certified steps of this system are slow, so the defaults are modest; ask for more with order, tol, track
    const points = y0.every((x) => x instanceof Rational);
    return odeSolve({ f: [format(vel[0]), format(vel[1]), ...rhs.map(format)], vars: [u, v, p, q], y0, time: "s_", until, params: this.params, order: 6, tol: "1e-6", bits: 64, track: !points, ...rest });
  }
  /** g(a, b) at a point, for tangent vectors given by their (u, v) components (Iv). */
  #inner(env, a, b, bits) {
    const [E, F, G] = [this.E, this.F, this.G].map((x) => evalAt(x, env, bits));
    return E.mul(a[0]).mul(b[0]).add(F.mul(a[0].mul(b[1]).add(a[1].mul(b[0])))).add(G.mul(a[1]).mul(b[1]));
  }
  /**
   * Parallel transport of a tangent vector along the curve (u(t), v(t)),
   * t in [a, b] (rational): the validated solution of
   *     Vᵏ′ = −Γᵏᵢⱼ cⁱ′ Vʲ.
   * Returns { vector, start, angle, length } where `vector` is the result
   * at b, and `angle` the unsigned angle between the transported vector and
   * the starting one measured in the metric at the two ends (meaningful for
   * a closed curve, where it is the holonomy).
   */
  transport(path, [a, b], vector, opts = {}) {
    const G = this.christoffelAst();
    const [u, v] = this.parameters;
    const time = opts.parameter ?? "t";
    const c = [A(path[u]), A(path[v])];
    const dc = c.map((x) => D(x, time));
    const on = { [u]: c[0], [v]: c[1] };
    const names = ["V1_", "V2_"];
    const V = names.map(variable);
    const rhs = [0, 1].map((k) => S(neg(sum([0, 1].flatMap((i) => [0, 1].map((j) => mul(subst(G[k][i][j], on), mul(dc[i], V[j]))))))));
    const bits = 96;
    const v0 = vector.map((x) => pointIv(x, bits));
    const sol = odeSolve({ f: rhs.map(format), vars: names, y0: v0.map((iv) => (iv.isPoint ? iv.lo : iv.toRationalInterval())), time, t0: a, until: b, params: this.params, order: opts.order ?? 8, tol: opts.tol ?? "1e-8", step: opts.step }).exact();
    if (!sol.complete) refuse("no-enclosure", `transport stopped early: ${sol.reason ?? "no validated step"}`);
    const v1 = sol.final.map((x) => Iv.from(x));
    const envAt = (t) => {
      const tt = { [time]: pointIv(t, bits) };
      for (const [k, val] of Object.entries(this.params)) tt[k] = pointIv(val, bits);
      return this._env(c.map((x) => evalAt(x, tt, bits)), bits);
    };
    const e0 = envAt(a);
    const e1 = envAt(b);
    const l0 = ivSqrt(this.#inner(e0, v0, v0, bits), bits);
    const l1sq = this.#inner(e1, v1, v1, bits);
    const res = { start: v0.map(out), vector: v1.map(out), length: out(l0), lengthAfter: sign(l1sq) === 1 ? out(ivSqrt(l1sq, bits)) : null, solution: sol };
    // the angle only makes sense when the two ends are the same point
    try {
      const cosang = this.#inner(e1, v0, v1, bits).div(l0.mul(l0));
      const clamp = new Iv(cosang.lo.compareTo(ONE.negate()) < 0 ? ONE.negate() : cosang.lo, cosang.hi.compareTo(ONE) > 0 ? ONE : cosang.hi);
      res.angle = out(encloseAst(call("acos", variable("c_")), { c_: clamp }, bits));
    } catch {
      res.angle = null;
    }
    return res;
  }
  /** numerator of geodesic curvature × |c′|³ / √det, for the path (u(t), v(t)) */
  #bend(c, time) {
    const G = this.christoffelAst();
    const [u, v] = this.parameters;
    const on = { [u]: c[0], [v]: c[1] };
    const d1 = c.map((x) => D(x, time));
    const d2 = d1.map((x) => D(x, time));
    const acc = [0, 1].map((k) => add(d2[k], sum([0, 1].flatMap((i) => [0, 1].map((j) => mul(subst(G[k][i][j], on), mul(d1[i], d1[j])))))));
    const speed2 = S(sum([mul(subst(this.E, on), mul(d1[0], d1[0])), mul(num(2), mul(subst(this.F, on), mul(d1[0], d1[1]))), mul(subst(this.G, on), mul(d1[1], d1[1]))]));
    const numer = S(mul(sqrt(subst(this.det, on)), sub(mul(d1[0], acc[1]), mul(d1[1], acc[0]))));
    return { numer, speed2, d1 };
  }
  /** Geodesic curvature of the path { u: "...", v: "..." } in t, as a formula tree. */
  geodesicCurvatureAst(path, parameter = "t") {
    const [u, v] = this.parameters;
    const { numer, speed2 } = this.#bend([A(path[u]), A(path[v])], parameter);
    return S(div(numer, op("^", speed2, num(new Rational(3n, 2n)))));
  }
  /** Geodesic curvature of a path: a formula, or with a parameter value its enclosure there. */
  geodesicCurvature(path, t, opts = {}) {
    const time = opts.parameter ?? "t";
    const ast = this.geodesicCurvatureAst(path, time);
    if (t === undefined) return format(ast);
    const bits = bitsOf(opts);
    const env = { [time]: pointIv(t, bits) };
    for (const [k, val] of Object.entries(this.params)) env[k] = pointIv(val, bits);
    return out(evalAt(ast, env, bits));
  }
  /**
   * The Gauss-Bonnet theorem on the patch { u: [a, b], v: [lo(u), hi(u)] },
   * a curvilinear polygon with Euler characteristic 1:
   *
   *     ∬ K dA  +  ∮ k_g ds  +  Σ exterior angles  =  2π.
   *
   * Returns { statement, curvature, boundary: { value, pieces }, angles:
   * { value, corners }, total, expected, agree }. The patch must be regular
   * (EG − F² > 0) up to and including its boundary.
   */
  gaussBonnet(region, opts = {}) {
    const digits = opts.digits ?? 7;
    const bits = bitsForDigits(digits) + 32;
    const [u, v] = this.parameters;
    const bs = [u, v].map((name) => {
      const b = region[name];
      if (!Array.isArray(b) || b.length !== 2) refuse("bad-region", `the region needs ${name}: [low, high]`);
      return [A(b[0]), A(b[1])];
    });
    const [[a, b], [lo, hi]] = bs;
    const at = (g, x) => S(subst(g, { [u]: x }));
    const all = [];
    const bottomU = along(a, b);
    all.push({ name: `${v} = ${format(lo)}`, c: [bottomU, at(lo, bottomU)] });
    all.push({ name: `${u} = ${format(b)}`, c: [b, along(at(lo, b), at(hi, b))] });
    const topU = along(b, a);
    all.push({ name: `${v} = ${format(hi)}, backwards`, c: [topU, at(hi, topU)] });
    all.push({ name: `${u} = ${format(a)}, downwards`, c: [a, along(at(hi, a), at(lo, a))] });
    const sidesList = all.filter((s) => !(isZero(D(s.c[0], "t")) && isZero(D(s.c[1], "t"))));
    const penv = {};
    for (const [k, val] of Object.entries(this.params)) penv[k] = pointIv(val, bits);
    const tol = tolOf(digits + 1);
    const pieces = sidesList.map((s) => {
      const { numer, speed2, d1 } = this.#bend(s.c, "t");
      s.d1 = d1;
      const integrand = S(div(numer, speed2));
      const value = isZero(integrand) ? new RationalInterval(ZERO, ZERO) : out(quad1(integrand, "t", penv, ZERO, ONE, { tol, bits }).iv);
      return { side: s.name, path: { [u]: format(s.c[0]), [v]: format(s.c[1]) }, value };
    });
    const corners = sidesList.map((s, i) => {
      const next = sidesList[(i + 1) % sidesList.length];
      const end = (side, t) => {
        const env = { ...penv, t: Iv.point(t) };
        return { point: side.c.map((x) => evalAt(x, env, bits)), dir: side.d1.map((x) => evalAt(x, env, bits)) };
      };
      const e1 = end(s, ONE);
      const e2 = end(next, ZERO);
      const env = this._env(e1.point, bits);
      const cosang = this.#inner(env, e1.dir, e2.dir, bits).div(ivSqrt(this.#inner(env, e1.dir, e1.dir, bits).mul(this.#inner(env, e2.dir, e2.dir, bits)), bits));
      const clamp = new Iv(cosang.lo.compareTo(ONE.negate()) < 0 ? ONE.negate() : cosang.lo, cosang.hi.compareTo(ONE) > 0 ? ONE : cosang.hi);
      const exterior = encloseAst(call("acos", variable("c_")), { c_: clamp }, bits);
      return { at: e1.point.map(out), exterior: out(exterior) };
    });
    const fmt = Object.fromEntries([u, v].map((name, i) => [name, bs[i].map((x) => constantRational(x) ?? format(x))]));
    const curvature = this.totalCurvature(fmt, { digits });
    const addAll = (list) => out(list.reduce((s, x) => s.add(Iv.from(x)), Iv.point(ZERO)));
    const boundary = { value: addAll(pieces.map((p) => p.value)), pieces };
    const angles = { value: addAll(corners.map((c) => c.exterior)), corners };
    const total = addAll([curvature, boundary.value, angles.value]);
    const twoPi = encloseAst(toAst("2*pi"), {}, bits);
    const expected = out(twoPi);
    return {
      statement: "∬ K dA + ∮ k_g ds + Σ exterior angles = 2π",
      curvature: { name: "integral of the Gaussian curvature", value: curvature },
      boundary: { name: "geodesic curvature of the sides", ...boundary },
      angles: { name: "exterior angles at the corners", ...angles },
      total,
      expected,
      agree: !(total.low.compareTo(expected.high) > 0 || total.high.compareTo(expected.low) < 0),
    };
  }
}

export function metric(g, parameters, opts) {
  return new Metric(g, parameters, opts);
}

// ---------------------------------------------------------------- surfaces

/**
 * A parametrised surface in space, r(u, v):
 *
 *     surface(["cos(u)*sin(v)", "sin(u)*sin(v)", "cos(v)"], ["u", "v"])
 *
 * It is a Metric (its first fundamental form) with the second fundamental
 * form, the normal and the curvatures that depend on how it sits in space.
 */
export class Surface extends Metric {
  constructor(components, parameters = ["u", "v"], opts = {}) {
    if (!Array.isArray(components) || components.length !== 3) refuse("bad-dimension", "a surface needs three component formulas");
    const r = components.map(A);
    const [u, v] = parameters;
    const ru = r.map((c) => D(c, u));
    const rv = r.map((c) => D(c, v));
    super({ E: dot(ru, ru), F: dot(ru, rv), G: dot(rv, rv) }, parameters, opts);
    for (const c of r) for (const name of freeVariables(c)) if (!parameters.includes(name) && !(name in this.params)) refuse("unbound", `${name} has no value: pass it in params`);
    this.r = r;
    this.ru = ru;
    this.rv = rv;
    this.n = cross(ru, rv); // not normalised: |n|² = EG − F²
    const ruu = ru.map((c) => D(c, u));
    const ruv = ru.map((c) => D(c, v));
    const rvv = rv.map((c) => D(c, v));
    // second form times |n|
    this.l = dot(ruu, this.n);
    this.m = dot(ruv, this.n);
    this.nn = dot(rvv, this.n);
  }
  get position() { return this.r.map(format); }
  /** r_u × r_v as formulas (divide by √(EG − F²) for the unit normal) */
  normal() { return this.n.map(format); }
  /** { L, M, N } as formulas */
  second() {
    const w = sqrt(this.det);
    return { L: format(S(div(this.l, w))), M: format(S(div(this.m, w))), N: format(S(div(this.nn, w))) };
  }
  /** Gaussian curvature (LN − M²)/(EG − F²) as a formula tree. */
  gaussianAst() {
    if (this._K) return this._K;
    return (this._K = S(div(sub(mul(this.l, this.nn), mul(this.m, this.m)), mul(this.det, this.det))));
  }
  /** the same from the metric alone, for comparing with gaussian() */
  intrinsicGaussian() {
    const keep = this._K;
    this._K = null;
    const K = Metric.prototype.gaussianAst.call(this);
    this._K = keep;
    return format(K);
  }
  /** Mean curvature (EN − 2FM + GL) / (2(EG − F²)) as a formula tree. */
  meanAst() {
    return S(div(add(sub(mul(this.E, this.nn), mul(num(2), mul(this.F, this.m))), mul(this.G, this.l)), mul(num(2), op("^", this.det, num(new Rational(3n, 2n))))));
  }
  mean() { return format(this.meanAst()); }
  /**
   * Everything at one point, each number a RationalInterval: { point, normal,
   * E, F, G, L, M, N, gaussian, mean, principal: [k1, k2], kind } where kind
   * is "elliptic", "hyperbolic", "parabolic", "planar" or null when the
   * enclosures cannot tell (a parabolic or planar point is only reported
   * when the formulas vanish exactly).
   */
  at(u, v, opts = {}) {
    const bits = bitsOf(opts);
    const env = this._env([u, v], bits);
    const ev = (ast) => evalAt(ast, env, bits);
    const [E, F, G] = [this.E, this.F, this.G].map(ev);
    const det = E.mul(G).sub(F.mul(F));
    if (sign(det) !== 1) refuse("not-regular", "EG − F² may vanish there: the parametrisation is not regular at that point");
    const w = ivSqrt(det, bits);
    const [L, M, N] = [this.l, this.m, this.nn].map((a) => ev(a).div(w));
    const K = L.mul(N).sub(M.mul(M)).div(det);
    const H = E.mul(N).sub(F.mul(M).scale(new Rational(2n))).add(G.mul(L)).div(det.scale(new Rational(2n)));
    // principal curvatures H ± √(H² − K); the discriminant is never negative
    let disc = H.mul(H).sub(K);
    if (disc.lo.numerator < 0n) disc = new Iv(ZERO, disc.hi.numerator < 0n ? ZERO : disc.hi);
    const root = disc.isPoint && disc.lo.numerator === 0n ? Iv.point(ZERO) : disc.lo.numerator === 0n ? new Iv(ZERO, ivSqrt(Iv.point(disc.hi), bits).hi) : ivSqrt(disc, bits);
    const sK = sign(K);
    let kind = sK === 1 ? "elliptic" : sK === -1 ? "hyperbolic" : null;
    if (sK === 0 || (kind === null && isZero(subst(this.gaussianAst(), this.#exact(u, v))))) {
      const flat = [this.l, this.m, this.nn].every((a) => isZero(subst(a, this.#exact(u, v))));
      kind = flat ? "planar" : "parabolic";
    }
    return {
      point: this.r.map((c) => out(ev(c))),
      normal: this.n.map((c) => out(ev(c).div(w))),
      E: out(E), F: out(F), G: out(G), L: out(L), M: out(M), N: out(N),
      gaussian: out(K),
      mean: out(H),
      principal: [out(H.sub(root)), out(H.add(root))],
      kind,
    };
  }
  #exact(u, v) {
    const [a, b] = this.parameters;
    const lift = (x) => (typeof x === "string" ? toAst(x) : x instanceof Iv || x instanceof RationalInterval ? variable("?") : A(x));
    return { [a]: lift(u), [b]: lift(v) };
  }
}

export function surface(components, parameters, opts) {
  return new Surface(components, parameters, opts);
}
