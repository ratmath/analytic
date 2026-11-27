// Solution methods for ordinary differential equations, with their steps.
//
// The validated solver in ode.js answers "what is y(2)?" with a proof and no
// formula. A course asks for the formula and the method. Here each standard
// method is carried out symbolically and reports its steps; the formula it
// finds can then be checked against the validated numerical solution, so a
// wrong closed form is caught, not returned.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ, isZero } from "./rat.js";
import { toAst, format, derivative, freeVariables, constantRational, num, v as variable, op, call, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { solve as odeSolve } from "./ode.js";
import { tidy, vanishesIdentically } from "./tidy.js";
import * as P from "./rpoly.js";
import { antiderivative, sumAst, additiveTerms, rationalRoots, rationalSqrt, solveLinear, partialFractions, expTrigTerm, expTrigAst, expTrigDerivativeMatrix } from "./antiderivative.js";

const A = (x) => (typeof x === "number" ? num(toRational(x)) : typeof x === "bigint" || x instanceof Rational ? num(toQ(x)) : toAst(x));
const qOf = (x) => (x instanceof Rational ? x : typeof x === "string" || typeof x === "number" ? toRational(x) : toQ(x));
const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const add = (a, b) => op("+", a, b);
const sub = (a, b) => op("-", a, b);
const mul = (a, b) => op("*", a, b);
const div = (a, b) => op("/", a, b);
const pw = (a, b) => op("^", a, b);
const neg = (a) => op("neg", a);
const D = (ast, name) => tidy(derivative(ast, name));
const has = (ast, name) => freeVariables(ast).has(name);
const subst = (ast, map) => {
  if (ast.type === "var") return map[ast.name] ?? ast;
  if (ast.args) return { ...ast, args: ast.args.map((a) => subst(a, map)) };
  return ast;
};
const F = format;
const meets = (a, b) => !(a.low.compareTo(b.high) > 0 || a.high.compareTo(b.low) < 0);
const ivOf = (x, bits) => {
  if (x instanceof RationalInterval) return Iv.from(x);
  if (typeof x === "string") {
    const ast = toAst(x);
    const c = constantRational(ast);
    return c !== null ? Iv.point(c) : encloseAst(ast, {}, bits);
  }
  return Iv.point(qOf(x));
};
const integral = (ast, name) => {
  const r = antiderivative(ast, name);
  return r ? r.tree : null;
};
const C = variable("C");
/** |u| → u: for an integrating factor a constant sign does not matter */
const stripAbs = (ast) => (ast.type === "call" && ast.name === "abs" ? stripAbs(ast.args[0]) : ast.args ? { ...ast, args: ast.args.map(stripAbs) } : ast);

// ---------------------------------------------------------------- first order

/** the relation or formula with the constant settled, and its check against the validated solution */
class Particular {
  constructor(parent, x0, y0, constant, solution, relation) {
    this.x0 = x0;
    this.y0 = y0;
    /** the value of the constant, as a formula */
    this.constant = F(constant);
    /** "y = …" when the method gives y explicitly, else null */
    this.solution = solution ? F(solution) : null;
    /** the relation F(x, y) = constant that the solution satisfies, as "F(x, y) = c" */
    this.relation = relation ? `${F(relation)} = ${F(constant)}` : null;
    this._parent = parent;
    this._solution = solution;
    this._relation = relation;
    this._constant = constant;
  }
  /** the value of the explicit solution at x, enclosed */
  at(x, opts = {}) {
    if (!this._solution) refuse("implicit", "this method gives the solution as a relation, not as a formula for y");
    const bits = bitsForDigits(opts.digits ?? 15) + 16;
    return encloseAst(this._solution, { [this._parent.x]: ivOf(x, bits) }, bits).toRationalInterval();
  }
  /**
   * Compare with the validated numerical solution at x1:
   * { agree, numeric, formula } for an explicit solution (two enclosures of
   * y(x1) that must meet), { agree, numeric, relation, constant } for an
   * implicit one (the relation evaluated on the numerical enclosure must
   * contain the constant).
   */
  check(x1, opts = {}) {
    const p = this._parent;
    const bits = bitsForDigits(opts.digits ?? 12) + 24;
    const sol = odeSolve({ f: F(p.rhs), vars: [p.y], time: p.x, y0: this.y0, t0: this.x0, until: x1, order: opts.order ?? 8, tol: opts.tol ?? "1e-8", track: opts.track ?? false }).exact();
    if (!sol.complete) refuse("no-enclosure", `the validated solution stopped before x = ${x1}: ${sol.reason}`);
    const numeric = sol.final;
    if (this._solution) {
      const formula = encloseAst(this._solution, { [p.x]: ivOf(x1, bits) }, bits).toRationalInterval();
      return { agree: meets(numeric, formula), numeric, formula };
    }
    const env = { [p.x]: ivOf(x1, bits), [p.y]: Iv.from(numeric) };
    const relation = encloseAst(this._relation, env, bits).toRationalInterval();
    const constant = encloseAst(this._constant, {}, bits).toRationalInterval();
    return { agree: meets(relation, constant), numeric, relation, constant };
  }
}

class FirstOrder {
  constructor(rhs, x, y) {
    this.rhs = rhs;
    this.x = x;
    this.y = y;
    this.equation = `${y}' = ${F(rhs)}`;
    this.types = [];
    this.type = null;
    this.steps = [];
    /** explicit general solution as a tree in x and C, or null */
    this._explicit = null;
    /** relation G(x, y) with G = C along solutions, or null */
    this._relation = null;
    this._constantAt = null;
    this.singular = [];
  }
  step(what, formula) {
    this.steps.push({ what, formula: typeof formula === "string" ? formula : F(formula) });
  }
  /** "y = …" with the constant C, or null when the solution is only implicit */
  get general() {
    return this._explicit ? `${this.y} = ${F(this._explicit)}` : null;
  }
  /** "G(x, y) = C" */
  get implicit() {
    return this._relation ? `${F(this._relation)} = C` : null;
  }
  /** The solution through (x0, y0). */
  through(x0, y0) {
    const at = { [this.x]: A(x0), [this.y]: A(y0) };
    if (this._explicit) {
      const c = tidy(this._constantAt(A(x0), A(y0)));
      return new Particular(this, x0, y0, c, tidy(subst(this._explicit, { C: c })), null);
    }
    if (!this._relation) refuse("no-method", "no closed form was found for this equation");
    return new Particular(this, x0, y0, tidy(subst(this._relation, at)), null, this._relation);
  }
}

/**
 * y′ = f(x, y) by the standard methods: linear, separable, Bernoulli,
 * homogeneous. Returns { equation, type, types, steps, general, implicit,
 * singular, through(x0, y0) }. `type` is null when none applies or an
 * integral could not be done; the validated solver still works then.
 */
/** log|u| → log u throughout a tree. */
function dropAbsInLog(t) {
  if (!t || (t.type !== "op" && t.type !== "call")) return t;
  if (t.type === "call" && (t.name === "log" || t.name === "ln") && t.args[0]?.type === "call" && t.args[0].name === "abs") return call(t.name, dropAbsInLog(t.args[0].args[0]));
  const args = t.args.map(dropAbsInLog);
  return args.every((a, i) => a === t.args[i]) ? t : { ...t, args };
}

export function firstOrder(rhs, opts = {}) {
  const x = opts.x ?? "x";
  const y = opts.y ?? "y";
  const f = tidy(A(rhs));
  const out = new FirstOrder(f, x, y);
  const X = variable(x);
  const Y = variable(y);
  const fy = D(f, y);

  // which types apply
  const linear = vanishesIdentically(D(fy, y));
  let separable = null;
  {
    // f(x, y)·f(a, b) = f(x, b)·f(a, y) for generic a, b
    const [a, b] = [variable("a_"), variable("b_")];
    const lhs = mul(f, subst(f, { [x]: a, [y]: b }));
    const rhs2 = mul(subst(f, { [y]: b }), subst(f, { [x]: a }));
    if (vanishesIdentically(sub(lhs, rhs2))) {
      // pick a base point where f is defined and not zero
      for (const [a0, b0] of [[1, 1], [0, 1], [1, 2], [2, 1], [1, -1], [3, 2], [0, 0]]) {
        try {
          const c = constantRational(tidy(subst(f, { [x]: num(a0), [y]: num(b0) })));
          const gx = tidy(subst(f, { [y]: num(b0) }));
          if (c === null || isZero(c)) continue;
          separable = { g: gx, h: tidy(div(subst(f, { [x]: num(a0) }), num(c))) };
          break;
        } catch {
          // undefined there: try the next
        }
      }
    }
  }
  let bernoulli = null;
  if (!linear) {
    // f = p·y + q·yⁿ: w = y f_y − f = (n − 1) q yⁿ and n = y w_y / w
    const w = tidy(sub(mul(Y, fy), f));
    if (!vanishesIdentically(w)) {
      const n = constantRational(tidy(div(mul(Y, D(w, y)), w)));
      if (n !== null && !n.equals(ONE) && !isZero(n)) {
        const qx = tidy(div(w, mul(num(n.subtract(ONE)), pw(Y, num(n)))));
        const px = tidy(div(sub(f, mul(qx, pw(Y, num(n)))), Y));
        if (!has(qx, y) && !has(px, y)) bernoulli = { n, p: px, q: qx };
      }
    }
  }
  let homogeneous = null;
  {
    const V = variable("v_");
    const g = tidy(subst(f, { [y]: mul(V, X) }));
    if (!has(g, x) && !linear) homogeneous = { F: g };
  }
  if (linear) out.types.push("linear");
  if (separable) out.types.push("separable");
  if (bernoulli) out.types.push("bernoulli");
  if (homogeneous) out.types.push("homogeneous");

  const tryLinear = () => {
    const b = fy; // coefficient of y
    const a = tidy(sub(f, mul(b, Y)));
    const B0 = integral(b, x);
    if (!B0) return false;
    // any constant multiple of an integrating factor is one, so on an interval where u keeps its sign
    // exp(−log|u|) = ±1/u may be taken as 1/u: keeping |u| leaves ∫ a·μ dx out of reach (∫ 1/|x| dx)
    const B = dropAbsInLog(B0);
    const mu = tidy(call("exp", neg(B)));
    const I = integral(tidy(mul(a, mu)), x);
    if (!I) return false;
    out.step("write it as y′ − b(x)·y = a(x)", `${y}' - (${F(b)})*${y} = ${F(a)}`);
    out.step("integrating factor μ = exp(−∫ b dx)", mu);
    out.step("then (μ·y)′ = μ·a, so μ·y = ∫ μ·a dx + C", `${F(tidy(mul(mu, Y)))} = ${F(I)} + C`);
    out._explicit = tidy(div(add(I, C), mu));
    out._constantAt = (x0, y0) => sub(mul(subst(mu, { [x]: x0 }), y0), subst(I, { [x]: x0 }));
    out.step("solve for y", `${y} = ${F(out._explicit)}`);
    return true;
  };
  const trySeparable = () => {
    const { g, h } = separable;
    const H = integral(tidy(div(num(1), h)), y);
    const G = integral(g, x);
    if (!H || !G) return false;
    out.step("separate the variables", `d${y}/(${F(h)}) = (${F(g)}) d${x}`);
    out.step("integrate both sides", `${F(H)} = ${F(G)} + C`);
    out._relation = tidy(sub(H, G));
    // constant solutions lost by dividing: the zeros of h
    const rf = P.rationalFunction(h, y);
    if (rf) for (const r of rationalRoots(rf.num).roots) out.singular.push(`${y} = ${r.root}`);
    if (out.singular.length) out.step("constant solutions, lost when dividing", out.singular.join(", "));
    // explicit forms worth giving
    const c = constantRational(tidy(div(H, call("log", call("abs", Y)))));
    if (c !== null) {
      out._explicit = tidy(mul(C, call("exp", div(G, num(c)))));
      out._constantAt = (x0, y0) => div(y0, call("exp", div(subst(G, { [x]: x0 }), num(c))));
      out.step("solve for y (C renamed)", `${y} = ${F(out._explicit)}`);
    } else if (vanishesIdentically(sub(H, Y))) {
      out._explicit = tidy(add(G, C));
      out._constantAt = (x0, y0) => sub(y0, subst(G, { [x]: x0 }));
    } else {
      const k = constantRational(tidy(mul(H, Y)));
      if (k !== null) {
        // k/y = G + C
        out._explicit = tidy(div(num(k), add(G, C)));
        out._constantAt = (x0, y0) => sub(div(num(k), y0), subst(G, { [x]: x0 }));
        out.step("solve for y", `${y} = ${F(out._explicit)}`);
      } else {
        const ka = constantRational(tidy(div(H, call("atan", Y))));
        if (ka !== null) {
          // ka·atan(y) = G + C
          out._explicit = call("tan", tidy(div(add(G, C), num(ka))));
          out._constantAt = (x0, y0) => sub(mul(num(ka), call("atan", y0)), subst(G, { [x]: x0 }));
          out.step("solve for y", `${y} = ${F(out._explicit)}`);
        }
      }
    }
    return true;
  };
  const tryBernoulli = () => {
    const { n, p, q } = bernoulli;
    const m = ONE.subtract(n);
    // v = y^(1−n): v′ = m·p·v + m·q
    const b = tidy(mul(num(m), p));
    const a = tidy(mul(num(m), q));
    const B0 = integral(b, x);
    if (!B0) return false;
    // any constant multiple of an integrating factor is one, so on an interval where u keeps its sign
    // exp(−log|u|) = ±1/u may be taken as 1/u: keeping |u| leaves ∫ a·μ dx out of reach (∫ 1/|x| dx)
    const B = dropAbsInLog(B0);
    const mu = tidy(call("exp", neg(B)));
    const I = integral(tidy(mul(a, mu)), x);
    if (!I) return false;
    out.step(`Bernoulli with n = ${n}: substitute v = ${y}^(${m})`, `v' = (${F(b)})*v + ${F(a)}`);
    out.step("integrating factor for the linear equation in v", mu);
    const v = tidy(div(add(I, C), mu));
    out.step("its solution", `v = ${F(v)}`);
    out._explicit = m.reciprocal().denominator === 1n ? tidy(pw(v, num(m.reciprocal()))) : pw(v, num(m.reciprocal()));
    out._constantAt = (x0, y0) => sub(mul(subst(mu, { [x]: x0 }), pw(y0, num(m))), subst(I, { [x]: x0 }));
    out.step("back to y", `${y} = ${F(out._explicit)}`);
    if (n.numerator > 0n) out.singular.push(`${y} = 0`);
    return true;
  };
  const tryHomogeneous = () => {
    const V = variable("v_");
    const g = tidy(sub(homogeneous.F, V));
    if (vanishesIdentically(g)) return false;
    const H = integral(tidy(div(num(1), g)), "v_");
    if (!H) return false;
    out.step(`the right side depends only on ${y}/${x}: substitute ${y} = v·${x}`, `${x}*v' = ${F(subst(g, { v_: variable("v") }))}`);
    out.step("separate and integrate", `${F(subst(H, { v_: variable("v") }))} = log(abs(${x})) + C`);
    out._relation = tidy(sub(subst(H, { v_: div(Y, X) }), call("log", call("abs", X))));
    out.step(`put v = ${y}/${x} back`, `${F(out._relation)} = C`);
    return true;
  };
  // Bernoulli first when it gives y without a root, since the separable form is only a relation
  const neat = bernoulli && ONE.subtract(bernoulli.n).reciprocal().denominator === 1n;
  const order = [["linear", linear, tryLinear], ...(neat ? [["bernoulli", bernoulli, tryBernoulli]] : []), ["separable", separable, trySeparable], ...(neat ? [] : [["bernoulli", bernoulli, tryBernoulli]]), ["homogeneous", homogeneous, tryHomogeneous]];
  const wanted = opts.method ? order.filter(([name]) => name === opts.method) : order;
  for (const [name, applies, run] of wanted) {
    if (!applies) continue;
    out.steps = [];
    out.singular = [];
    if (run()) {
      out.type = name;
      break;
    }
  }
  if (opts.method && out.type === null) refuse("no-method", `the ${opts.method} method does not apply or its integrals were not found`);
  return out;
}

/**
 * M(x, y) dx + N(x, y) dy = 0: exact when ∂M/∂y = ∂N/∂x, and otherwise made
 * exact by an integrating factor that depends on x alone or on y alone.
 * Returns { exact, factor, potential, implicit, steps, through(x0, y0) }.
 */
export function exactEquation(M, N, opts = {}) {
  const x = opts.x ?? "x";
  const y = opts.y ?? "y";
  let m = tidy(A(M));
  let n = tidy(A(N));
  const out = new FirstOrder(tidy(neg(div(m, n))), x, y);
  out.equation = `(${F(m)}) d${x} + (${F(n)}) d${y} = 0`;
  const gap = tidy(sub(D(m, y), D(n, x)));
  out.exact = vanishesIdentically(gap);
  out.factor = null;
  out.step("test: ∂M/∂y − ∂N/∂x", gap);
  if (!out.exact) {
    const viaX = tidy(div(gap, n));
    const viaY = tidy(div(neg(gap), m));
    let mu = null;
    if (!has(viaX, y)) {
      const I = integral(viaX, x);
      if (I) {
        mu = tidy(call("exp", stripAbs(I)));
        out.step(`(M_y − N_x)/N = ${F(viaX)} depends on ${x} alone: factor μ(${x}) = exp(∫ that)`, mu);
      }
    }
    if (!mu && !has(viaY, x)) {
      const I = integral(viaY, y);
      if (I) {
        mu = tidy(call("exp", stripAbs(I)));
        out.step(`(N_x − M_y)/M = ${F(viaY)} depends on ${y} alone: factor μ(${y}) = exp(∫ that)`, mu);
      }
    }
    if (!mu) {
      out.potential = null;
      return out;
    }
    out.factor = F(mu);
    m = tidy(mul(mu, m));
    n = tidy(mul(mu, n));
  }
  const Fx = integral(m, x);
  if (!Fx) return Object.assign(out, { potential: null });
  const restY = tidy(sub(n, D(Fx, y)));
  if (has(restY, x)) return Object.assign(out, { potential: null });
  const Gy = integral(restY, y);
  if (!Gy) return Object.assign(out, { potential: null });
  const phi = sumAst([...additiveTerms(Fx), ...additiveTerms(Gy)]);
  out.step(`integrate M in ${x}`, Fx);
  out.step(`what N still needs, a function of ${y} alone, integrated`, Gy);
  out._relation = phi;
  out.potential = F(phi);
  out.type = "exact";
  out.types.push("exact");
  out.step("solutions are the level curves", `${F(phi)} = C`);
  return out;
}

// ---------------------------------------------------------------- constant coefficients

/** complex numbers over Q as [re, im] */
const cadd = (a, b) => [a[0].add(b[0]), a[1].add(b[1])];
const cmul = (a, b) => [a[0].multiply(b[0]).subtract(a[1].multiply(b[1])), a[0].multiply(b[1]).add(a[1].multiply(b[0]))];
const cIsZero = (a) => isZero(a[0]) && isZero(a[1]);
function polyAtComplex(p, z) {
  let acc = [ZERO, ZERO];
  for (let k = p.length - 1; k >= 0; k--) acc = cadd(cmul(acc, z), [p[k], ZERO]);
  return acc;
}
const polyText = (p, name) => F(tidy(p.map((c, k) => mul(num(c), pw(variable(name), num(k)))).reduce(add)));

/**
 * The roots of a polynomial over Q, as far as square roots reach:
 * [{ kind: "real" | "complex", re, im2, multiplicity, text }] where the root
 * is re ± √(im2)·i for a complex pair (im2 > 0 rational) and re ± √(disc)
 * is written out for real surds. null when a factor of degree above two
 * remains (other than an even quartic).
 */
function characteristicRoots(p) {
  const { roots, rest } = rationalRoots(p);
  const out = roots.map(({ root, multiplicity }) => ({ kind: "real", value: root, surd: null, multiplicity, text: `${root}` }));
  const r = P.monic(rest);
  const quads = [];
  if (P.deg(r) === 2) quads.push([r[1], r[0], 1]);
  else if (P.deg(r) === 4 && isZero(r[1]) && isZero(r[3])) {
    const z = rationalRoots([r[0], r[2], ONE]);
    if (P.deg(z.rest) >= 1) return null;
    for (const t of z.roots) quads.push([ZERO, t.root.negate(), t.multiplicity]);
  } else if (P.deg(r) >= 1) {
    // (x² + px + q)² and the like: try the square-free part
    const sf = P.squareFree(r);
    if (sf.length === 1 && P.deg(sf[0].factor) === 2) quads.push([sf[0].factor[1], sf[0].factor[0], sf[0].multiplicity]);
    else return null;
  }
  for (const [p1, q1, mult] of quads) {
    const re = p1.divide(TWO).negate();
    const disc = p1.multiply(p1).divide(Q(4)).subtract(q1); // (p/2)² − q
    if (disc.numerator < 0n) {
      const im2 = disc.negate();
      const s = rationalSqrt(im2);
      const imText = s ? (s.equals(ONE) ? "" : `${s}*`) : `sqrt(${im2})*`;
      out.push({ kind: "complex", re, im2, im: s, multiplicity: mult, text: `${isZero(re) ? "" : `${re} `}± ${imText}i` });
    } else {
      // real, irrational
      for (const sgn of [1, -1]) out.push({ kind: "real", value: null, re, surd: disc, sign: sgn, multiplicity: mult, text: `${isZero(re) ? "" : `${re} `}${sgn > 0 ? "+" : "-"} sqrt(${disc})` });
    }
  }
  return out;
}

class LinearODE {
  constructor(coeffs, forcing, x, y) {
    this.x = x;
    this.y = y;
    this.order = coeffs.length - 1;
    this.coefficients = coeffs; // highest derivative first
    this.forcing = forcing;
    this.steps = [];
  }
  step(what, formula) {
    this.steps.push({ what, formula: typeof formula === "string" ? formula : F(formula) });
  }
  /** "y = …" with C1, C2, … */
  get general() {
    if (!this._particular && !vanishesIdentically(this.forcing)) return null;
    const hom = this._basis.map((b, i) => tidy(mul(variable(`C${i + 1}`), b)));
    return `${this.y} = ${F(sumAst([...hom, ...(this._particular ? additiveTerms(this._particular) : [])]))}`;
  }
  /**
   * The solution with y(x0) = values[0], y′(x0) = values[1], …:
   * { constants, solution, at(x), check(x1) }.
   */
  initial(values, x0 = 0) {
    const n = this.order;
    if (values.length !== n) refuse("bad-initial", `an equation of order ${n} needs ${n} initial values`);
    if (!this._particular && !vanishesIdentically(this.forcing)) refuse("no-method", "no particular solution was found, so there is no formula to fit");
    const at = { [this.x]: A(x0) };
    const yp = this._particular ?? num(0);
    // rows: derivative order, columns: basis functions
    const rows = [];
    const rhs = [];
    let ds = this._basis.slice();
    let dp = yp;
    for (let k = 0; k < n; k++) {
      rows.push(ds.map((b) => tidy(subst(b, at))));
      rhs.push(tidy(sub(A(values[k]), subst(dp, at))));
      ds = ds.map((b) => D(b, this.x));
      dp = D(dp, this.x);
    }
    const consts = solveSymbolic(rows, rhs);
    if (!consts) refuse("singular", "the initial conditions do not determine the constants");
    const solution = tidy(add(sumAst(this._basis.map((b, i) => mul(consts[i], b))), yp));
    const self = this;
    return {
      constants: consts.map(F),
      solution: `${this.y} = ${F(solution)}`,
      tree: solution,
      at(xv, opts = {}) {
        const bits = bitsForDigits(opts.digits ?? 15) + 16;
        return encloseAst(solution, { [self.x]: ivOf(xv, bits) }, bits).toRationalInterval();
      },
      /** the formula against the validated numerical solution at x1 */
      check(x1, opts = {}) {
        const bits = bitsForDigits(opts.digits ?? 12) + 24;
        const names = Array.from({ length: n }, (_, i) => `y${i}_`);
        const lead = self.coefficients[0];
        const top = tidy(div(sub(self.forcing, self.coefficients.slice(1).map((c, i) => mul(num(c), variable(names[n - 1 - i]))).reduce(add)), num(lead)));
        const sol = odeSolve({ f: [...names.slice(1), F(top)], vars: names, time: self.x, y0: values.map((val) => (typeof val === "string" ? toRational(val) : val)), t0: x0, until: x1, order: opts.order ?? 8, tol: opts.tol ?? "1e-8", track: opts.track ?? false }).exact();
        if (!sol.complete) refuse("no-enclosure", `the validated solution stopped before x = ${x1}: ${sol.reason}`);
        const numeric = sol.final[0];
        const formula = encloseAst(solution, { [self.x]: ivOf(x1, bits) }, bits).toRationalInterval();
        return { agree: meets(numeric, formula), numeric, formula };
      },
    };
  }
}

/** Gaussian elimination on formula trees, tidying as it goes; null when singular */
function solveSymbolic(M, b) {
  const n = b.length;
  const rows = M.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let piv = -1;
    for (let r = c; r < n; r++) if (!vanishesIdentically(rows[r][c])) {
      piv = r;
      break;
    }
    if (piv < 0) return null;
    [rows[c], rows[piv]] = [rows[piv], rows[c]];
    const p = rows[c][c];
    rows[c] = rows[c].map((e) => tidy(div(e, p)));
    for (let r = 0; r < n; r++) {
      if (r === c || vanishesIdentically(rows[r][c])) continue;
      const f = rows[r][c];
      rows[r] = rows[r].map((e, j) => tidy(sub(e, mul(f, rows[c][j]))));
    }
  }
  return rows.map((row) => row[n]);
}
/** a solution of M·x = b with free unknowns set to 0; null when inconsistent */
function solveConsistent(M, b) {
  const rows = M.map((row, i) => [...row, b[i]]);
  const m = rows.length;
  const n = M[0].length;
  const pivots = [];
  let r = 0;
  for (let c = 0; c < n && r < m; c++) {
    let piv = -1;
    for (let i = r; i < m; i++) if (!isZero(rows[i][c])) {
      piv = i;
      break;
    }
    if (piv < 0) continue;
    [rows[r], rows[piv]] = [rows[piv], rows[r]];
    const inv = rows[r][c].reciprocal();
    rows[r] = rows[r].map((e) => e.multiply(inv));
    for (let i = 0; i < m; i++) {
      if (i === r || isZero(rows[i][c])) continue;
      const f = rows[i][c];
      rows[i] = rows[i].map((e, j) => e.subtract(f.multiply(rows[r][j])));
    }
    pivots.push(c);
    r++;
  }
  for (let i = r; i < m; i++) if (!isZero(rows[i][n])) return null;
  const x = new Array(n).fill(ZERO);
  pivots.forEach((c, i) => (x[c] = rows[i][n]));
  return x;
}
const matMul = (X, Y) => X.map((row) => Y[0].map((_, j) => row.reduce((s, e, k) => s.add(e.multiply(Y[k][j])), ZERO)));
const matAdd = (X, Y, s = ONE) => X.map((row, i) => row.map((e, j) => e.add(Y[i][j].multiply(s))));
const identity = (n) => Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => (i === j ? ONE : ZERO)));

/**
 * aₙ y⁽ⁿ⁾ + … + a₁ y′ + a₀ y = g(x) with rational coefficients, given
 * highest derivative first: linearODE([1, -3, 2], "exp(x)").
 *
 * Returns { characteristic, roots, basis, homogeneous, particular, method,
 * steps, general, initial(values, x0) }.
 */
export function linearODE(coefficients, forcing = 0, opts = {}) {
  const x = opts.x ?? "x";
  const y = opts.y ?? "y";
  const cs = coefficients.map(qOf);
  if (cs.length < 2 || isZero(cs[0])) refuse("bad-equation", "give the coefficients highest derivative first, the first one not zero");
  const g = tidy(A(forcing));
  const out = new LinearODE(cs, g, x, y);
  const n = cs.length - 1;
  const p = cs.slice().reverse(); // index = power of r
  out.characteristic = `${polyText(p, "r")} = 0`;
  out.step("characteristic equation", out.characteristic);
  const roots = characteristicRoots(p);
  if (!roots) refuse("no-closed-form", "the characteristic polynomial has roots that square roots do not reach; use ode.solve for values");
  out.roots = roots.map((r) => ({ root: r.text, kind: r.kind, multiplicity: r.multiplicity }));
  out.step("roots", roots.map((r) => (r.multiplicity > 1 ? `${r.text} (${r.multiplicity} times)` : r.text)).join(",  "));
  const X = variable(x);
  const basis = [];
  for (const r of roots) {
    for (let j = 0; j < r.multiplicity; j++) {
      const xj = j === 0 ? null : j === 1 ? X : pw(X, num(j));
      const withPower = (t) => (xj ? (t ? mul(xj, t) : xj) : t ?? num(1));
      if (r.kind === "real") {
        const rate = r.value !== null ? num(r.value) : r.sign > 0 ? add(num(r.re), call("sqrt", num(r.surd))) : sub(num(r.re), call("sqrt", num(r.surd)));
        const zero = r.value !== null && isZero(r.value);
        basis.push(withPower(zero ? null : call("exp", tidy(mul(rate, X)))));
      } else {
        const w = r.im ? num(r.im) : call("sqrt", num(r.im2));
        const e = isZero(r.re) ? null : call("exp", tidy(mul(num(r.re), X)));
        for (const trig of ["cos", "sin"]) {
          const t = call(trig, tidy(mul(w, X)));
          basis.push(withPower(e ? mul(e, t) : t));
        }
      }
    }
  }
  out._basis = basis.map(tidy);
  out.basis = out._basis.map(F);
  out.homogeneous = F(sumAst(out._basis.map((b, i) => tidy(mul(variable(`C${i + 1}`), b)))));
  out.step("solutions of the homogeneous equation", out.basis.join(",  "));
  out._particular = null;
  out.particular = null;
  out.method = null;
  if (vanishesIdentically(g)) {
    out._particular = num(0);
    out.particular = "0";
    return out;
  }
  // undetermined coefficients: every term c·x^k·e^{ax}·(cos|sin)(wx)
  const ts = additiveTerms(g).map((t) => expTrigTerm(tidy(t), x));
  if (ts.every((t) => t !== null)) {
    const groups = new Map();
    for (const t of ts) {
      const key = `${t.a}|${t.w}`;
      if (!groups.has(key)) groups.set(key, { a: t.a, w: t.w, terms: [] });
      groups.get(key).terms.push(t);
    }
    const parts = [];
    for (const grp of groups.values()) {
      // multiplicity of a + iw as a characteristic root
      let s = 0;
      let dp = p;
      while (cIsZero(polyAtComplex(dp, [grp.a, grp.w])) && s <= n) {
        s++;
        dp = P.derivative(dp);
      }
      const K = Math.max(...grp.terms.map((t) => t.k)) + s;
      const two = !isZero(grp.w);
      const M = expTrigDerivativeMatrix(K, grp.a, grp.w);
      const size = M.length;
      // L = Σ a_j M^j
      let L = Array.from({ length: size }, () => new Array(size).fill(ZERO));
      let Mk = identity(size);
      for (let j = 0; j <= n; j++) {
        L = matAdd(L, Mk, p[j]);
        Mk = matMul(M, Mk);
      }
      const b = new Array(size).fill(ZERO);
      for (const t of grp.terms) {
        const i = two ? 2 * t.k + (t.trig === "sin" ? 1 : 0) : t.k;
        b[i] = b[i].add(t.c);
      }
      // the lowest s powers solve the homogeneous equation: leave them out
      const keep = [];
      for (let i = 0; i < size; i++) if ((two ? Math.floor(i / 2) : i) >= s) keep.push(i);
      const sol = solveConsistent(L.map((row) => keep.map((i) => row[i])), b);
      if (!sol) refuse("internal", "undetermined coefficients found no solution");
      const deg = K - s;
      const polyName = deg === 0 ? "A" : `(polynomial of degree ${deg})`;
      const xs = s === 0 ? "" : s === 1 ? "x·" : `x^${s}·`;
      const shape = two ? `${xs}${isZero(grp.a) ? "" : `exp(${grp.a}x)·`}(${deg === 0 ? "A" : "P(x)"}·cos(${grp.w}x) + ${deg === 0 ? "B" : "Q(x)"}·sin(${grp.w}x))${deg === 0 ? "" : `, P and Q of degree ${deg}`}` : `${xs}${polyName}${isZero(grp.a) ? "" : `·exp(${grp.a}x)`}`;
      const rootName = isZero(grp.w) ? `${grp.a}` : `${isZero(grp.a) ? "" : `${grp.a} `}± ${grp.w.equals(ONE) ? "" : grp.w}i`;
      out.step(s > 0 ? `trial solution, with the extra factor ${xs.slice(0, -1)} because ${rootName} is a characteristic root${s > 1 ? ` ${s} times` : ""}` : "trial solution", shape);
      sol.forEach((coef, idx) => {
        if (isZero(coef)) return;
        const i = keep[idx];
        parts.push(mul(num(coef), expTrigAst({ k: two ? Math.floor(i / 2) : i, a: grp.a, w: grp.w, trig: two ? (i % 2 ? "sin" : "cos") : null }, x)));
      });
    }
    out._particular = tidy(sumAst(parts));
    out.method = "undetermined coefficients";
  } else if (n === 2) {
    // variation of parameters
    const [y1, y2] = out._basis;
    const W = tidy(sub(mul(y1, D(y2, x)), mul(y2, D(y1, x))));
    const gn = tidy(div(g, num(cs[0])));
    const u1 = integral(tidy(neg(div(mul(y2, gn), W))), x);
    const u2 = integral(tidy(div(mul(y1, gn), W)), x);
    out.step("Wronskian of the two solutions", W);
    if (u1 && u2) {
      out.step("u₁ = −∫ y₂ g / W", u1);
      out.step("u₂ = ∫ y₁ g / W", u2);
      out._particular = tidy(add(mul(u1, y1), mul(u2, y2)));
      out.method = "variation of parameters";
    }
  }
  if (out._particular) {
    // the residual must vanish
    let res = neg(g);
    let d = out._particular;
    for (let j = 0; j <= n; j++) {
      res = add(res, mul(num(p[j]), d));
      d = D(d, x);
    }
    out.verified = vanishesIdentically(res);
    out.particular = F(out._particular);
    out.step(`particular solution, by ${out.method}`, out.particular);
  }
  return out;
}

// ---------------------------------------------------------------- Laplace transforms

const fact = (k) => {
  let f = 1n;
  for (let i = 2n; i <= BigInt(k); i++) f *= i;
  return new Rational(f);
};
const binom = (n, k) => {
  let r = 1n;
  for (let i = 0n; i < BigInt(k); i++) r = (r * (BigInt(n) - i)) / (i + 1n);
  return new Rational(r);
};

const STEP_NAMES = new Set(["heaviside"]);
const IMPULSE_NAMES = new Set(["dirac"]);
/** the multiplicative factors of a term, with a sign and rational constant pulled out */
const factorsOf = (ast) => {
  if (ast.type === "op" && ast.op === "*") return [...factorsOf(ast.args[0]), ...factorsOf(ast.args[1])];
  return [ast];
};
const productOf = (fs) => (fs.length ? fs.reduce((a, b) => mul(a, b)) : num(1));
/** heaviside(t − c) or dirac(t − c): { kind, c }, or null */
function switchOf(ast, t) {
  if (ast.type !== "call" || ast.args.length !== 1) return null;
  const kind = STEP_NAMES.has(ast.name) ? "step" : IMPULSE_NAMES.has(ast.name) ? "impulse" : null;
  if (!kind) return null;
  const arg = tidy(ast.args[0]);
  const lin = arg.type === "var" && arg.name === t ? { a: ONE, b: ZERO } : linearInVar(arg, t);
  if (!lin || !lin.a.equals(ONE)) refuse("no-transform", `write ${ast.name}(${t} - c) with a rational c ≥ 0`);
  const c = lin.b.negate();
  if (c.numerator < 0n) refuse("no-transform", `${ast.name}(${F(arg)}) switches at a negative time; the transform starts at ${t} = 0`);
  return { kind, c };
}
function linearInVar(ast, name) {
  const rf = P.rationalFunction(ast, name);
  if (!rf || P.deg(rf.den) !== 0 || P.deg(rf.num) !== 1) return null;
  return { a: rf.num[1].divide(rf.den[0]), b: rf.num[0].divide(rf.den[0]) };
}

/** L{c·t^k·e^{at}·trig(wt)} as a tree in s */
function transformTerm(e, Sv) {
  const u = isZero(e.a) ? Sv : tidy(sub(Sv, num(e.a)));
  const power = (base, m) => (m === 1 ? base : pw(base, num(m)));
  if (!e.trig || isZero(e.w)) {
    if (e.trig === "sin") return num(ZERO);
    return div(num(e.c.multiply(fact(e.k))), power(u, e.k + 1));
  }
  // k!/(u − iw)^{k+1} = k!·(u + iw)^{k+1}/(u² + w²)^{k+1}; cos takes the real part, sin the imaginary
  const m = e.k + 1;
  let top = null;
  for (let j = e.trig === "cos" ? 0 : 1; j <= m; j += 2) {
    const sgn = Math.floor(j / 2) % 2 === 0 ? ONE : ONE.negate();
    const coef = binom(m, j).multiply(sgn);
    let wj = ONE;
    for (let i = 0; i < j; i++) wj = wj.multiply(e.w);
    const piece = mul(num(coef.multiply(wj)), pw(u, num(m - j)));
    top = top ? add(top, piece) : piece;
  }
  return div(tidy(mul(num(e.c.multiply(fact(e.k))), top)), power(add(pw(u, num(2)), num(e.w.multiply(e.w))), m));
}

/**
 * L{g(t + c)} for g = C·t^k·e^{at}·trig(wt): expand (t + c)^k by the binomial
 * theorem and trig(wt + wc) by the addition formulas. The constants e^{ac},
 * cos(wc), sin(wc) stay as exact formulas.
 */
function shiftedTransform(e, c, Sv) {
  const parts = [];
  const expC = isZero(e.a) || isZero(c) ? null : call("exp", num(e.a.multiply(c)));
  const wc = e.w.multiply(c);
  const trigPieces = !e.trig || isZero(e.w)
    ? [{ trig: e.trig, k: null }]
    : isZero(wc)
      ? [{ trig: e.trig, k: num(1) }]
      : e.trig === "cos"
        ? [{ trig: "cos", k: call("cos", num(wc)) }, { trig: "sin", k: neg(call("sin", num(wc))) }]
        : [{ trig: "cos", k: call("sin", num(wc)) }, { trig: "sin", k: call("cos", num(wc)) }];
  for (let j = 0; j <= e.k; j++) {
    let cj = binom(e.k, j);
    for (let i = 0; i < e.k - j; i++) cj = cj.multiply(c);
    if (isZero(cj)) continue;
    for (const tp of trigPieces) {
      const inner = transformTerm({ c: e.c.multiply(cj), k: j, a: e.a, w: e.w, trig: tp.trig }, Sv);
      let piece = inner;
      if (tp.k) piece = mul(tp.k, piece);
      if (expC) piece = mul(expC, piece);
      parts.push(piece);
    }
  }
  return sumAst(parts);
}

/**
 * The pieces of the transform grouped by delay: Map(c → tree in s without
 * the factor e^{−cs}). Terms are c·t^k·e^{at}·(cos | sin)(wt), optionally
 * times heaviside(t − c) (a switch at time c), or dirac(t − c)·g(t) (an
 * impulse at c).
 */
function transformGroups(f, t, s) {
  const Sv = variable(s);
  const groups = new Map();
  const put = (c, ast) => {
    const key = String(c);
    const g = groups.get(key);
    groups.set(key, g ? { c, parts: [...g.parts, ast] } : { c, parts: [ast] });
  };
  for (const term of additiveTerms(tidy(A(f)))) {
    let sign = 1;
    let body = tidy(term);
    while (body.type === "op" && body.op === "neg") {
      sign = -sign;
      body = body.args[0];
    }
    const fs = factorsOf(body);
    const switches = fs.map((x) => switchOf(x, t));
    const rest = productOf(fs.filter((_, i) => !switches[i]));
    const sw = switches.filter(Boolean);
    const signed = (ast) => (sign < 0 ? neg(ast) : ast);
    if (sw.length > 1) refuse("no-transform", "one switch (heaviside or dirac) per term; split the term");
    if (sw.length === 1 && sw[0].kind === "impulse") {
      // L{g(t)·δ(t − c)} = g(c)·e^{−cs}
      put(sw[0].c, signed(tidy(subst(rest, { [t]: num(sw[0].c) }))));
      continue;
    }
    let e = expTrigTerm(tidy(rest), t);
    if (!e && sw.length === 1) {
      // u(t − c)·f(t − c): read f from rest(t + c) and transform it unshifted
      const moved = expTrigTerm(tidy(subst(rest, { [t]: add(variable(t), num(sw[0].c)) })), t);
      if (moved) {
        if (sign < 0) moved.c = moved.c.negate();
        put(sw[0].c, transformTerm(moved, Sv));
        continue;
      }
    }
    if (!e) refuse("no-transform", `${F(rest)} is not a product of a power of ${t}, an exponential and a sine or cosine`);
    if (sign < 0) e.c = e.c.negate();
    if (sw.length === 1) put(sw[0].c, shiftedTransform(e, sw[0].c, Sv));
    else put(ZERO, transformTerm(e, Sv));
  }
  return [...groups.values()].map((g) => ({ c: g.c, ast: sumAst(g.parts) })).sort((a, b) => a.c.compareTo(b.c));
}
/** f·ast, written tidily: no "*1", no "*-(…)" */
function withFactor(f, ast, skip = false) {
  if (skip) return ast;
  if (ast.type === "op" && ast.op === "neg") return neg(withFactor(f, ast.args[0]));
  if (ast.type === "num") {
    if (ast.value.equals(ONE)) return f;
    if (ast.value.numerator < 0n) return neg(withFactor(f, num(ast.value.negate())));
    return mul(ast, f);
  }
  if (ast.type === "op" && ast.op === "/") {
    const top = withFactor(f, ast.args[0]);
    return top.type === "op" && top.op === "neg" ? neg(div(top.args[0], ast.args[1])) : div(top, ast.args[1]);
  }
  return mul(f, ast);
}
const delayFactor = (c, Sv) => call("exp", tidy(neg(mul(num(c), Sv))));
function joinGroups(groups, Sv) {
  const parts = groups.map(({ c, ast: raw }) => {
    return withFactor(delayFactor(c, Sv), raw, isZero(c));
  });
  return sumAst(parts);
}

/**
 * The Laplace transform, as a formula in s, of a sum of terms
 * c·t^k·e^{at}·(cos | sin)(wt). A term may be switched on at time c by a
 * factor heaviside(t − c), and dirac(t − c) is a unit
 * impulse at time c. With { delay: c } the whole function is taken to be
 * u(t − c)·f(t − c), which multiplies the transform by e^{−cs}.
 */
export function laplace(f, opts = {}) {
  const t = opts.t ?? "t";
  const s = opts.s ?? "s";
  const Sv = variable(s);
  let groups = transformGroups(f, t, s);
  if (opts.delay !== undefined) {
    const d = qOf(opts.delay);
    groups = groups.map((g) => ({ c: g.c.add(d), ast: g.ast }));
  }
  return F(joinGroups(groups, Sv));
}

/** a rational function of s, inverted by partial fractions: { fractions, terms, impulse } */
function inverseRational(rf, t, s) {
  const pf = partialFractions(rf.num, rf.den);
  if (!pf) refuse("no-transform", "the denominator does not split into linear factors and single quadratics over the rationals");
  let impulse = null;
  if (!P.isZeroPoly(pf.poly)) {
    if (P.deg(pf.poly) > 0) refuse("no-transform", "the numerator's degree exceeds the denominator's: the inverse would contain derivatives of an impulse");
    impulse = pf.poly[0];
  }
  const Tv = variable(t);
  const Sv = variable(s);
  const fractions = impulse ? [num(impulse)] : [];
  const terms = [];
  for (const L of pf.linear) {
    const u = isZero(L.root) ? Sv : sub(Sv, num(L.root));
    fractions.push(div(num(L.coeff), L.power === 1 ? u : pw(u, num(L.power))));
    terms.push(mul(num(L.coeff.divide(fact(L.power - 1))), expTrigAst({ k: L.power - 1, a: L.root, w: ZERO, trig: null }, t)));
  }
  for (const qd of pf.quadratic) {
    const quad = sumAst([pw(Sv, num(2)), mul(num(qd.p), Sv), num(qd.q)]);
    fractions.push(div(sumAst([mul(num(qd.alpha), Sv), num(qd.beta)]), quad));
    const a = qd.p.divide(TWO).negate();
    const c = qd.q.subtract(qd.p.multiply(qd.p).divide(Q(4)));
    const k = qd.beta.add(qd.alpha.multiply(a));
    const e = isZero(a) ? null : call("exp", mul(num(a), Tv));
    const withE = (x) => (e ? mul(e, x) : x);
    const pos = c.numerator > 0n;
    const m = pos ? c : c.negate();
    const r = rationalSqrt(m);
    const root = r ? num(r) : call("sqrt", num(m));
    const arg = tidy(mul(root, Tv));
    if (!isZero(qd.alpha)) terms.push(mul(num(qd.alpha), withE(call(pos ? "cos" : "cosh", arg))));
    if (!isZero(k)) terms.push(mul(div(num(k), root), withE(call(pos ? "sin" : "sinh", arg))));
  }
  return { fractions: sumAst(fractions.map(tidy)), terms: sumAst(terms.map(tidy)), impulse };
}

/** split a term of F(s) into a delay c (from factors e^{as}, a ≤ 0 in total) and the rest */
function splitDelay(ast, s) {
  const walk = (x) => {
    if (x.type === "call" && x.name === "exp") {
      const lin = linearInVar(tidy(x.args[0]), s);
      if (lin && isZero(lin.b)) return { a: lin.a, rest: num(1) };
      return null;
    }
    if (x.type === "op" && (x.op === "*" || x.op === "/")) {
      const l = walk(x.args[0]);
      const r = walk(x.args[1]);
      if (!l && !r) return null;
      const a = (l?.a ?? ZERO)[x.op === "*" ? "add" : "subtract"](r?.a ?? ZERO);
      return { a, rest: op(x.op, l ? l.rest : x.args[0], r ? r.rest : x.args[1]) };
    }
    if (x.type === "op" && x.op === "neg") {
      const y = walk(x.args[0]);
      return y && { a: y.a, rest: neg(y.rest) };
    }
    return null;
  };
  const w = walk(ast);
  if (!w) return null;
  if (w.a.numerator > 0n) refuse("no-transform", `a factor e^(${w.a}*${s}) would switch on before time 0`);
  return { c: w.a.negate(), rest: w.rest };
}

/** the switched piece u(t − c)·g(t − c), as a tree */
function switchedOn(c, ast, t, kind = "heaviside") {
  const Tv = variable(t);
  if (isZero(c)) return ast;
  const shifted = tidy(subst(ast, { [t]: sub(Tv, num(c)) }));
  return withFactor(call(kind, tidy(sub(Tv, num(c)))), shifted);
}

/**
 * The inverse Laplace transform of a sum of terms e^{−cs}·R(s), each R a
 * rational function of s with rational coefficients, by partial fractions
 * over the rationals: { partialFractions, result }. A delay c gives
 * heaviside(t − c)·r(t − c); a constant part of R gives an impulse dirac(t − c).
 */
export function inverseLaplace(Fs, opts = {}) {
  const t = opts.t ?? "t";
  const s = opts.s ?? "s";
  const Sv = variable(s);
  const Tv = variable(t);
  const groups = new Map();
  for (const term of additiveTerms(A(Fs))) {
    const d = splitDelay(term, s) ?? { c: ZERO, rest: term };
    const key = String(d.c);
    const g = groups.get(key);
    groups.set(key, { c: d.c, parts: [...(g?.parts ?? []), d.rest] });
  }
  const fractions = [];
  const terms = [];
  for (const { c, parts } of [...groups.values()].sort((a, b) => a.c.compareTo(b.c))) {
    const rf = P.rationalFunction(tidy(sumAst(parts)), s);
    if (!rf) refuse("no-transform", "the inverse here is for sums of e^(-c*s) times rational functions of s with rational coefficients");
    const inv = inverseRational(rf, t, s);
    fractions.push(withFactor(delayFactor(c, Sv), inv.fractions, isZero(c)));
    if (inv.impulse) terms.push(withFactor(isZero(c) ? call("dirac", Tv) : call("dirac", tidy(sub(Tv, num(c)))), num(inv.impulse)));
    const body = inv.terms;
    if (!(body.type === "num" && isZero(body.value))) terms.push(isZero(c) ? body : switchedOn(c, body, t));
  }
  const result = sumAst(terms);
  return { partialFractions: F(sumAst(fractions)), result: F(result), tree: result };
}

/** replace heaviside(t − c) by 1 or 0 for times in (from, …) and impulses by 0: the formula on one interval */
function onInterval(ast, t, from) {
  if (ast.type === "call") {
    const sw = ast.args.length === 1 && (STEP_NAMES.has(ast.name) || IMPULSE_NAMES.has(ast.name)) ? switchOf(ast, t) : null;
    if (sw) return num(sw.kind === "impulse" ? ZERO : sw.c.compareTo(from) <= 0 ? ONE : ZERO);
  }
  if (ast.args) return { ...ast, args: ast.args.map((a) => onInterval(a, t, from)) };
  return ast;
}
function switchTimes(ast, t, out = new Map()) {
  if (ast.type === "call" && ast.args.length === 1 && (STEP_NAMES.has(ast.name) || IMPULSE_NAMES.has(ast.name))) {
    const sw = switchOf(ast, t);
    const prev = out.get(String(sw.c));
    out.set(String(sw.c), { c: sw.c, impulse: (prev?.impulse ?? false) || sw.kind === "impulse" });
  }
  if (ast.args) for (const a of ast.args) switchTimes(a, t, out);
  return out;
}

/**
 * Solve a_n y⁽ⁿ⁾ + … + a_0 y = g(t) with y(0), y′(0), … given, by the Laplace
 * transform. The forcing may switch on and off (heaviside(t − c)) and kick
 * (dirac(t − c)). Returns { transform, partialFractions, solution, pieces,
 * verified, steps }: `pieces` is the solution on each interval between
 * switching times, and `verified` says that each piece satisfies the
 * equation identically, the first piece the initial conditions, and the
 * pieces join as the equation forces: y, y′, …, y⁽ⁿ⁻¹⁾ continuous, except
 * that an impulse w·dirac(t − c) makes y⁽ⁿ⁻¹⁾ jump by exactly w/a_n at c.
 */
export function laplaceSolve(coefficients, forcing = 0, initial = [], opts = {}) {
  const t = opts.t ?? "t";
  const s = opts.s ?? "s";
  const Sv = variable(s);
  const Tv = variable(t);
  const a = coefficients.map(qOf);
  const n = a.length - 1;
  if (n < 1 || isZero(a[0])) refuse("bad-equation", "give the coefficients highest derivative first, the first one not zero");
  const y0 = Array.from({ length: n }, (_, i) => qOf(initial[i] ?? 0));
  const steps = [];
  const step = (what, value) => steps.push({ what, value });
  const p = a.slice().reverse(); // p[j] = coefficient of s^j
  step("characteristic polynomial", polyText(p, s));
  // Y·p(s) = G(s) + Σ_j a_j Σ_{i<j} s^{j−1−i} y⁽ⁱ⁾(0)
  const q = new Array(n).fill(ZERO);
  for (let j = 1; j <= n; j++) for (let i = 0; i < j; i++) q[j - 1 - i] = q[j - 1 - i].add(p[j].multiply(y0[i]));
  const groups = transformGroups(forcing, t, s);
  step("transform of the forcing", F(joinGroups(groups, Sv)) || "0");
  const pAst = polyAst(p, Sv);
  const qAst = polyAst(q, Sv);
  const byDelay = new Map(groups.map((g) => [String(g.c), g]));
  if (!byDelay.has("0")) byDelay.set("0", { c: ZERO, ast: num(ZERO) });
  const ys = [...byDelay.values()].sort((x, y) => x.c.compareTo(y.c)).map((g) => ({ c: g.c, ast: tidy(div(isZero(g.c) ? add(g.ast, qAst) : g.ast, pAst)) }));
  const transform = F(joinGroups(ys, Sv));
  step("Y(s)", transform);
  const inv = inverseLaplace(transform, { t, s });
  step("partial fractions", inv.partialFractions);
  step("y(t)", inv.result);
  // the certificate
  const g = tidy(A(forcing));
  const y = inv.tree;
  const times = [...switchTimes(g, t).values(), ...switchTimes(y, t).values()].sort((u, v) => u.c.compareTo(v.c));
  const breaks = [];
  for (const x of times) {
    const last = breaks[breaks.length - 1];
    if (last && last.c.equals(x.c)) last.impulse ||= x.impulse;
    else breaks.push({ ...x });
  }
  const starts = [ZERO, ...breaks.map((b) => b.c).filter((c) => c.numerator > 0n)];
  const pieces = starts.map((from) => ({ from: String(from), y: tidy(onInterval(y, t, from)), g: tidy(onInterval(g, t, from)) }));
  const derivs = (ast) => {
    const out = [ast];
    for (let j = 1; j <= n; j++) out.push(D(out[j - 1], t));
    return out;
  };
  let verified = true;
  const reasons = [];
  for (const piece of pieces) {
    const d = derivs(piece.y);
    let lhs = num(ZERO);
    for (let j = 0; j <= n; j++) lhs = add(lhs, mul(num(p[j]), d[j]));
    if (!vanishesIdentically(sub(lhs, piece.g))) {
      verified = false;
      reasons.push(`the equation on t > ${piece.from}`);
    }
  }
  const at = (ast, c) => tidy(subst(ast, { [t]: num(c) }));
  // the size of each impulse in the forcing: an impulse w·δ(t − c) makes y⁽ⁿ⁻¹⁾ jump by w/a_n at c
  const kicks = new Map();
  for (const term of additiveTerms(g)) {
    let sign = 1;
    let body = term;
    while (body.type === "op" && body.op === "neg") {
      sign = -sign;
      body = body.args[0];
    }
    const fs = factorsOf(body);
    const k = fs.findIndex((x) => x.type === "call" && IMPULSE_NAMES.has(x.name));
    if (k < 0) continue;
    const c = switchOf(fs[k], t).c;
    const w = at(productOf(fs.filter((_, i) => i !== k)), c);
    const key = String(c);
    kicks.set(key, tidy(add(kicks.get(key) ?? num(ZERO), sign < 0 ? neg(w) : w)));
  }
  const jump = (c) => tidy(div(kicks.get(String(c)) ?? num(ZERO), num(p[n])));
  const d0 = derivs(pieces[0].y);
  for (let i = 0; i < n; i++) {
    const want = i === n - 1 ? add(num(y0[i]), jump(ZERO)) : num(y0[i]);
    if (!vanishesIdentically(sub(at(d0[i], ZERO), want))) {
      verified = false;
      reasons.push(`y${"'".repeat(i)}(0)`);
    }
  }
  for (let k = 1; k < pieces.length; k++) {
    const c = qOf(pieces[k].from);
    const before = derivs(pieces[k - 1].y);
    const after = derivs(pieces[k].y);
    for (let i = 0; i < n; i++) {
      const want = i === n - 1 ? jump(c) : num(ZERO);
      if (!vanishesIdentically(sub(sub(at(after[i], c), at(before[i], c)), want))) {
        verified = false;
        reasons.push(`the join of y${"'".repeat(i)} at t = ${c}`);
      }
    }
  }
  step(verified ? "verified: each piece solves the equation, the start matches, the pieces join" : `not verified: ${reasons.join("; ")}`, "");
  return {
    transform,
    partialFractions: inv.partialFractions,
    solution: inv.result,
    pieces: pieces.map((x) => ({ from: x.from, y: F(x.y) })),
    verified,
    steps,
    /** the solution at a time, as a formula (heaviside and dirac switched for that time) */
    at(time) {
      const c = qOf(time);
      return F(tidy(at(onInterval(y, t, c), c)));
    },
  };
}
function polyAst(p, X) {
  const parts = [];
  p.forEach((c, j) => {
    if (isZero(c)) return;
    parts.push(j === 0 ? num(c) : mul(num(c), j === 1 ? X : pw(X, num(j))));
  });
  return parts.length ? tidy(sumAst(parts)) : num(ZERO);
}

// ---------------------------------------------------------------- linear systems in the plane

/** classification of the origin of x′ = Ax from trace and determinant (numbers with exact signs) */
function classify(tr, det, disc) {
  const s = (v) => (v > 0 ? 1 : v < 0 ? -1 : 0);
  if (s(det) < 0) return { kind: "saddle", stability: "unstable" };
  if (s(det) === 0) return { kind: s(tr) === 0 ? "degenerate (zero matrix or shear)" : "line of equilibria", stability: s(tr) < 0 ? "stable, not asymptotically" : "unstable" };
  if (s(disc) < 0) {
    if (s(tr) === 0) return { kind: "centre", stability: "stable, not asymptotically" };
    return { kind: "spiral", stability: s(tr) < 0 ? "asymptotically stable" : "unstable" };
  }
  return { kind: s(disc) === 0 ? "degenerate node" : "node", stability: s(tr) < 0 ? "asymptotically stable" : "unstable" };
}

/**
 * x′ = Ax for a 2×2 rational matrix: { trace, determinant, discriminant,
 * eigenvalues, eigenvectors, kind, stability, exponential, solution(x0) }.
 * `exponential` is e^{At} as four formulas in t. Other sizes go to
 * linearSystemN below (e^{At} by the inverse Laplace transform of (sI − A)⁻¹).
 */
export function linearSystem(matrix, opts = {}) {
  const t = opts.t ?? "t";
  const n = matrix.length;
  if (!n || matrix.some((row) => row.length !== n)) refuse("bad-dimension", "linearSystem needs a square matrix");
  if (n !== 2) return linearSystemN(matrix.map((row) => row.map(qOf)), t, opts);
  const [[a, b], [c, d]] = matrix.map((row) => row.map(qOf));
  const tr = a.add(d);
  const det = a.multiply(d).subtract(b.multiply(c));
  const tau = tr.divide(TWO);
  const delta = tau.multiply(tau).subtract(det); // (tr/2)² − det
  const sg = (v) => (v.numerator > 0n ? 1 : v.numerator < 0n ? -1 : 0);
  const cls = classify(sg(tr), sg(det), sg(delta));
  // a degenerate node that is a multiple of the identity is a star
  if (cls.kind === "degenerate node" && isZero(b) && isZero(c)) cls.kind = "star node";
  const Tv = variable(t);
  const root = (m) => {
    const r = rationalSqrt(m);
    return r ? num(r) : call("sqrt", num(m));
  };
  let Cf;
  let Sf;
  let eigenvalues;
  let eigenvectors = null;
  if (delta.numerator > 0n) {
    const w = root(delta);
    Cf = call("cosh", tidy(mul(w, Tv)));
    Sf = div(call("sinh", tidy(mul(w, Tv))), w);
    eigenvalues = [tidy(sub(num(tau), w)), tidy(add(num(tau), w))];
    eigenvectors = eigenvalues.map((lam) => (isZero(b) ? (isZero(c) ? null : [tidy(sub(lam, num(d))), num(c)]) : [num(b), tidy(sub(lam, num(a)))]));
    if (isZero(b) && isZero(c)) eigenvectors = a.compareTo(d) < 0 ? [[num(1), num(0)], [num(0), num(1)]] : [[num(0), num(1)], [num(1), num(0)]];
  } else if (delta.numerator < 0n) {
    const w = root(delta.negate());
    Cf = call("cos", tidy(mul(w, Tv)));
    Sf = div(call("sin", tidy(mul(w, Tv))), w);
    const wt = F(w);
    const im = `${wt === "1" ? "" : `${wt}*`}i`;
    eigenvalues = isZero(tau) ? [`-${im}`, im] : [`${tau} - ${im}`, `${tau} + ${im}`];
  } else {
    Cf = num(1);
    Sf = Tv;
    eigenvalues = [num(tau), num(tau)];
    eigenvectors = isZero(b) && isZero(c) ? [[num(1), num(0)], [num(0), num(1)]] : [isZero(b) ? [num(0), num(1)] : [num(b), num(tau.subtract(a))]];
  }
  // e^{At} = e^{τt}·(C·I + S·(A − τI))
  const E = isZero(tau) ? null : call("exp", tidy(mul(num(tau), Tv)));
  const withE = (x) => tidy(E ? mul(E, x) : x);
  const N = [[a.subtract(tau), b], [c, d.subtract(tau)]];
  let exponential = N.map((row, i) => row.map((e, j) => withE(add(i === j ? Cf : num(0), mul(num(e), Sf)))));
  if (delta.numerator > 0n) {
    // two real eigenvalues: e^{At} = ((A − λ₂I)·e^{λ₁t} − (A − λ₁I)·e^{λ₂t})/(λ₁ − λ₂)
    const w = root(delta);
    const [l2, l1] = eigenvalues;
    const e1 = call("exp", tidy(mul(l1, Tv)));
    const e2 = call("exp", tidy(mul(l2, Tv)));
    const M = [[a, b], [c, d]];
    exponential = M.map((row, i) => row.map((e, j) => tidy(div(sub(mul(sub(num(e), i === j ? l2 : num(0)), e1), mul(sub(num(e), i === j ? l1 : num(0)), e2)), mul(num(2), w)))));
  }
  const txt = (v) => (typeof v === "string" ? v : F(v));
  return {
    matrix: [[a, b], [c, d]],
    trace: tr,
    determinant: det,
    discriminant: tr.multiply(tr).subtract(det.multiply(Q(4))),
    eigenvalues: eigenvalues.map(txt),
    eigenvectors: eigenvectors && eigenvectors.map((vec) => vec && vec.map(txt)),
    kind: cls.kind === "node" || cls.kind === "spiral" || cls.kind === "degenerate node" || cls.kind === "star node" ? `${cls.stability === "unstable" ? "unstable" : "stable"} ${cls.kind}` : cls.kind,
    stability: cls.stability,
    exponential: exponential.map((row) => row.map(F)),
    /** the solution with x(0) = x0, as two formulas in t */
    solution(x0) {
      const v0 = x0.map(A);
      return exponential.map((row) => F(tidy(add(mul(row[0], v0[0]), mul(row[1], v0[1])))));
    },
  };
}

/** rank of a rational matrix */
function rankQ(M) {
  const R = M.map((r) => [...r]);
  let rank = 0;
  const cols = R[0]?.length ?? 0;
  for (let c = 0; c < cols && rank < R.length; c++) {
    const p = R.findIndex((r, i) => i >= rank && !isZero(r[c]));
    if (p < 0) continue;
    [R[rank], R[p]] = [R[p], R[rank]];
    for (let i = 0; i < R.length; i++) {
      if (i === rank || isZero(R[i][c])) continue;
      const f = R[i][c].divide(R[rank][c]);
      R[i] = R[i].map((v, k) => v.subtract(f.multiply(R[rank][k])));
    }
    rank++;
  }
  return rank;
}
const matMulQ = (X, Y) => X.map((r) => Y[0].map((_, j) => r.reduce((acc, v, k) => acc.add(v.multiply(Y[k][j])), ZERO)));
const signOfRoot = (r) => {
  // the sign of the real part of a root from characteristicRoots, exactly
  if (r.kind === "complex") return r.re.numerator > 0n ? 1 : r.re.numerator < 0n ? -1 : 0;
  if (r.value !== null) return r.value.numerator > 0n ? 1 : r.value.numerator < 0n ? -1 : 0;
  // re ± √d with d > 0
  const re = r.re;
  const reSign = re.numerator > 0n ? 1 : re.numerator < 0n ? -1 : 0;
  if (r.sign > 0 && reSign >= 0) return 1;
  if (r.sign < 0 && reSign <= 0) return -1;
  const c = re.multiply(re).compareTo(r.surd);
  return c === 0 ? 0 : c > 0 ? reSign : r.sign;
};

/**
 * x′ = Ax for an n×n rational matrix. e^{At} is the inverse Laplace transform
 * of (sI − A)⁻¹, whose entries come from the Faddeev–LeVerrier recursion:
 * (sI − A)⁻¹ = (Σₖ Mₖ s^{n−k})/p(s). Works when p splits over the rationals
 * into linear factors and quadratics (the inverse transform's condition).
 * `verified` says that d/dt e^{At} = A·e^{At} holds identically and e^{A·0} = I.
 */
function linearSystemN(M, t, opts) {
  const n = M.length;
  const I = M.map((_, i) => M.map((_, j) => (i === j ? ONE : ZERO)));
  // Faddeev–LeVerrier: M_1 = I, c_{n−1} = −tr A; M_k = A M_{k−1} + c_{n−k+1} I, c_{n−k} = −tr(A M_k)/k
  const c = new Array(n + 1).fill(ZERO);
  c[n] = ONE;
  const Ms = [];
  let Mk = M.map((r) => r.map(() => ZERO));
  for (let k = 1; k <= n; k++) {
    Mk = matMulQ(M, Mk).map((r, i) => r.map((v, j) => (i === j ? v.add(c[n - k + 1]) : v)));
    Ms.push(Mk);
    const AM = matMulQ(M, Mk);
    c[n - k] = AM.reduce((acc, r, i) => acc.add(r[i]), ZERO).divide(Q(k)).negate();
  }
  const roots = characteristicRoots(c);
  const exponential = M.map((_, i) =>
    M.map((_, j) => {
      const numer = new Array(n).fill(ZERO);
      Ms.forEach((Mk2, k) => (numer[n - 1 - k] = Mk2[i][j]));
      while (numer.length > 1 && isZero(numer[numer.length - 1])) numer.pop();
      if (numer.every(isZero)) return num(ZERO);
      return inverseRational({ num: numer, den: c }, t, "s").terms;
    }),
  );
  // stability from the real parts of the eigenvalues
  let stability = null;
  if (roots) {
    const signs = roots.map(signOfRoot);
    if (signs.some((x) => x > 0)) stability = "unstable";
    else if (signs.every((x) => x < 0)) stability = "asymptotically stable";
    else {
      // eigenvalues on the imaginary axis: stable when each is semisimple
      let semisimple = true;
      roots.forEach((r, k) => {
        if (signs[k] !== 0 || r.multiplicity === 1) return;
        if (r.kind === "real") semisimple &&= rankQ(M.map((row, i) => row.map((v, j) => (i === j ? v.subtract(r.value) : v)))) === n - r.multiplicity;
        else {
          const w2 = r.im2;
          semisimple &&= rankQ(matMulQ(M, M).map((row, i) => row.map((v, j) => (i === j ? v.add(w2) : v)))) === n - 2 * r.multiplicity;
        }
      });
      stability = semisimple ? "stable, not asymptotically" : "unstable";
    }
  }
  // the certificate: d/dt e^{At} = A·e^{At} identically, and e^{A·0} = I
  let verified = true;
  for (let i = 0; i < n && verified; i++)
    for (let j = 0; j < n && verified; j++) {
      let rhs = num(ZERO);
      for (let k = 0; k < n; k++) if (!isZero(M[i][k])) rhs = add(rhs, mul(num(M[i][k]), exponential[k][j]));
      if (!vanishesIdentically(sub(D(exponential[i][j], t), rhs))) verified = false;
      if (!vanishesIdentically(sub(tidy(subst(exponential[i][j], { [t]: num(ZERO) })), num(i === j ? ONE : ZERO)))) verified = false;
    }
  return {
    matrix: M,
    verified,
    trace: M.reduce((acc, r, i) => acc.add(r[i]), ZERO),
    characteristic: `${polyText(c, "s")} = 0`,
    eigenvalues: roots
      ? roots.flatMap((r) => {
          const texts = r.kind === "complex" ? ["-", "+"].map((sg) => r.text.replace("± ", sg === "-" ? "- " : "+ ").replace(/^([-+]) /, (m, x) => (x === "-" ? "-" : ""))) : [r.text];
          return Array(r.multiplicity).fill(texts).flat();
        })
      : null,
    eigenvectors: null,
    kind: null,
    stability,
    exponential: exponential.map((row) => row.map(F)),
    solution(x0) {
      const v0 = x0.map(A);
      return exponential.map((row) => F(tidy(row.reduce((acc, e, j) => add(acc, mul(e, v0[j])), num(ZERO)))));
    },
  };
}

// ---------------------------------------------------------------- nonlinear systems in the plane

/**
 * x′ = f(x, y), y′ = g(x, y): planarSystem(["y", "-sin(x) - y/2"], ["x", "y"]).
 * Gives the Jacobian, nullclines, certified equilibria with their linear
 * classification, conserved quantities checked by differentiation, and orbits
 * through the validated solver.
 */
export class PlanarSystem {
  constructor(field, variables = ["x", "y"], opts = {}) {
    if (field.length !== 2 || variables.length !== 2) refuse("bad-dimension", "a planar system has two equations in two unknowns");
    this.variables = variables;
    this.params = opts.params ?? {};
    this.f = field.map((c) => tidy(A(c)));
    this.J = this.f.map((c) => variables.map((name) => D(c, name)));
  }
  /** the Jacobian matrix as formulas */
  jacobian() {
    return this.J.map((row) => row.map(F));
  }
  /** the curves where each component vanishes: { x: "f = 0", y: "g = 0" } keyed by variable */
  nullclines() {
    const [x, y] = this.variables;
    return { [x]: `${F(this.f[0])} = 0`, [y]: `${F(this.f[1])} = 0` };
  }
  #env(box, bits) {
    const env = {};
    this.variables.forEach((name, i) => (env[name] = box[i]));
    for (const [k, val] of Object.entries(this.params)) env[k] = ivOf(val, bits);
    return env;
  }
  /**
   * Every equilibrium in the box { x: [a, b], y: [c, d] }, each proven to
   * exist and to be the only one in its small box, with the linearisation
   * there: [{ point, unique, jacobian, trace, determinant, kind, stability,
   * hyperbolic }]. `complete` on the returned array says the rest of the box
   * was proven empty.
   */
  equilibria(region, opts = {}) {
    const bits = bitsForDigits(opts.digits ?? 12) + 24;
    const [xn, yn] = this.variables;
    const start = [xn, yn].map((name) => new Iv(qOf(region[name][0]), qOf(region[name][1])));
    const tol = opts.tol ? qOf(opts.tol) : new Rational(1n, 1n << 30n);
    const found = [];
    let undecided = 0;
    const stack = [start];
    let budget = opts.maxBoxes ?? 20000;
    const evalBox = (asts, box) => asts.map((a) => {
      try {
        return encloseAst(a, this.#env(box, bits), bits);
      } catch {
        return null;
      }
    });
    while (stack.length && budget-- > 0) {
      const box = stack.pop();
      if (found.some((e) => e._box.every((iv, i) => iv.contains(box[i])))) continue;
      const val = evalBox(this.f, box);
      if (val.some((iv) => iv !== null && !iv.containsZero())) continue;
      const width = box[0].width.compareTo(box[1].width) > 0 ? box[0].width : box[1].width;
      // Krawczyk test on a slightly inflated box
      if (val.every((iv) => iv !== null)) {
        const hit = this.#krawczyk(box, bits);
        if (hit) {
          if (!found.some((e) => e._box.every((iv, i) => iv.intersect(hit[i]) !== null))) found.push(this.#describe(hit, bits));
          continue;
        }
      }
      if (width.compareTo(tol) < 0) {
        undecided++;
        continue;
      }
      const k = box[0].width.compareTo(box[1].width) >= 0 ? 0 : 1;
      const mid = box[k].mid;
      const left = box.slice();
      const right = box.slice();
      left[k] = new Iv(box[k].lo, mid);
      right[k] = new Iv(mid, box[k].hi);
      stack.push(left, right);
    }
    const list = found.map(({ _box, ...rest }) => rest);
    list.sort((p, q) => p.point[0].low.compareTo(q.point[0].low) || p.point[1].low.compareTo(q.point[1].low));
    list.complete = stack.length === 0 && undecided === 0;
    return list;
  }
  #krawczyk(box, bits) {
    const inflate = (iv) => {
      const r = iv.width.multiply(new Rational(1n, 8n));
      return new Iv(iv.lo.subtract(r), iv.hi.add(r)).roundOut(bits);
    };
    let Xb = box.map(inflate);
    for (let iter = 0; iter < 12; iter++) {
      const m = Xb.map((iv) => iv.mid);
      let Fm;
      let Jx;
      let Jm;
      try {
        Fm = this.f.map((a) => encloseAst(a, this.#env(m.map((v) => Iv.point(v)), bits), bits));
        Jx = this.J.map((row) => row.map((a) => encloseAst(a, this.#env(Xb, bits), bits)));
        Jm = this.J.map((row) => row.map((a) => encloseAst(a, this.#env(m.map((v) => Iv.point(v)), bits), bits).mid));
      } catch {
        return null;
      }
      const det = Jm[0][0].multiply(Jm[1][1]).subtract(Jm[0][1].multiply(Jm[1][0]));
      if (isZero(det)) return null;
      const Y = [[Jm[1][1].divide(det), Jm[0][1].negate().divide(det)], [Jm[1][0].negate().divide(det), Jm[0][0].divide(det)]];
      // K = m − Y·F(m) + (I − Y·J(X))·(X − m)
      const K = [0, 1].map((i) => {
        let acc = Iv.point(m[i]).sub(Fm[0].scale(Y[i][0]).add(Fm[1].scale(Y[i][1])));
        for (let j = 0; j < 2; j++) {
          const e = Iv.point(i === j ? ONE : ZERO).sub(Jx[0][j].scale(Y[i][0]).add(Jx[1][j].scale(Y[i][1])));
          acc = acc.add(e.mul(Xb[j].sub(Iv.point(m[j]))));
        }
        return acc.roundOut(bits);
      });
      const inside = K.every((iv, i) => iv.lo.compareTo(Xb[i].lo) > 0 && iv.hi.compareTo(Xb[i].hi) < 0);
      if (inside) {
        // contract a few more times
        let cur = K;
        for (let r = 0; r < 6; r++) {
          const nx = this.#krawczykStep(cur, bits);
          if (!nx) break;
          cur = nx;
        }
        return cur;
      }
      const next = K.map((iv, i) => iv.intersect(Xb[i]));
      if (next.some((iv) => iv === null)) return null;
      if (next.every((iv, i) => iv.width.multiply(TWO).compareTo(Xb[i].width) > 0)) return null;
      Xb = next;
    }
    return null;
  }
  #krawczykStep(Xb, bits) {
    const m = Xb.map((iv) => iv.mid);
    try {
      const Fm = this.f.map((a) => encloseAst(a, this.#env(m.map((v) => Iv.point(v)), bits), bits));
      const Jx = this.J.map((row) => row.map((a) => encloseAst(a, this.#env(Xb, bits), bits)));
      const Jm = Jx.map((row) => row.map((iv) => iv.mid));
      const det = Jm[0][0].multiply(Jm[1][1]).subtract(Jm[0][1].multiply(Jm[1][0]));
      if (isZero(det)) return null;
      const Y = [[Jm[1][1].divide(det), Jm[0][1].negate().divide(det)], [Jm[1][0].negate().divide(det), Jm[0][0].divide(det)]];
      const K = [0, 1].map((i) => {
        let acc = Iv.point(m[i]).sub(Fm[0].scale(Y[i][0]).add(Fm[1].scale(Y[i][1])));
        for (let j = 0; j < 2; j++) {
          const e = Iv.point(i === j ? ONE : ZERO).sub(Jx[0][j].scale(Y[i][0]).add(Jx[1][j].scale(Y[i][1])));
          acc = acc.add(e.mul(Xb[j].sub(Iv.point(m[j]))));
        }
        return acc.roundOut(bits);
      });
      const next = K.map((iv, i) => iv.intersect(Xb[i]));
      if (next.some((iv) => iv === null)) return null;
      if (next.every((iv, i) => iv.width.compareTo(Xb[i].width) >= 0)) return null;
      return next;
    } catch {
      return null;
    }
  }
  #describe(box, bits) {
    const Jb = this.J.map((row) => row.map((a) => encloseAst(a, this.#env(box, bits), bits)));
    const tr = Jb[0][0].add(Jb[1][1]);
    const det = Jb[0][0].mul(Jb[1][1]).sub(Jb[0][1].mul(Jb[1][0]));
    const disc = tr.mul(tr).sub(det.scale(Q(4)));
    const sg = (iv) => (iv.lo.numerator > 0n ? 1 : iv.hi.numerator < 0n ? -1 : iv.isPoint ? 0 : null);
    const [st, sd, sc] = [sg(tr), sg(det), sg(disc)];
    let kind = null;
    let stability = null;
    let hyperbolic = null;
    if (sd === -1) [kind, stability, hyperbolic] = ["saddle", "unstable", true];
    else if (sd === 1 && st !== null && st !== 0) {
      hyperbolic = true;
      stability = st < 0 ? "asymptotically stable" : "unstable";
      kind = sc === -1 ? `${st < 0 ? "stable" : "unstable"} spiral` : sc === 1 ? `${st < 0 ? "stable" : "unstable"} node` : `${st < 0 ? "stable" : "unstable"} node or spiral`;
    } else if (sd === 1 && st === null) {
      [kind, stability, hyperbolic] = ["centre or spiral: the trace is not separated from 0", null, null];
    } else if (sd === 1 && st === 0) {
      // the linear part is a centre: the nonlinear terms decide
      [kind, stability, hyperbolic] = ["centre of the linear part (a centre or a weak spiral)", null, false];
    }
    return {
      _box: box,
      point: box.map((iv) => iv.toRationalInterval()),
      unique: true,
      jacobian: Jb.map((row) => row.map((iv) => iv.toRationalInterval())),
      trace: tr.toRationalInterval(),
      determinant: det.toRationalInterval(),
      kind,
      stability,
      hyperbolic,
    };
  }
  /** Whether H(x, y) is constant along every solution: H_x·f + H_y·g ≡ 0. */
  conserves(H) {
    const h = A(H);
    return vanishesIdentically(add(mul(D(h, this.variables[0]), this.f[0]), mul(D(h, this.variables[1]), this.f[1])));
  }
  /** dV/dt along solutions for a candidate Lyapunov function, as a formula */
  along(V) {
    const h = A(V);
    return F(tidy(add(mul(D(h, this.variables[0]), this.f[0]), mul(D(h, this.variables[1]), this.f[1]))));
  }
  /** The orbit from a point: a Refinement like ode.solve (quick preview, exact() validated). */
  orbit({ from, until, ...rest }) {
    return odeSolve({ f: this.f.map(F), vars: this.variables, y0: from, until, params: this.params, ...rest });
  }
}
export function planarSystem(field, variables, opts) {
  return new PlanarSystem(field, variables, opts);
}

// ---------------------------------------------------------------- series solutions

/** the first n+1 Taylor coefficients of N/D about 0, D(0) ≠ 0 */
function seriesOf(N, D0, n) {
  const out = [];
  for (let k = 0; k <= n; k++) {
    let s = N[k] ?? ZERO;
    for (let j = 1; j <= k; j++) s = s.subtract((D0[j] ?? ZERO).multiply(out[k - j]));
    out.push(s.divide(D0[0]));
  }
  return out;
}
/** p(x + c) for a polynomial over Q */
const shiftPoly = (p, c) => {
  let out = [ZERO];
  for (let k = p.length - 1; k >= 0; k--) out = P.add(P.mul(out, [c, ONE]), [p[k]]);
  return out;
};
const seriesText = (coeffs, x, r) => {
  const parts = [];
  coeffs.forEach((c, k) => {
    if (isZero(c)) return;
    const X = variable(x);
    const m = k === 0 ? num(c) : mul(num(c), k === 1 ? X : pw(X, num(k)));
    parts.push(m);
  });
  const body = F(sumAst(parts.map(tidy)));
  if (isZero(r)) return `${body} + …`;
  const lead = r.equals(ONE) ? x : `${x}^(${r})`;
  return `${lead}*(${body} + …)`;
};

/**
 * Series solutions of y″ + p(x)·y′ + q(x)·y = 0 about a point, for rational
 * functions p and q: at an ordinary point the two power series with
 * (y, y′) = (1, 0) and (0, 1); at a regular singular point the Frobenius
 * series for each exponent that yields one.
 *
 * Returns { about, kind, indicial, exponents, solutions: [{ exponent,
 * coefficients, text, remainder, enclose }], notes, radius, provenRadius }.
 * Coefficients are exact.
 *
 * Each solution is (x − c)^r·g(x) with g the power series listed. Its
 * `remainder(ρ)` gives a proven bound for everything the listing leaves out:
 * |g(x) − Σₙ≤N aₙ(x − c)ⁿ| ≤ bound for all complex x with |x − c| ≤ ρ, for any
 * ρ below `provenRadius` (a proven lower bound for the distance to the
 * nearest other singular point). `enclose(x)` is the partial sum at a
 * rational x with that bound on either side.
 */
export function seriesSolution({ p = 0, q = 0, about = 0, order = 8, x = "x" }) {
  const c = qOf(about);
  const read = (e) => {
    const rf = P.rationalFunction(tidy(A(e)), x);
    if (!rf) refuse("no-series", "series solutions here need p and q to be rational functions with rational coefficients");
    const g = P.gcd(rf.num, rf.den);
    return { num: shiftPoly(P.divmod(rf.num, g).quo, c), den: shiftPoly(P.divmod(rf.den, g).quo, c) };
  };
  const pr = read(p);
  const qr = read(q);
  // order of the pole at 0 (after the shift)
  const pole = (r) => {
    let k = 0;
    let d = r.den;
    while (isZero(d[0])) {
      d = d.slice(1);
      k++;
    }
    return { k, den: d };
  };
  const pp = pole(pr);
  const qp = pole(qr);
  const out = { about: c, notes: [], solutions: [] };
  const shiftedX = isZero(c) ? x : `(${x} - ${c})`;
  // distance to the nearest other singular point, estimated from the roots of the denominators
  out.radius = nearestRoot([pp.den, qp.den]);
  const W = [pp.den, qp.den].map(inverseRootBound).reduce((u, v) => (u.compareTo(v) > 0 ? u : v));
  out.provenRadius = isZero(W) ? Infinity : ONE.divide(W);
  const attach = (sol, r, delta, Pnum, Qnum) => {
    const data = { a: sol.coefficients, r, delta, N: order, P: { num: Pnum, den: pp.den }, Q: { num: Qnum, den: qp.den }, R: out.provenRadius };
    sol.remainder = (rho) => seriesTail(data, qOf(rho));
    sol.enclose = (at) => {
      const h = qOf(at).subtract(c);
      let partial = ZERO;
      for (let k = sol.coefficients.length - 1; k >= 0; k--) partial = partial.multiply(h).add(sol.coefficients[k]);
      const bound = isZero(h) ? ZERO : seriesTail(data, h.abs()).bound;
      return { at: qOf(at), partial, bound, low: partial.subtract(bound), high: partial.add(bound), exponent: sol.exponent };
    };
    return sol;
  };
  if (pp.k === 0 && qp.k === 0) {
    out.kind = "ordinary";
    const ps = seriesOf(pr.num, pr.den, order);
    const qs = seriesOf(qr.num, qr.den, order);
    for (const [a0, a1] of [[ONE, ZERO], [ZERO, ONE]]) {
      const a = [a0, a1];
      for (let n = 0; n + 2 <= order; n++) {
        let s = ZERO;
        for (let k = 0; k <= n; k++) s = s.add(ps[k].multiply(Q(n - k + 1)).multiply(a[n - k + 1])).add(qs[k].multiply(a[n - k]));
        a.push(s.negate().divide(Q((n + 2) * (n + 1))));
      }
      // as a Frobenius series with exponent 0: x·p and x²·q, F(n) = n(n − 1)
      out.solutions.push(attach({ exponent: ZERO, coefficients: a, text: seriesText(a, shiftedX, ZERO) }, ZERO, ONE.negate(), [ZERO, ...pr.num], [ZERO, ZERO, ...qr.num]));
    }
    return out;
  }
  if (pp.k > 1 || qp.k > 2) {
    out.kind = "irregular singular";
    out.notes.push("the point is an irregular singular point: the Frobenius method does not apply");
    return out;
  }
  out.kind = "regular singular";
  // x·p and x²·q as power series
  const Pnum = pp.k === 1 ? pr.num : [ZERO, ...pr.num];
  const Qnum = qp.k === 2 ? qr.num : qp.k === 1 ? [ZERO, ...qr.num] : [ZERO, ZERO, ...qr.num];
  const Ps = seriesOf(Pnum, pp.den, order);
  const Qs = seriesOf(Qnum, qp.den, order);
  // r(r − 1) + P0·r + Q0 = 0
  const ind = [Qs[0], Ps[0].subtract(ONE), ONE];
  out.indicial = `${polyText(ind, "r")} = 0`;
  const roots = characteristicRoots(ind);
  if (!roots || roots.some((r) => r.kind !== "real" || r.value === null)) {
    out.exponents = roots ? roots.map((r) => r.text) : null;
    out.notes.push("the exponents are not rational: the series have irrational or complex powers and are not built here");
    return out;
  }
  const rs = roots.flatMap((r) => Array.from({ length: r.multiplicity }, () => r.value)).sort((u, v) => v.compareTo(u));
  out.exponents = rs;
  const indAt = (r) => r.multiply(r.subtract(ONE)).add(Ps[0].multiply(r)).add(Qs[0]);
  const build = (r) => {
    const a = [ONE];
    for (let n = 1; n <= order; n++) {
      let s = ZERO;
      for (let k = 1; k <= n; k++) s = s.add(Ps[k].multiply(r.add(Q(n - k))).add(Qs[k]).multiply(a[n - k]));
      const lead = indAt(r.add(Q(n)));
      if (isZero(lead)) {
        if (!isZero(s)) return null; // a logarithm is needed
        a.push(ZERO);
      } else a.push(s.negate().divide(lead));
    }
    return a;
  };
  // F(r + n) = n·(n + δ) with δ = F′(r) = 2r − 1 + P₀
  const deltaAt = (r) => r.multiply(TWO).subtract(ONE).add(Ps[0]);
  const first = build(rs[0]);
  out.solutions.push(attach({ exponent: rs[0], coefficients: first, text: seriesText(first, shiftedX, rs[0]) }, rs[0], deltaAt(rs[0]), Pnum, Qnum));
  const gap = rs[0].subtract(rs[1]);
  if (isZero(gap)) out.notes.push("the exponents are equal: the second solution is y₁·log x plus another series");
  else {
    const second = build(rs[1]);
    if (second) out.solutions.push(attach({ exponent: rs[1], coefficients: second, text: seriesText(second, shiftedX, rs[1]) }, rs[1], deltaAt(rs[1]), Pnum, Qnum));
    else out.notes.push(`the exponents differ by the whole number ${gap} and the smaller one needs a logarithm: the second solution is c·y₁·log x plus a series`);
  }
  return out;
}

// ---- a proven remainder ------------------------------------------------------------------------
//
// Write the equation as x²y″ + x·P(x)·y′ + Q(x)·y = 0 with P = Σ Pₖxᵏ and
// Q = Σ Qₖxᵏ. A solution xʳ Σ aₙxⁿ satisfies
//
//   F(r + n)·aₙ = − Σₖ₌₁ⁿ (Pₖ·(r + n − k) + Qₖ)·aₙ₋ₖ,   F(r + n) = n·(n + δ).
//
// P and Q are rational functions N/D. If every root of D has modulus at least
// R then 1/D is majorised by |D(0)|⁻¹(1 − x/R)^(−deg D), so for any s < R,
// |Pₖ| ≤ M_P/sᵏ with M_P the value of the majorant at s (and likewise M_Q).
// Put bₙ = |aₙ|sⁿ and cⱼ = M_P(|r| + j) + M_Q. Then
//
//   n(n + δ)·bₙ ≤ Sₙ := Σⱼ<ₙ cⱼbⱼ   and   Sₙ₊₁ ≤ Sₙ·(1 + εₙ),  εₙ = cₙ/(n(n + δ)),
//
// with εₙ decreasing once n > max(0, −δ). S_(N+1) is known exactly from the
// coefficients computed, so for |x| ≤ ρ < s, with t = ρ/s and ε = ε_(N+1),
//
//   Σₙ>N |aₙ|ρⁿ ≤ S_(N+1)·t^(N+1) / ((N + 1)(N + 1 + δ)(1 − (1 + ε)t))
//
// whenever (1 + ε)t < 1. Everything is rational arithmetic.

const lnBig = (n) => {
  if (n < 0n) n = -n;
  if (n === 0n) return -Infinity;
  const bits = n.toString(2).length;
  const shift = Math.max(0, bits - 53);
  return Math.log(Number(n >> BigInt(shift))) + shift * Math.LN2;
};
const lnQ = (q) => lnBig(q.numerator) - lnBig(q.denominator);
const powQ = (q, n) => { let r = ONE; let b = q; let e = n; while (e > 0) { if (e & 1) r = r.multiply(b); b = b.multiply(b); e >>= 1; } return r; };
/** a rational at least x, with about `digits` significant digits */
function roundUp(x, digits = 3) {
  if (isZero(x)) return ZERO;
  const e = Math.floor(lnQ(x) / Math.LN10);
  const k = digits - 1 - e;
  const scale = k >= 0 ? new Rational(10n ** BigInt(k)) : new Rational(1n, 10n ** BigInt(-k));
  return new Rational(x.multiply(scale).ceil()).divide(scale);
}
/**
 * A rational W with 1/|ζ| ≤ W for every root ζ of the polynomial d (d(0) ≠ 0),
 * so that d has no root of modulus below 1/W. Zero for a constant. Graeffe's
 * root squaring is applied to the reversed polynomial and Fujiwara's bound to
 * the result, which loses at most a factor 2^(1/64).
 */
function inverseRootBound(d) {
  let e = [...d];
  while (e.length > 1 && isZero(e[e.length - 1])) e.pop();
  const m = e.length - 1;
  if (m < 1) return ZERO;
  e.reverse(); // roots are now the reciprocals 1/ζ
  let steps = 0;
  while (steps < 6) {
    const size = e.reduce((s, v) => Math.max(s, v.numerator.toString(2).length + v.denominator.toString(2).length), 0);
    if (size > 6000) break;
    const flipped = e.map((v, k) => (k % 2 ? v.negate() : v));
    const prod = P.mul(e, flipped);
    e = Array.from({ length: m + 1 }, (_, k) => prod[2 * k] ?? ZERO);
    // clear a common scale so the numbers stay as small as they can
    const lead = e[m];
    e = e.map((v) => v.divide(lead));
    steps += 1;
  }
  const pow = 2 ** steps;
  const ratios = [];
  for (let k = 1; k <= m; k++) ratios.push(e[m - k].divide(e[m]).abs());
  let ln = -Infinity;
  ratios.forEach((q, i) => { if (!isZero(q)) ln = Math.max(ln, (Math.LN2 + lnQ(q) / (i + 1)) / pow); });
  if (ln === -Infinity) return ZERO;
  // a rational a little above exp(ln), then checked exactly: W^(pow·k) ≥ 2ᵏ·|e_(m−k)/e_m|
  let w = Math.exp(ln) * (1 + 1e-9);
  for (let tries = 0; tries < 60; tries++) {
    const digits = 12 - Math.floor(Math.log10(w));
    const scale = digits >= 0 ? 10n ** BigInt(digits) : 1n;
    const W = digits >= 0 ? new Rational(BigInt(Math.ceil(w * Number(scale))), scale) : new Rational(BigInt(Math.ceil(w)));
    const ok = ratios.every((q, i) => isZero(q) || powQ(W, pow * (i + 1)).compareTo(q.multiply(powQ(TWO, i + 1))) >= 0);
    if (ok) return W;
    w *= 1 + 1e-7;
  }
  refuse("no-series", "could not prove a bound for the singular points of this equation");
}
const TAIL_FROM = 120;
/**
 * A proven M with |cₖ|·sᵏ ≤ M for every k ≥ 1, where N/D = Σ cₖxᵏ. The first
 * TAIL_FROM coefficients are used exactly; the rest are bounded through the
 * majorant |D(0)|⁻¹(1 − x/R)^(−deg D) of 1/D, whose coefficients times sʲ
 * decrease once j is large. Null when s is too close to R for that.
 */
function supBound(fn, s, R) {
  const { num: N, den } = fn;
  let m = den.length - 1;
  while (m > 0 && isZero(den[m])) m--;
  const L = Math.max(TAIL_FROM, N.length + 1);
  fn.series ??= seriesOf(N, den, L - 1);
  let M = ZERO;
  let sp = ONE;
  for (let k = 1; k < L; k++) {
    sp = sp.multiply(s);
    if (isZero(fn.series[k])) continue;
    const v = roundUp(fn.series[k].abs().multiply(sp), 6);
    if (v.compareTo(M) > 0) M = v;
  }
  if (m === 0) return M; // a polynomial: nothing beyond its degree
  const j0 = L - (N.length - 1);
  const ratio = s.divide(R);
  if (Q(j0 + m, j0 + 1).multiply(ratio).compareTo(ONE) >= 0) return null;
  let binom = ONE; // C(j0 + m − 1, m − 1)
  for (let i = 1; i <= m - 1; i++) binom = binom.multiply(Q(j0 + i, i));
  let top = ZERO;
  for (let k = N.length - 1; k >= 0; k--) top = top.multiply(s).add(N[k].abs());
  const tail = roundUp(top.multiply(binom).multiply(powQ(ratio, j0)).divide(den[0].abs()), 6);
  return tail.compareTo(M) > 0 ? tail : M;
}
function seriesTail({ a, r, delta, N, P: Pd, Q: Qd, R }, rho) {
  if (rho.compareTo(ZERO) <= 0) refuse("no-series", "the radius has to be positive");
  if (R !== Infinity && rho.compareTo(R) >= 0) refuse("no-series", `a remainder is proven only inside the disc of radius ${Number(R.toNumber().toPrecision(6))}, short of the nearest singular point`);
  if (Q(N + 1).add(delta).compareTo(ZERO) <= 0) refuse("no-series", "take more terms: the remainder bound starts past the difference of the exponents");
  const absR = r.abs();
  const candidates = [];
  if (R === Infinity) for (let j = 1; j <= 6; j++) candidates.push(rho.multiply(powQ(TWO, j)));
  else {
    for (let j = 1; j <= 7; j++) {
      const s = roundUp(rho.add(R.subtract(rho).multiply(Q(j, 8))), 4);
      if (s.compareTo(rho) > 0 && s.compareTo(R) < 0) candidates.push(s);
    }
  }
  let best = null;
  for (const s of candidates) {
    const MP = supBound(Pd, s, R);
    const MQ = supBound(Qd, s, R);
    if (!MP || !MQ) continue;
    const cAt = (j) => MP.multiply(absR.add(Q(j))).add(MQ);
    const t = rho.divide(s);
    // S = S_(N+1) = Σⱼ≤N cⱼ|aⱼ|sʲ, exactly
    let S = ZERO;
    let sp = ONE;
    for (let j = 0; j <= N; j++) {
      if (!isZero(a[j])) S = S.add(cAt(j).multiply(a[j].abs()).multiply(sp));
      sp = sp.multiply(s);
    }
    S = roundUp(S, 15);
    // step forward until the ratio (1 + εₙ)t is safely below 1, then sum a geometric series
    const target = ONE.add(t).divide(TWO);
    let n = N + 1;
    let tn = roundUp(powQ(t, n), 15);
    let acc = ZERO;
    let B = null;
    for (let step = 0; step < 400; step++) {
      const lead = Q(n).multiply(Q(n).add(delta));
      const eps = cAt(n).divide(lead);
      const ratio = ONE.add(eps).multiply(t);
      if (ratio.compareTo(target) <= 0) {
        B = acc.add(S.multiply(tn).divide(lead.multiply(ONE.subtract(ratio))));
        break;
      }
      acc = roundUp(acc.add(S.multiply(tn).divide(lead)), 15);
      S = roundUp(S.multiply(ONE.add(eps)), 15);
      tn = roundUp(tn.multiply(t), 15);
      n += 1;
    }
    if (B && (!best || B.compareTo(best) < 0)) best = B;
  }
  if (!best) refuse("no-series", `no remainder could be proven out to radius ${rho}: take a smaller radius`);
  const bound = roundUp(best);
  return { radius: rho, terms: N + 1, bound, approx: bound.toNumber(), text: `for |x| ≤ ${rho} from the centre, the terms beyond degree ${N} add up to at most ${bound.toNumber().toExponential(2)}` };
}

/** smallest modulus of a root of any of the polynomials (floating point; Infinity when there are none) */
function nearestRoot(polys) {
  let best = Infinity;
  for (const p of polys) {
    const n = p.length - 1;
    if (n < 1) continue;
    const cf = p.map((c) => c.toNumber());
    // Durand–Kerner
    let zs = Array.from({ length: n }, (_, k) => [0.4 * Math.cos(2.1 * k + 0.3) + 0.5, 0.9 * Math.sin(2.1 * k + 0.3)]);
    const ev = ([re, im]) => {
      let a = [0, 0];
      for (let k = n; k >= 0; k--) a = [a[0] * re - a[1] * im + cf[k], a[0] * im + a[1] * re];
      return a;
    };
    for (let it = 0; it < 200; it++) {
      zs = zs.map((z, i) => {
        let den = [cf[n], 0];
        zs.forEach((w, j) => {
          if (j === i) return;
          const d = [z[0] - w[0], z[1] - w[1]];
          den = [den[0] * d[0] - den[1] * d[1], den[0] * d[1] + den[1] * d[0]];
        });
        const f = ev(z);
        const m = den[0] * den[0] + den[1] * den[1] || 1e-300;
        return [z[0] - (f[0] * den[0] + f[1] * den[1]) / m, z[1] - (f[1] * den[0] - f[0] * den[1]) / m];
      });
    }
    for (const z of zs) best = Math.min(best, Math.hypot(z[0], z[1]));
  }
  return best;
}
