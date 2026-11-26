// The theorems of vector calculus as checked statements.
//
// Green's theorem, Stokes' theorem and the divergence theorem each say that
// two integrals are equal. Here both are enclosed by certified integration,
// independently: one over the region, the other over its boundary, which is
// built piece by piece from the description of the region. The theorem holds,
// so the two enclosures must meet; `agree` reports that they do. Change of
// variables shows its Jacobian, potentials are found and verified, and the
// candidates of Lagrange's method are certified critical points of the
// Lagrangian.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, toQ, lt, gt } from "./rat.js";
import { toAst, format, derivative, simplify, freeVariables, constantRational, num, v as variable, op, call, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { field, ScalarField, divergence, curl, lineIntegral } from "./multi.js";

const A = (x) => (typeof x === "number" ? num(toRational(x)) : typeof x === "bigint" || x instanceof Rational ? num(toQ(x)) : toAst(x));
const subst = (ast, map) => {
  if (ast.type === "var") return map[ast.name] ?? ast;
  if (ast.args) return { ...ast, args: ast.args.map((a) => subst(a, map)) };
  return ast;
};
const D = (ast, name) => simplify(derivative(ast, name));
const add = (a, b) => op("+", a, b);
const sub = (a, b) => op("-", a, b);
const mul = (a, b) => op("*", a, b);
const isZero = (ast) => {
  const c = constantRational(simplify(ast));
  return c !== null && c.numerator === 0n;
};
const meet = (a, b) => {
  const lo = gt(a.low, b.low) ? a.low : b.low;
  const hi = lt(a.high, b.high) ? a.high : b.high;
  return gt(lo, hi) ? null : new RationalInterval(lo, hi);
};
const total = (ivs) => {
  let s = Iv.point(ZERO);
  for (const iv of ivs) s = s.add(Iv.from(iv));
  return s.toRationalInterval();
};
const bounds = (region, names) => names.map((name) => {
  const b = region[name];
  if (!Array.isArray(b) || b.length !== 2) refuse("bad-region", `the region needs ${name}: [low, high]`);
  return [A(b[0]), A(b[1])];
});
const fmtRegion = (names, bs) => Object.fromEntries(names.map((name, i) => [name, bs[i].map((b) => constantRational(b) ?? format(b))]));
const T = variable("t");
/** from + (to − from)·t */
const along = (from, to) => simplify(add(from, mul(sub(to, from), T)));
const report = (statement, left, right) => {
  const overlap = meet(left.value, right.value);
  return { statement, left, right, agree: overlap !== null, overlap };
};

/**
 * The four sides of { u: [a, b], v: [lo(u), hi(u)] } in order, counter-
 * clockwise, each as { name, u, v } with u and v formulas in t on [0, 1].
 */
function sides(names, bs) {
  const [u, v] = names;
  const [[a, b], [lo, hi]] = bs;
  const at = (g, x) => simplify(subst(g, { [u]: x }));
  const out = [];
  const bottomU = along(a, b);
  out.push({ name: `${v} = ${format(lo)}`, u: bottomU, v: at(lo, bottomU) });
  out.push({ name: `${u} = ${format(b)}`, u: b, v: along(at(lo, b), at(hi, b)) });
  const topU = along(b, a);
  out.push({ name: `${v} = ${format(hi)}, backwards`, u: topU, v: at(hi, topU) });
  out.push({ name: `${u} = ${format(a)}, downwards`, u: a, v: along(at(hi, a), at(lo, a)) });
  // a side of no length (the two bounds meet there) contributes nothing
  return out.filter((s) => !(isZero(D(s.u, "t")) && isZero(D(s.v, "t"))));
}

/**
 * Green's theorem on the region { x: [a, b], y: [lo(x), hi(x)] }:
 *
 *     ∮ P dx + Q dy  =  ∬ (∂Q/∂x − ∂P/∂y) dA,
 *
 * the boundary taken counter-clockwise. Returns { statement, left, right,
 * agree, overlap }: `left` is the circulation with one enclosure per side,
 * `right` the double integral, each with `value` a RationalInterval.
 * With { flux: true }, the normal form ∮ F·n ds = ∬ div F dA.
 */
export function greens(F, variables, region, opts = {}) {
  if (F.length !== 2 || variables.length !== 2) refuse("bad-dimension", "Green's theorem needs two components and two variables");
  const [x, y] = variables;
  const bs = bounds(region, variables);
  const digits = opts.digits ?? 8;
  const [P, Q] = F.map(A);
  // flux form: ∮ F·n ds = ∮ P dy − Q dx, which is the circulation of (−Q, P)
  const G = opts.flux ? [op("neg", Q), P] : [P, Q];
  const pieces = sides(variables, bs).map((s) => ({
    side: s.name,
    curve: { [x]: format(s.u), [y]: format(s.v) },
    value: lineIntegral(G, variables, { [x]: format(s.u), [y]: format(s.v) }, [0, 1], { digits: digits + 1 }).exact(),
  }));
  const inside = opts.flux ? divergence([P, Q], variables) : curl([P, Q], variables);
  const double = inside.integral(fmtRegion(variables, bs), { digits }).exact();
  return report(
    opts.flux ? "∮ F·n ds = ∬ div F dA" : "∮ P dx + Q dy = ∬ (∂Q/∂x − ∂P/∂y) dA",
    { name: opts.flux ? "flux out through the boundary" : "circulation around the boundary", value: total(pieces.map((p) => p.value)), pieces },
    { name: opts.flux ? "integral of the divergence" : "integral of the curl", integrand: inside, value: double },
  );
}

/**
 * Stokes' theorem on the surface r(u, v), (u, v) in { u: [a, b], v: [lo(u), hi(u)] }:
 *
 *     ∮ F·dr  =  ∬ (curl F)·(r_u × r_v) du dv,
 *
 * the boundary being the image of the boundary of the parameter region,
 * counter-clockwise in the (u, v) plane.
 */
export function stokes(F, variables, surface, parameters, region, opts = {}) {
  if (F.length !== 3 || variables.length !== 3 || parameters.length !== 2) refuse("bad-dimension", "Stokes' theorem needs three components, three variables and two parameters");
  const digits = opts.digits ?? 6;
  const bs = bounds(region, parameters);
  const r = variables.map((name) => A(surface[name]));
  const pieces = sides(parameters, bs).map((s) => {
    const curve = Object.fromEntries(variables.map((name, i) => [name, format(simplify(subst(r[i], { [parameters[0]]: s.u, [parameters[1]]: s.v })))]));
    return { side: s.name, curve, value: lineIntegral(F.map(A), variables, curve, [0, 1], { digits: digits + 1 }).exact() };
  });
  const C = curl(F.map(A), variables);
  const ru = r.map((c) => D(c, parameters[0]));
  const rv = r.map((c) => D(c, parameters[1]));
  const normal = [sub(mul(ru[1], rv[2]), mul(ru[2], rv[1])), sub(mul(ru[2], rv[0]), mul(ru[0], rv[2])), sub(mul(ru[0], rv[1]), mul(ru[1], rv[0]))].map(simplify);
  const onSurface = Object.fromEntries(variables.map((name, i) => [name, r[i]]));
  const integrand = simplify(C.map((c, i) => mul(subst(c.ast, onSurface), normal[i])).reduce(add));
  const flux = new ScalarField(integrand, parameters).integral(fmtRegion(parameters, bs), { digits }).exact();
  return report(
    "∮ F·dr = ∬ (curl F)·n dS",
    { name: "circulation around the boundary", value: total(pieces.map((p) => p.value)), pieces },
    { name: "flux of the curl through the surface", curl: C, normal: normal.map(format), integrand: format(integrand), value: flux },
  );
}

/**
 * The divergence theorem on the solid
 * { x: [a, b], y: [c(x), d(x)], z: [e(x, y), f(x, y)] }:
 *
 *     ∯ F·n dS  =  ∭ div F dV,
 *
 * n pointing outward. The surface is the top, the bottom and up to four
 * walls, each integrated separately. With { surface: [...] } the closed
 * surface is given instead, as pieces { r: { x, y, z }, parameters: [u, v],
 * region, orientation: 1 | -1 } where orientation says whether r_u × r_v
 * points outward.
 */
export function divergenceTheorem(F, variables, solid, opts = {}) {
  if (F.length !== 3 || variables.length !== 3) refuse("bad-dimension", "the divergence theorem needs three components and three variables");
  const digits = opts.digits ?? 5;
  const [x, y, z] = variables;
  const bs = bounds(solid, variables);
  const [[a, b], [c, d], [e, f]] = bs;
  const Fa = F.map(A);
  const pieces = [];
  const face = (name, names, at, normal, region) => {
    const integrand = simplify(Fa.map((comp, i) => mul(subst(comp, at), normal[i])).reduce(add));
    // a face of no height, or one the field does not cross
    const flat = isZero(sub(region[1][1], region[1][0])) || isZero(sub(region[0][1], region[0][0]));
    const value = flat || isZero(integrand) ? new RationalInterval(ZERO, ZERO) : new ScalarField(integrand, names).integral(fmtRegion(names, region), { digits: digits + 1 }).exact();
    pieces.push({ face: name, integrand: format(integrand), value });
  };
  if (opts.surface) {
    for (const piece of opts.surface) {
      const ps = piece.parameters;
      const r = variables.map((name) => A(piece.r[name]));
      const ru = r.map((comp) => D(comp, ps[0]));
      const rv = r.map((comp) => D(comp, ps[1]));
      const s = num(piece.orientation === -1 ? -1 : 1);
      const normal = [sub(mul(ru[1], rv[2]), mul(ru[2], rv[1])), sub(mul(ru[2], rv[0]), mul(ru[0], rv[2])), sub(mul(ru[0], rv[1]), mul(ru[1], rv[0]))].map((n) => simplify(mul(s, n)));
      face(piece.name ?? `piece ${pieces.length + 1}`, ps, Object.fromEntries(variables.map((name, i) => [name, r[i]])), normal, bounds(piece.region, ps));
    }
  } else {
    const one = num(1);
    const zero = num(0);
    const neg = (t) => simplify(op("neg", t));
    const onY = (g, yv) => simplify(subst(g, { [y]: yv }));
    const onX = (g, xv) => simplify(subst(g, { [x]: xv }));
    face(`top, ${z} = ${format(f)}`, [x, y], { [z]: f }, [neg(D(f, x)), neg(D(f, y)), one], [[a, b], [c, d]]);
    face(`bottom, ${z} = ${format(e)}`, [x, y], { [z]: e }, [D(e, x), D(e, y), num(-1)], [[a, b], [c, d]]);
    face(`wall ${y} = ${format(d)}`, [x, z], { [y]: d }, [neg(D(d, x)), one, zero], [[a, b], [onY(e, d), onY(f, d)]]);
    face(`wall ${y} = ${format(c)}`, [x, z], { [y]: c }, [D(c, x), num(-1), zero], [[a, b], [onY(e, c), onY(f, c)]]);
    face(`wall ${x} = ${format(b)}`, [y, z], { [x]: b }, [one, zero, zero], [[onX(c, b), onX(d, b)], [onX(e, b), onX(f, b)]]);
    face(`wall ${x} = ${format(a)}`, [y, z], { [x]: a }, [num(-1), zero, zero], [[onX(c, a), onX(d, a)], [onX(e, a), onX(f, a)]]);
  }
  const div = divergence(Fa, variables);
  const inside = isZero(div.ast) ? new RationalInterval(ZERO, ZERO) : div.integral(fmtRegion(variables, bs), { digits }).exact();
  return report(
    "∯ F·n dS = ∭ div F dV",
    { name: "flux out through the surface", value: total(pieces.map((p) => p.value)), pieces },
    { name: "integral of the divergence", integrand: div, value: inside },
  );
}

/**
 * Change of variables in a double or triple integral, with the Jacobian as a
 * visible step:
 *
 *     ∫ f(x) dx over T(S)  =  ∫ f(T(u))·|det T′(u)| du over S.
 *
 * `map` gives each old variable in terms of the new ones, `region` is S.
 * Returns { jacobian, determinant, factor, integrand, value } and, when
 * `original` (the region T(S) in the old variables) is given, also `direct`
 * and `agree`. The sign of the determinant on S is proven before the
 * absolute value is dropped.
 */
export function changeOfVariables(f, variables, map, newVariables, region, opts = {}) {
  const n = variables.length;
  if (newVariables.length !== n || (n !== 2 && n !== 3)) refuse("bad-dimension", "change of variables is for two or three variables, with as many new ones");
  const digits = opts.digits ?? 8;
  const Tm = variables.map((name) => A(map[name]));
  const J = Tm.map((row) => newVariables.map((u) => D(row, u)));
  const det = tidy(simplify(
    n === 2
      ? sub(mul(J[0][0], J[1][1]), mul(J[0][1], J[1][0]))
      : add(sub(mul(J[0][0], sub(mul(J[1][1], J[2][2]), mul(J[1][2], J[2][1]))), mul(J[0][1], sub(mul(J[1][0], J[2][2]), mul(J[1][2], J[2][0])))), mul(J[0][2], sub(mul(J[1][0], J[2][1]), mul(J[1][1], J[2][0])))),
  ), newVariables);
  const bs = bounds(region, newVariables);
  const S = fmtRegion(newVariables, bs);
  // one sign on the whole region lets |det| be written without the bars
  let sign = 0;
  try {
    const range = new ScalarField(det, newVariables).range(S, { digits: 4 }).exact();
    sign = range.low.numerator >= 0n ? 1 : range.high.numerator <= 0n ? -1 : 0;
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
  }
  const factor = simplify(sign > 0 ? det : sign < 0 ? op("neg", det) : call("abs", det));
  const integrand = simplify(mul(tidy(subst(A(f), Object.fromEntries(variables.map((name, i) => [name, Tm[i]]))), newVariables), factor));
  const value = new ScalarField(integrand, newVariables).integral(S, { digits }).exact();
  const out = {
    jacobian: J.map((row) => row.map(format)),
    determinant: format(det),
    sign: sign > 0 ? "positive on the region" : sign < 0 ? "negative on the region" : "not of one sign on the region: the absolute value is kept",
    factor: format(factor),
    integrand: format(integrand),
    value,
  };
  if (opts.original) {
    out.direct = field(A(f), variables).integral(opts.original, { digits: opts.directDigits ?? Math.min(digits, 5) }).exact();
    out.overlap = meet(out.direct, value);
    out.agree = out.overlap !== null;
  }
  return out;
}

// ---- potentials -------------------------------------------------------------------------------

/** A polynomial with rational coefficients as Map "e1,e2,…" → coefficient; null when the tree is not one. */
function polyOf(ast, names) {
  const k = (e) => e.join(",");
  const one = (e) => new Map([[k(e), ONE]]);
  const zeroE = names.map(() => 0);
  const addP = (p, r, s = ONE) => {
    const out = new Map(p);
    for (const [key, c] of r) {
      const t = (out.get(key) ?? ZERO).add(c.multiply(s));
      if (t.numerator === 0n) out.delete(key);
      else out.set(key, t);
    }
    return out;
  };
  const mulP = (p, r) => {
    let out = new Map();
    for (const [k1, c1] of p) for (const [k2, c2] of r) {
      const e1 = k1.split(",").map(Number);
      const e2 = k2.split(",").map(Number);
      out = addP(out, new Map([[k(e1.map((x, i) => x + e2[i])), c1.multiply(c2)]]));
    }
    return out;
  };
  const go = (t) => {
    if (t.type === "num") return t.value.numerator === 0n ? new Map() : new Map([[k(zeroE), t.value]]);
    if (t.type === "var") {
      const i = names.indexOf(t.name);
      return i < 0 ? null : one(zeroE.map((_, j) => (j === i ? 1 : 0)));
    }
    if (t.type !== "op") return null;
    const a = t.args.map(go);
    if (a.some((p) => p === null)) return null;
    switch (t.op) {
      case "+": return addP(a[0], a[1]);
      case "-": return addP(a[0], a[1], ONE.negate());
      case "neg": return addP(new Map(), a[0], ONE.negate());
      case "*": return mulP(a[0], a[1]);
      case "/": {
        const c = constantRational(t.args[1]);
        return c === null || c.numerator === 0n ? null : addP(new Map(), a[0], c.reciprocal());
      }
      case "^": {
        const c = constantRational(t.args[1]);
        if (c === null || c.denominator !== 1n || c.numerator < 0n || c.numerator > 40n) return null;
        let out = one(zeroE);
        for (let i = 0n; i < c.numerator; i++) out = mulP(out, a[0]);
        return out;
      }
    }
    return null;
  };
  return go(ast);
}
function polyAst(p, names) {
  const terms = [...p].sort((s, t) => (s[0] < t[0] ? 1 : -1)).map(([key, c]) => {
    const e = key.split(",").map(Number);
    let m = null;
    e.forEach((d, i) => {
      if (!d) return;
      const f = d === 1 ? variable(names[i]) : op("^", variable(names[i]), num(d));
      m = m ? mul(m, f) : f;
    });
    return m === null ? num(c) : c.equals(ONE) ? m : mul(num(c), m);
  });
  return terms.length ? simplify(terms.reduce(add)) : num(0);
}

/**
 * The tree as a polynomial in its variables and in its function calls, each
 * call (sin(x*y), exp(z)) standing as one more letter: { poly, names, back }.
 * Two trees with the same polynomial are identical as functions.
 */
function kernelPoly(ast, variables) {
  const kernels = new Map();
  const hide = (t) => {
    if (t.type === "call") {
      const key = format(t);
      if (!kernels.has(key)) kernels.set(key, { name: `k${kernels.size}_`, tree: t });
      return variable(kernels.get(key).name);
    }
    return t.args ? { ...t, args: t.args.map(hide) } : t;
  };
  const hidden = hide(ast);
  const names = [...variables, ...[...kernels.values()].map((k) => k.name)];
  const poly = polyOf(hidden, names);
  const back = Object.fromEntries([...kernels.values()].map((k) => [k.name, k.tree]));
  return poly && { poly, names, back, kernels };
}
/** Whether the tree is identically 0, as far as multiplying out shows. */
function vanishes(ast, variables) {
  if (isZero(ast)) return true;
  const k = kernelPoly(ast, variables);
  return k !== null && k.poly.size === 0;
}
/** Multiply out and use sin² = 1 − cos², which is what tidies a polar or spherical Jacobian. */
function tidy(ast, variables) {
  const k = kernelPoly(ast, variables);
  if (!k) return ast;
  let p = k.poly;
  for (const [key, { name, tree }] of k.kernels) {
    if (tree.name !== "sin") continue;
    const cosKey = format(call("cos", tree.args[0]));
    if (!k.kernels.has(cosKey)) continue;
    const si = k.names.indexOf(name);
    const ci = k.names.indexOf(k.kernels.get(cosKey).name);
    void key;
    for (let guard = 0; guard < 64; guard++) {
      const big = [...p].find(([m]) => Number(m.split(",")[si]) >= 2);
      if (!big) break;
      const [m, c] = big;
      const e = m.split(",").map(Number);
      p = new Map(p);
      p.delete(m);
      const put = (ee, cc) => {
        const kk = ee.join(",");
        const t = (p.get(kk) ?? ZERO).add(cc);
        if (t.numerator === 0n) p.delete(kk);
        else p.set(kk, t);
      };
      e[si] -= 2;
      put(e, c);
      const e2 = [...e];
      e2[ci] += 2;
      put(e2, c.negate());
    }
  }
  return simplify(subst(polyAst(p, k.names), k.back));
}

/**
 * Is F a gradient? { conservative, curl, potential, check, witness, value }.
 *
 * conservative is true when every component of the curl simplifies to 0
 * (on a region without holes that is the condition), false when the curl is
 * proven nonzero at a point (`witness`), and null otherwise. For a field
 * with polynomial components, `potential` is φ with ∇φ = F in closed form,
 * and `check` lists ∂φ/∂xᵢ − Fᵢ, each simplified to 0. For any conservative
 * field, value(p, from) encloses φ(p) − φ(from) by the line integral along
 * the straight segment.
 */
export function potential(F, variables, opts = {}) {
  const n = variables.length;
  if (F.length !== n || (n !== 2 && n !== 3)) refuse("bad-dimension", "a potential is looked for in two or three variables");
  const Fa = F.map(A);
  const C = n === 2 ? [curl(Fa, variables)] : curl(Fa, variables);
  const zero = C.every((c) => vanishes(c.ast, variables));
  let witness = null;
  if (!zero) {
    // a rational point where some component of the curl is certainly not 0
    const bits = bitsForDigits(opts.digits ?? 10) + 16;
    outer: for (const base of [[1, 2, 3], [1, 1, 1], [-1, 2, 1], [2, -3, 1], [1, 3, -2]]) {
      const env = Object.fromEntries(variables.map((name, i) => [name, Iv.point(new Rational(BigInt(base[i]), 2n))]));
      for (const c of C) {
        try {
          const val = encloseAst(c.ast, env, bits);
          if (!val.containsZero()) {
            witness = { point: Object.fromEntries(variables.map((name, i) => [name, new Rational(BigInt(base[i]), 2n)])), curl: val.toRationalInterval() };
            break outer;
          }
        } catch (e) {
          if (!(e instanceof AnalyticError)) throw e;
        }
      }
    }
  }
  const conservative = zero ? true : witness ? false : null;
  let phi = null;
  let check = null;
  if (zero) {
    const ps = Fa.map((c) => polyOf(c, variables));
    if (ps.every((p) => p !== null)) {
      // φ(x) = ∫₀¹ F(t·x)·x dt: a term c·x^e of Fᵢ gives c·x^e·xᵢ/(|e| + 1)
      const out = new Map();
      ps.forEach((p, i) => {
        for (const [key, c] of p) {
          const e = key.split(",").map(Number);
          const deg = e.reduce((s, d) => s + d, 0);
          e[i] += 1;
          const k2 = e.join(",");
          const t = (out.get(k2) ?? ZERO).add(c.divide(new Rational(BigInt(deg + 1))));
          if (t.numerator === 0n) out.delete(k2);
          else out.set(k2, t);
        }
      });
      phi = polyAst(out, variables);
      check = variables.map((name, i) => format(simplify(polyAst(polyOf(sub(D(phi, name), Fa[i]), variables), variables))));
    }
  }
  return {
    conservative,
    curl: C.map((c) => format(c.ast)),
    witness,
    potential: phi ? field(phi, variables) : null,
    check,
    /** φ(p) − φ(from), enclosed by ∫ F·dr along the segment. Only meaningful for a conservative field. */
    value(p, from = variables.map(() => 0), o = {}) {
      const P = p.map((c) => A(c));
      const O = from.map((c) => A(c));
      const curve = Object.fromEntries(variables.map((name, i) => [name, format(along(O[i], P[i]))]));
      return lineIntegral(Fa, variables, curve, [0, 1], { digits: o.digits ?? 10 }).exact();
    },
  };
}

// ---- Lagrange multipliers ---------------------------------------------------------------------

/**
 * Extremes of f on the curve or surface g = 0 by Lagrange's method: the
 * points where ∇f = λ·∇g and g = 0, found as the critical points of
 * L = f − λ·g in the variables and λ together. Each candidate is proven to
 * exist in its small box (and to be the only one there).
 *
 * Returns { candidates, max, min, lagrangian }: each candidate is
 * { point, multiplier, value, unique }; max and min are the candidates with
 * the largest and smallest value where the enclosures decide that. They are
 * the extremes on the constraint set when that set is closed and bounded,
 * lies inside the box, and ∇g ≠ 0 on it: those conditions are the theorem's,
 * and are not checked here.
 */
export function lagrange(f, constraint, variables, box, opts = {}) {
  const lam = opts.multiplierName ?? "lambda_";
  const g = A(constraint);
  const L = simplify(sub(A(f), mul(variable(lam), g)));
  for (const name of freeVariables(L)) if (name !== lam && !variables.includes(name)) refuse("unbound", `${name} is not one of the variables`);
  const names = [...variables, lam];
  const region = { ...box, [lam]: opts.multiplier ?? [-16, 16] };
  const found = new ScalarField(L, names).criticalPoints(region, { digits: opts.digits ?? 10, ...(opts.maxBoxes ? { maxBoxes: opts.maxBoxes } : {}) }).exact();
  const candidates = found.map((p) => ({
    point: Object.fromEntries(variables.map((name, i) => [name, p.point[i]])),
    multiplier: p.point[variables.length],
    value: p.value,
    unique: p.unique ?? null,
    proven: p.kind !== "possible",
  }));
  const proven = candidates.filter((c) => c.proven && c.value);
  const above = (c, d) => gt(c.value.low, d.value.high);
  const tops = proven.filter((c) => !proven.some((d) => above(d, c)));
  const bottoms = proven.filter((c) => !proven.some((d) => above(c, d)));
  const hull = (list) => (list.length ? new RationalInterval(list.reduce((m, c) => (lt(c.value.low, m) ? c.value.low : m), list[0].value.low), list.reduce((m, c) => (gt(c.value.high, m) ? c.value.high : m), list[0].value.high)) : null);
  return {
    lagrangian: format(L),
    candidates,
    max: tops.length ? { value: hull(tops), at: tops.map((c) => c.point) } : null,
    min: bottoms.length ? { value: hull(bottoms), at: bottoms.map((c) => c.point) } : null,
    complete: candidates.every((c) => c.proven),
  };
}
