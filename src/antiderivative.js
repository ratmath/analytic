// A small antiderivative engine for the formulas a course in differential
// equations meets: polynomials, rational functions by partial fractions,
// exponentials and sines of linear arguments (alone, with polynomial factors
// and with each other), and one level of substitution.
//
// Nothing is returned unless differentiating it gives the integrand back:
// `proven` when the difference tidies to zero, `checked` when the two agree
// at sample points to rounding. The full engine is in @ratmath/symbolic; this
// one exists so that the solution methods here can show their integrals.
import { Rational } from "@ratmath/core";
import { ZERO, ONE, TWO, isZero } from "./rat.js";
import { format, derivative, constantRational, freeVariables, compileFloat, num, v as variable, op, call } from "./expr.js";
import { tidy, vanishesIdentically } from "./tidy.js";
import * as P from "./rpoly.js";

const add = (a, b) => op("+", a, b);
const sub = (a, b) => op("-", a, b);
const mul = (a, b) => op("*", a, b);
const div = (a, b) => op("/", a, b);
const pw = (a, b) => op("^", a, b);
const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const has = (ast, name) => freeVariables(ast).has(name);
const subst = (ast, map) => {
  if (ast.type === "var") return map[ast.name] ?? ast;
  if (ast.args) return { ...ast, args: ast.args.map((a) => subst(a, map)) };
  return ast;
};
const replaceTree = (ast, key, by) => {
  if (format(ast) === key) return by;
  if (ast.args) return { ...ast, args: ast.args.map((a) => replaceTree(a, key, by)) };
  return ast;
};

/** a sum written with minus signs where a term is a negation */
export function sumAst(list) {
  let out = null;
  for (const t of list) {
    const c = constantRational(t);
    if (c !== null && isZero(c)) continue;
    const negative = t.type === "op" && t.op === "neg";
    const lead = t.type === "op" && t.op === "*" && t.args[0].type === "num" && t.args[0].value.numerator < 0n;
    if (out === null) out = t;
    else if (negative) out = sub(out, t.args[0]);
    else if (lead) out = sub(out, t.args[0].value.equals(Q(-1)) ? t.args[1] : mul(num(t.args[0].value.negate()), t.args[1]));
    else out = add(out, t);
  }
  return out ?? num(0);
}
export { terms as additiveTerms };

// ---- polynomials over Q in one letter -------------------------------------------------------

const polyAst = (p, x) => {
  let out = null;
  for (let k = p.length - 1; k >= 0; k--) {
    if (isZero(p[k])) continue;
    const m = k === 0 ? num(p[k]) : mul(num(p[k]), k === 1 ? x : pw(x, num(k)));
    out = out ? add(out, m) : m;
  }
  return out ?? num(0);
};
const isqrtBig = (n) => {
  if (n < 0n) return null;
  if (n < 2n) return n;
  let r = BigInt(Math.floor(Math.sqrt(Number(n))));
  while (r * r > n) r--;
  while ((r + 1n) * (r + 1n) <= n) r++;
  return r * r === n ? r : null;
};
/** the square root of a rational when it is rational, else null */
export function rationalSqrt(c) {
  if (c.numerator < 0n) return null;
  const a = isqrtBig(c.numerator);
  const b = isqrtBig(c.denominator);
  return a === null || b === null ? null : new Rational(a, b);
}
function divisors(n) {
  if (n < 0n) n = -n;
  const out = [];
  if (n > 10n ** 12n) return null;
  const lim = Number(n);
  for (let i = 1; i * i <= lim; i++) {
    if (lim % i === 0) {
      out.push(BigInt(i));
      if (i * i !== lim) out.push(BigInt(lim / i));
    }
  }
  return out;
}
/** rational roots of a polynomial over Q, with multiplicity: [{ root, multiplicity }], and what is left */
export function rationalRoots(p) {
  let rest = P.trim(p.slice());
  const roots = [];
  const bump = (r) => {
    const hit = roots.find((x) => x.root.equals(r));
    if (hit) hit.multiplicity++;
    else roots.push({ root: r, multiplicity: 1 });
  };
  while (P.deg(rest) >= 1 && isZero(rest[0])) {
    bump(ZERO);
    rest = rest.slice(1);
  }
  for (let guard = 0; guard < 64 && P.deg(rest) >= 1; guard++) {
    // whole coefficients
    let lcm = 1n;
    const g = (a, b) => {
      while (b) [a, b] = [b, a % b];
      return a < 0n ? -a : a;
    };
    for (const c of rest) lcm = (lcm * c.denominator) / g(lcm, c.denominator);
    const ints = rest.map((c) => (c.numerator * lcm) / c.denominator);
    const ps = divisors(ints[0]);
    const qs = divisors(ints[ints.length - 1]);
    if (!ps || !qs) break;
    let found = null;
    outer: for (const a of ps) for (const b of qs) for (const s of [1n, -1n]) {
      const r = new Rational(s * a, b);
      if (isZero(P.evaluate(rest, r))) {
        found = r;
        break outer;
      }
    }
    if (found === null) break;
    bump(found);
    rest = P.divmod(rest, [found.negate(), ONE]).quo;
  }
  return { roots, rest };
}

/** solve the square system M·x = b exactly; null when singular */
export function solveLinear(M, b) {
  const n = b.length;
  const A = M.map((row, i) => [...row, b[i]]);
  for (let c = 0; c < n; c++) {
    let piv = -1;
    for (let r = c; r < n; r++) if (!isZero(A[r][c])) {
      piv = r;
      break;
    }
    if (piv < 0) return null;
    [A[c], A[piv]] = [A[piv], A[c]];
    const inv = A[c][c].reciprocal();
    A[c] = A[c].map((x) => x.multiply(inv));
    for (let r = 0; r < n; r++) {
      if (r === c || isZero(A[r][c])) continue;
      const f = A[r][c];
      A[r] = A[r].map((x, j) => x.subtract(f.multiply(A[c][j])));
    }
  }
  return A.map((row) => row[n]);
}

/**
 * Partial fractions of N/D over the rationals:
 *   { poly, linear: [{ root, power, coeff }], quadratic: [{ p, q, alpha, beta }] }
 * meaning poly(x) + Σ coeff/(x − root)^power + Σ (alpha·x + beta)/(x² + p·x + q),
 * each quadratic without rational roots and to the first power. null when the
 * denominator does not split that far.
 */
export function partialFractions(N, D) {
  const lead = D[D.length - 1];
  D = P.scale(D, lead.reciprocal());
  N = P.scale(N, lead.reciprocal());
  const g = P.gcd(N, D);
  if (P.deg(g) >= 1) {
    N = P.divmod(N, g).quo;
    D = P.monic(P.divmod(D, g).quo);
    N = P.scale(N, ONE); // already consistent: both divided by the same monic g
  }
  const { quo, rem } = P.divmod(N, D);
  const { roots, rest } = rationalRoots(D);
  const quads = [];
  const r = P.monic(rest);
  if (P.deg(r) === 2) quads.push({ p: r[1], q: r[0] });
  else if (P.deg(r) === 4 && isZero(r[1]) && isZero(r[3])) {
    // even quartic: a quadratic in x²
    const { roots: zr, rest: zrest } = rationalRoots([r[0], r[2], ONE]);
    if (P.deg(zrest) >= 1) return null;
    for (const z of zr) for (let i = 0; i < z.multiplicity; i++) quads.push({ p: ZERO, q: z.root.negate() });
    if (quads.length === 2 && quads[0].q.equals(quads[1].q)) return null;
  } else if (P.deg(r) >= 1) return null;
  // unknowns: one per (root, power), two per quadratic
  const unknowns = [];
  for (const { root, multiplicity } of roots) for (let k = 1; k <= multiplicity; k++) unknowns.push({ kind: "linear", root, power: k });
  for (const qd of quads) unknowns.push({ kind: "alpha", qd }, { kind: "beta", qd });
  const n = P.deg(D);
  if (unknowns.length !== n) return null;
  // each unknown multiplies the polynomial D / (its denominator)
  const columns = unknowns.map((u) => {
    if (u.kind === "linear") {
      let den = [ONE];
      for (let i = 0; i < u.power; i++) den = P.mul(den, [u.root.negate(), ONE]);
      return P.divmod(D, den).quo;
    }
    const base = P.divmod(D, [u.qd.q, u.qd.p, ONE]).quo;
    return u.kind === "alpha" ? P.mul(base, [ZERO, ONE]) : base;
  });
  const M = Array.from({ length: n }, (_, i) => columns.map((c) => c[i] ?? ZERO));
  const b = Array.from({ length: n }, (_, i) => rem[i] ?? ZERO);
  const sol = n ? solveLinear(M, b) : [];
  if (!sol) return null;
  const linear = [];
  const quadratic = quads.map((qd) => ({ ...qd, alpha: ZERO, beta: ZERO }));
  unknowns.forEach((u, i) => {
    if (u.kind === "linear") linear.push({ root: u.root, power: u.power, coeff: sol[i] });
    else quadratic[quads.indexOf(u.qd)][u.kind] = sol[i];
  });
  return { poly: quo, linear: linear.filter((t) => !isZero(t.coeff)), quadratic: quadratic.filter((t) => !isZero(t.alpha) || !isZero(t.beta)) };
}

function integrateRational(ast, name) {
  const rf = P.rationalFunction(ast, name);
  if (!rf || P.deg(rf.den) < 1) return null;
  const pf = partialFractions(rf.num, rf.den);
  if (!pf) return null;
  const x = variable(name);
  const parts = [];
  if (!P.isZeroPoly(pf.poly)) parts.push(polyAst(pf.poly.map((c, k) => c.divide(Q(k + 1))).reduce((acc, c) => [...acc, c], [ZERO]), x));
  for (const t of pf.linear) {
    const u = isZero(t.root) ? x : sub(x, num(t.root));
    if (t.power === 1) parts.push(mul(num(t.coeff), call("log", call("abs", u))));
    else parts.push(div(num(t.coeff.divide(Q(1 - t.power))), pw(u, num(t.power - 1))));
  }
  for (const t of pf.quadratic) {
    const quad = add(add(pw(x, num(2)), mul(num(t.p), x)), num(t.q));
    if (!isZero(t.alpha)) parts.push(mul(num(t.alpha.divide(TWO)), call("log", call("abs", quad))));
    const k = t.beta.subtract(t.alpha.multiply(t.p).divide(TWO));
    if (isZero(k)) continue;
    const c = t.q.subtract(t.p.multiply(t.p).divide(Q(4)));
    const shifted = isZero(t.p) ? x : add(x, num(t.p.divide(TWO)));
    if (c.numerator > 0n) {
      const r = rationalSqrt(c);
      const root = r ? num(r) : call("sqrt", num(c));
      parts.push(mul(div(num(k), root), call("atan", div(shifted, root))));
    } else {
      const m = c.negate();
      const r = rationalSqrt(m);
      const root = r ? num(r) : call("sqrt", num(m));
      parts.push(mul(div(num(k), mul(num(2), root)), call("log", call("abs", div(sub(shifted, root), add(shifted, root))))));
    }
  }
  return parts.length ? parts.reduce(add) : num(0);
}

// ---- products of a polynomial, an exponential and a sine or cosine ---------------------------

/** a·x + b with rational a ≠ 0, else null */
function linearIn(ast, name) {
  const rf = P.rationalFunction(ast, name);
  if (!rf || P.deg(rf.den) !== 0 || P.deg(rf.num) !== 1) return null;
  return { a: rf.num[1].divide(rf.den[0]), b: rf.num[0].divide(rf.den[0]) };
}
/**
 * Reads a term as c · x^k · exp(a·x) · (cos | sin)(w·x) with rational a, w and
 * whole k: { c, k, a, w, trig: "cos" | "sin" | null }, or null. A constant
 * phase or shift is not accepted (tidy has usually expanded it already).
 */
export function expTrigTerm(ast, name) {
  let c = ONE;
  let k = 0;
  let a = ZERO;
  let w = null;
  let trig = null;
  const eat = (t, sign) => {
    const cr = constantRational(t);
    if (cr !== null) {
      c = sign > 0 ? c.multiply(cr) : c.divide(cr);
      return !isZero(cr);
    }
    if (t.type === "op" && t.op === "neg") {
      c = c.negate();
      return eat(t.args[0], sign);
    }
    if (t.type === "op" && t.op === "*") return eat(t.args[0], sign) && eat(t.args[1], sign);
    if (t.type === "op" && t.op === "/") return eat(t.args[0], sign) && eat(t.args[1], -sign);
    if (t.type === "var" && t.name === name) {
      k += sign;
      return true;
    }
    if (t.type === "op" && t.op === "^") {
      const e = constantRational(t.args[1]);
      if (e !== null && e.denominator === 1n && t.args[0].type === "var" && t.args[0].name === name) {
        k += sign * Number(e.numerator);
        return true;
      }
      if (e !== null && e.denominator === 1n && t.args[0].type === "call" && t.args[0].name === "exp") {
        const lin = linearIn(t.args[0].args[0], name);
        if (!lin || !isZero(lin.b)) return false;
        a = a.add(lin.a.multiply(e).multiply(Q(sign)));
        return true;
      }
      return false;
    }
    if (t.type === "call" && t.name === "exp") {
      const lin = linearIn(t.args[0], name);
      if (!lin || !isZero(lin.b)) return false;
      a = a.add(lin.a.multiply(Q(sign)));
      return true;
    }
    if (t.type === "call" && (t.name === "sin" || t.name === "cos") && sign > 0 && trig === null) {
      const lin = linearIn(t.args[0], name);
      if (!lin || !isZero(lin.b)) return false;
      trig = t.name;
      w = lin.a;
      return true;
    }
    return false;
  };
  if (!eat(ast, 1) || k < 0) return null;
  if (trig && w.numerator < 0n) {
    w = w.negate();
    if (trig === "sin") c = c.negate();
  }
  return { c, k, a, w: w ?? ZERO, trig };
}
/** the tree of x^k·exp(a·x)·trig(w·x) */
export function expTrigAst({ k, a, w, trig }, name) {
  const x = variable(name);
  let t = null;
  const put = (f) => (t = t ? mul(t, f) : f);
  if (k > 0) put(k === 1 ? x : pw(x, num(k)));
  if (!isZero(a)) put(call("exp", a.equals(ONE) ? x : mul(num(a), x)));
  if (trig) put(call(trig, w.equals(ONE) ? x : mul(num(w), x)));
  return t ?? num(1);
}
/**
 * In the space spanned by x^j e^{ax} cos(wx), x^j e^{ax} sin(wx) (j ≤ K),
 * differentiation is a matrix. Coordinates are [cos_0, sin_0, cos_1, sin_1, …]
 * (only cos_j when w = 0). Returns that matrix (column = image of a basis vector).
 */
export function expTrigDerivativeMatrix(K, a, w) {
  const two = !isZero(w);
  const size = (K + 1) * (two ? 2 : 1);
  const M = Array.from({ length: size }, () => new Array(size).fill(ZERO));
  const idx = (j, s) => (two ? 2 * j + s : j);
  for (let j = 0; j <= K; j++) {
    for (const s of two ? [0, 1] : [0]) {
      const col = idx(j, s);
      // d/dx x^j e^{ax} T = j x^{j-1} e^{ax} T + a x^j e^{ax} T + x^j e^{ax} T'
      if (j > 0) M[idx(j - 1, s)][col] = M[idx(j - 1, s)][col].add(Q(j));
      M[idx(j, s)][col] = M[idx(j, s)][col].add(a);
      if (two) {
        // cos' = −w sin, sin' = w cos
        if (s === 0) M[idx(j, 1)][col] = M[idx(j, 1)][col].add(w.negate());
        else M[idx(j, 0)][col] = M[idx(j, 0)][col].add(w);
      }
    }
  }
  return M;
}
function integrateExpTrig(ast, name) {
  const t = expTrigTerm(ast, name);
  if (!t || (isZero(t.a) && !t.trig)) return null;
  const two = !isZero(t.w);
  const M = expTrigDerivativeMatrix(t.k, t.a, t.w);
  const b = new Array(M.length).fill(ZERO);
  b[two ? 2 * t.k + (t.trig === "sin" ? 1 : 0) : t.k] = t.c;
  const sol = solveLinear(M, b);
  if (!sol) return null;
  let out = null;
  sol.forEach((coef, i) => {
    if (isZero(coef)) return;
    const j = two ? Math.floor(i / 2) : i;
    const trig = two ? (i % 2 ? "sin" : "cos") : null;
    const term = mul(num(coef), expTrigAst({ k: j, a: t.a, w: t.w, trig }, name));
    out = out ? add(out, term) : term;
  });
  return out ?? num(0);
}

// ---- the engine ----------------------------------------------------------------------------

const TABLE = {
  exp: (u) => call("exp", u),
  sin: (u) => op("neg", call("cos", u)),
  cos: (u) => call("sin", u),
  tan: (u) => op("neg", call("log", call("abs", call("cos", u)))),
  sinh: (u) => call("cosh", u),
  cosh: (u) => call("sinh", u),
  log: (u) => sub(mul(u, call("log", u)), u),
  ln: (u) => sub(mul(u, call("log", u)), u),
  atan: (u) => sub(mul(u, call("atan", u)), mul(num(Q(1, 2)), call("log", add(num(1), pw(u, num(2)))))),
};

function terms(ast) {
  if (ast.type === "op" && ast.op === "+") return [...terms(ast.args[0]), ...terms(ast.args[1])];
  if (ast.type === "op" && ast.op === "-") return [...terms(ast.args[0]), ...terms(ast.args[1]).map((t) => op("neg", t))];
  if (ast.type === "op" && ast.op === "neg") return terms(ast.args[0]).map((t) => op("neg", t));
  // a sum over a constant denominator
  if (ast.type === "op" && ast.op === "/" && constantRational(ast.args[1]) !== null) return terms(ast.args[0]).map((t) => div(t, ast.args[1]));
  return [ast];
}
/** split a product into the part free of the variable and the rest */
function splitConstant(ast, name) {
  if (!has(ast, name)) return [ast, num(1)];
  if (ast.type === "op" && ast.op === "neg") {
    const [c, r] = splitConstant(ast.args[0], name);
    return [op("neg", c), r];
  }
  if (ast.type === "op" && ast.op === "*") {
    const [c1, r1] = splitConstant(ast.args[0], name);
    const [c2, r2] = splitConstant(ast.args[1], name);
    return [mul(c1, c2), mul(r1, r2)];
  }
  if (ast.type === "op" && ast.op === "/") {
    const [c1, r1] = splitConstant(ast.args[0], name);
    const [c2, r2] = splitConstant(ast.args[1], name);
    return [div(c1, c2), div(r1, r2)];
  }
  return [num(1), ast];
}

function one(term, name, depth) {
  const x = variable(name);
  if (!has(term, name)) return mul(term, x);
  const [c, body0] = splitConstant(term, name);
  const body = tidy(body0);
  const scale = (r) => (r === null ? null : terms(r).map((t) => mul(c, t)).reduce(add));
  if (!has(body, name)) return mul(mul(c, body), x);
  // x^n
  if (body.type === "var") return scale(div(pw(x, num(2)), num(2)));
  if (body.type === "op" && body.op === "^" && body.args[0].type === "var" && !has(body.args[1], name)) {
    const e = constantRational(body.args[1]);
    if (e !== null && e.equals(Q(-1))) return scale(call("log", call("abs", x)));
    const e1 = tidy(add(body.args[1], num(1)));
    return scale(div(pw(x, e1), e1));
  }
  const rational = integrateRational(body, name);
  if (rational) return scale(rational);
  const et = integrateExpTrig(body, name);
  if (et) return scale(et);
  // f(a·x + b) from the table
  if (body.type === "call" && body.args.length === 1 && TABLE[body.name]) {
    const lin = linearIn(body.args[0], name);
    if (lin) return scale(div(TABLE[body.name](body.args[0]), num(lin.a)));
  }
  // (a·x + b)^n
  if (body.type === "op" && body.op === "^" && !has(body.args[1], name)) {
    const lin = linearIn(body.args[0], name);
    const e = constantRational(body.args[1]);
    if (lin && e !== null) {
      if (e.equals(Q(-1))) return scale(div(call("log", call("abs", body.args[0])), num(lin.a)));
      return scale(div(pw(body.args[0], num(e.add(ONE))), num(lin.a.multiply(e.add(ONE)))));
    }
  }
  // sin², cos² of a linear argument
  if (body.type === "op" && body.op === "^" && constantRational(body.args[1])?.equals(TWO) && body.args[0].type === "call" && (body.args[0].name === "sin" || body.args[0].name === "cos")) {
    const u = body.args[0].args[0];
    const lin = linearIn(u, name);
    if (lin) {
      const s2 = div(call("sin", mul(num(2), u)), num(lin.a.multiply(Q(4))));
      return scale(body.args[0].name === "sin" ? sub(div(x, num(2)), s2) : add(div(x, num(2)), s2));
    }
  }
  if (body.type === "call" && body.name === "sqrt") {
    const lin = linearIn(body.args[0], name);
    if (lin) return scale(div(pw(body.args[0], num(Q(3, 2))), num(lin.a.multiply(Q(3, 2)))));
  }
  // substitution u = g(x) for g an inner piece of the term
  if (depth < 2) {
    const candidates = new Map();
    const collect = (t) => {
      if (t.type === "call") {
        candidates.set(format(t), t);
        for (const a of t.args) if (a.type !== "var" && has(a, name)) candidates.set(format(a), a);
      }
      if (t.type === "op" && t.op === "^" && t.args[0].type !== "var" && has(t.args[0], name)) candidates.set(format(t.args[0]), t.args[0]);
      if (t.type === "op" && t.op === "/" && t.args[1].type !== "var" && has(t.args[1], name)) candidates.set(format(t.args[1]), t.args[1]);
      if (t.args) t.args.forEach(collect);
    };
    collect(body);
    for (const [key, g] of candidates) {
      const dg = tidy(derivative(g, name));
      if (vanishesIdentically(dg)) continue;
      const quotient = tidy(div(body, dg));
      const inU = replaceTree(quotient, key, variable("u_"));
      if (has(inU, name)) continue;
      const inner = go(inU, "u_", depth + 1);
      if (inner) return scale(subst(inner, { u_: g }));
    }
  }
  return null;
}
function go(ast, name, depth) {
  const parts = terms(tidy(ast));
  let out = null;
  for (const t of parts) {
    const r = one(t, name, depth);
    if (r === null) return null;
    out = out ? add(out, r) : r;
  }
  return out;
}

/**
 * An antiderivative of the tree in `name`, or null. The result is
 * { tree, trust } with trust "proven" (its derivative minus the integrand
 * tidies to zero) or "checked" (they agree at sample points).
 */
export function antiderivative(ast, name = "x") {
  const f = tidy(ast);
  if (vanishesIdentically(f)) return { tree: num(0), trust: "proven" };
  let F;
  try {
    F = go(f, name, 0);
  } catch {
    return null;
  }
  if (F === null) return null;
  F = sumAst(terms(F).map((t) => tidy(t)));
  const diff = sub(derivative(F, name), f);
  if (vanishesIdentically(diff)) return { tree: F, trust: "proven" };
  // sample points: the difference must vanish to rounding wherever both are defined
  try {
    const d = compileFloat(diff);
    const others = [...freeVariables(diff)].filter((n) => n !== name);
    let seen = 0;
    for (const x0 of [0.37, 1.13, 2.71, -0.53, -1.9, 4.2, 0.08, 7.3]) {
      const env = { [name]: x0 };
      others.forEach((n, i) => (env[n] = 0.61 + 0.37 * i));
      const val = d(env);
      if (!Number.isFinite(val)) continue;
      const size = Math.abs(compileFloat(f)(env)) + 1;
      if (Math.abs(val) > 1e-8 * size) return null;
      seen++;
    }
    return seen >= 4 ? { tree: F, trust: "checked" } : null;
  } catch {
    return null;
  }
}
