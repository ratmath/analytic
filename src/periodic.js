// Splitting a sequence with periodic factors into finitely many subsequences.
//
// (−1)^n, cos(πn), sin(πn/2) and the like repeat with a whole period p on the
// whole numbers. Along n = p·m + r each of them is a constant, known exactly,
// so a(p·m + r) is an ordinary formula in m whose limit the asymptotic code
// can find. The limits of the p subsequences are the only accumulation
// points, which gives lim sup and lim inf, and a plain statement that the
// sequence oscillates when they differ.
import { Rational } from "@ratmath/core";
import { ZERO, ONE } from "./rat.js";
import { derivative, simplify, freeVariables, constantRational, num, v as variable, op, call } from "./expr.js";

const PI = { type: "const", name: "pi" };
const depends = (ast, name) => freeVariables(ast).has(name);
const subst = (ast, name, by) => {
  if (ast.type === "var") return ast.name === name ? by : ast;
  if (ast.args) return { ...ast, args: ast.args.map((a) => subst(a, name, by)) };
  return ast;
};
const gcd = (a, b) => (b === 0n ? (a < 0n ? -a : a) : gcd(b, a % b));

/** r with ast = r·π exactly, read from the shape of the tree; null otherwise. */
export function piMultiple(ast) {
  switch (ast.type) {
    case "num":
      return ast.value.numerator === 0n ? ZERO : null;
    case "const":
      return ast.name === "pi" ? ONE : null;
    case "op": {
      const [a, b] = ast.args;
      if (ast.op === "neg") return piMultiple(a)?.negate() ?? null;
      if (ast.op === "+" || ast.op === "-") {
        const [x, y] = [piMultiple(a), piMultiple(b)];
        return x && y ? (ast.op === "+" ? x.add(y) : x.subtract(y)) : null;
      }
      if (ast.op === "*") {
        const [ca, cb] = [constantRational(a), constantRational(b)];
        if (ca !== null) return piMultiple(b)?.multiply(ca) ?? null;
        if (cb !== null) return piMultiple(a)?.multiply(cb) ?? null;
        return null;
      }
      if (ast.op === "/") {
        const cb = constantRational(b);
        if (cb !== null && cb.numerator !== 0n) return piMultiple(a)?.divide(cb) ?? null;
      }
      return null;
    }
  }
  return null;
}

/** u = (s·n + t)·π + c with rational s: { s, rest: u at n = 0 } or null. */
function piLinear(u, n) {
  const d = simplify(derivative(u, n));
  if (depends(d, n)) return null;
  const s = piMultiple(d);
  return s === null ? null : { s };
}
/** u = a·n + b with rational a and constant b (b as a tree). */
function linear(u, n) {
  const a = constantRational(simplify(derivative(u, n)));
  return a === null ? null : { a, b: simplify(subst(u, n, num(ZERO))) };
}

/**
 * The period of the periodic factors of a term on the whole numbers.
 * → { period, parts: number of periodic factors found } or
 *   { period: null, blocker: text } when a sin/cos/tan of the index does not
 *   repeat (sin(n)).
 */
export function periodOf(ast, n) {
  let p = 1n;
  let parts = 0;
  let blocker = null;
  const lcm = (a, b) => (a / gcd(a, b)) * b;
  const walk = (node) => {
    if (!node.args || !depends(node, n)) return;
    if (node.type === "op" && node.op === "^") {
      const [base, e] = node.args;
      const b = constantRational(base);
      if (b !== null && b.numerator < 0n && depends(e, n)) {
        const l = linear(e, n);
        if (l && l.a.denominator === 1n && constantRational(l.b)?.denominator === 1n) {
          parts++;
          if (l.a.numerator % 2n !== 0n) p = lcm(p, 2n);
          return;
        }
      }
    }
    if (node.type === "call" && ["sin", "cos", "tan"].includes(node.name) && depends(node.args[0], n)) {
      const l = piLinear(node.args[0], n);
      if (l) {
        parts++;
        // s·p must be an even whole number
        const den = l.s.denominator * 1n;
        const need = (2n * den) / gcd(l.s.numerator < 0n ? -l.s.numerator : l.s.numerator, 2n * den);
        p = lcm(p, need);
        return;
      }
      // sin(1/n) and the like settle down and are no obstacle; sin(n) is
      const d = simplify(derivative(node.args[0], n));
      const c = constantRational(d);
      if (c !== null && c.numerator !== 0n) blocker ??= `${node.name} of a multiple of the index that is not a rational multiple of pi does not repeat on the whole numbers`;
    }
    node.args.forEach(walk);
  };
  walk(ast);
  if (p > 60n) return { period: null, parts, blocker: `the periodic factors repeat only every ${p} terms, more than the 60 followed here` };
  return { period: Number(p), parts, blocker };
}

const SQ = (k) => call("sqrt", num(new Rational(BigInt(k))));
const half = (t) => op("/", t, num(new Rational(2n)));
/** cos(ρ·π) exactly for ρ with denominator 1, 2, 3, 4 or 6; null otherwise. */
export function cosPi(rho) {
  // reduce to [0, 2)
  const two = new Rational(2n);
  let r = rho.subtract(new Rational(rho.divide(two).floor()).multiply(two));
  // cos(2π − t) = cos t
  if (r.compareTo(ONE) > 0) r = two.subtract(r);
  // now r in [0, 1]; cos(π − t) = −cos t
  let sign = 1;
  if (r.compareTo(new Rational(1n, 2n)) > 0) {
    r = ONE.subtract(r);
    sign = -1;
  }
  const key = r.toString();
  const table = { 0: num(ONE), "1/6": half(SQ(3)), "1/4": half(SQ(2)), "1/3": num(new Rational(1n, 2n)), "1/2": num(ZERO) };
  const t = table[key];
  if (!t) return null;
  if (sign > 0 || key === "1/2") return t;
  return t.type === "num" ? num(t.value.negate()) : op("neg", t);
}

/**
 * The term along n = p·m + r, written in the same variable (so n now counts
 * m), with every periodic factor replaced by its constant value.
 */
export function alongResidue(ast, n, p, r) {
  const P = new Rational(BigInt(p));
  const Rr = new Rational(BigInt(r));
  const shift = op("+", op("*", num(P), variable(n)), num(Rr));
  const go = (node) => {
    if (!node.args || !depends(node, n)) return node;
    if (node.type === "op" && node.op === "^") {
      const [base, e] = node.args;
      const b = constantRational(base);
      if (b !== null && b.numerator < 0n && depends(e, n)) {
        const l = linear(e, n);
        const b0 = l ? constantRational(l.b) : null;
        if (l && l.a.denominator === 1n && b0 !== null && b0.denominator === 1n) {
          // (−c)^(a·n + b) at n = p·m + r: the sign is (−1)^(a·r + b), since a·p is even
          const parity = (l.a.numerator * BigInt(r) + b0.numerator) % 2n !== 0n;
          const mag = b.abs().equals(ONE) ? num(ONE) : op("^", num(b.abs()), e);
          return parity ? op("neg", mag) : mag;
        }
      }
    }
    if (node.type === "call" && ["sin", "cos", "tan"].includes(node.name) && depends(node.args[0], n)) {
      const l = piLinear(node.args[0], n);
      if (l) {
        const u0 = simplify(subst(node.args[0], n, num(Rr)));
        const rho = piMultiple(u0);
        if (rho !== null) {
          const c = cosPi(rho);
          const s = cosPi(rho.subtract(new Rational(1n, 2n))); // sin t = cos(t − π/2)
          if (c && s) {
            if (node.name === "cos") return c;
            if (node.name === "sin") return s;
            if (!(c.type === "num" && c.value.numerator === 0n)) return op("/", s, c);
          }
        }
        return call(node.name, u0);
      }
    }
    return { ...node, args: node.args.map(go) };
  };
  return simplify(subst(go(ast), n, shift));
}
