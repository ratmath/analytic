// Trigonometric polynomials Σ a_k·cos(kφ) + b_k·sin(kφ) with exact rational
// coefficients, read from a formula. Sums, products and whole powers are
// expanded with the product-to-sum identities, so cos(θ)² is 1/2 + cos(2θ)/2.
import { Rational } from "@ratmath/core";
import { ZERO, ONE } from "./rat.js";
import { constantRational } from "./expr.js";

const HALF = new Rational(1n, 2n);
// a trigonometric polynomial: Map k → [a_k, b_k], k ≥ 0
const put = (P, k, a, b) => {
  if (k < 0) {
    k = -k;
    b = b.negate(); // sin(−kφ) = −sin(kφ)
  }
  if (k === 0) b = ZERO;
  const [a0, b0] = P.get(k) ?? [ZERO, ZERO];
  P.set(k, [a0.add(a), b0.add(b)]);
};
const constant = (c) => new Map([[0, [c, ZERO]]]);
const addP = (A, B, sign = 1) => {
  const out = new Map([...A].map(([k, v]) => [k, [...v]]));
  for (const [k, [a, b]] of B) put(out, k, sign > 0 ? a : a.negate(), sign > 0 ? b : b.negate());
  return out;
};
const scaleP = (A, c) => new Map([...A].map(([k, [a, b]]) => [k, [a.multiply(c), b.multiply(c)]]));
function mulP(A, B) {
  const out = new Map();
  for (const [m, [a1, b1]] of A) for (const [n, [a2, b2]] of B) {
    // cos m·cos n = (cos(m−n) + cos(m+n))/2;  sin m·sin n = (cos(m−n) − cos(m+n))/2
    // sin m·cos n = (sin(m+n) + sin(m−n))/2;  cos m·sin n = (sin(m+n) − sin(m−n))/2
    const cc = a1.multiply(a2).multiply(HALF);
    const ss = b1.multiply(b2).multiply(HALF);
    const sc = b1.multiply(a2).multiply(HALF);
    const cs = a1.multiply(b2).multiply(HALF);
    put(out, m - n, cc.add(ss), sc.subtract(cs));
    put(out, m + n, cc.subtract(ss), sc.add(cs));
  }
  return out;
}

/**
 * The formula as a trigonometric polynomial, or null when it is not one with
 * rational coefficients. `modeOf(arg)` gives the whole number k when the
 * argument of a sin or cos is k times the basic angle, else null.
 * → [{ k, a, b }] sorted by k, zero modes dropped.
 */
export function trigPolynomial(ast, modeOf) {
  const go = (t) => {
    const c = constantRational(t);
    if (c !== null) return constant(c);
    if (t.type === "call" && (t.name === "sin" || t.name === "cos")) {
      const k = modeOf(t.args[0]);
      if (k === null) return null;
      const P = new Map();
      put(P, k, t.name === "cos" ? ONE : ZERO, t.name === "sin" ? ONE : ZERO);
      return P;
    }
    if (t.type !== "op") return null;
    const A = go(t.args[0]);
    if (A === null) return null;
    if (t.op === "neg") return scaleP(A, ONE.negate());
    if (t.op === "^") {
      const e = constantRational(t.args[1]);
      if (e === null || e.denominator !== 1n || e.numerator < 0n || e.numerator > 12n) return null;
      let out = constant(ONE);
      for (let i = 0n; i < e.numerator; i++) out = mulP(out, A);
      return out;
    }
    if (t.op === "/") {
      const d = constantRational(t.args[1]);
      return d === null || d.numerator === 0n ? null : scaleP(A, d.reciprocal());
    }
    const B = go(t.args[1]);
    if (B === null) return null;
    if (t.op === "+") return addP(A, B);
    if (t.op === "-") return addP(A, B, -1);
    if (t.op === "*") return mulP(A, B);
    return null;
  };
  const P = go(ast);
  if (P === null) return null;
  return [...P]
    .map(([k, [a, b]]) => ({ k, a, b }))
    .filter((m) => m.a.numerator !== 0n || m.b.numerator !== 0n)
    .sort((x, y) => x.k - y.k);
}
