// Exact polynomials over Q (arrays of Rationals, index = power of x):
// division, gcd, square-free (Yun) decomposition, Sturm counts, and reading a
// rational function N/D out of an expression tree.
import { Rational } from "@ratmath/core";
import { ZERO, ONE, isZero, sign } from "./rat.js";
import { trim, add, sub, scale, evaluate, derivative } from "./poly.js";

export { trim, add, sub, scale, evaluate, derivative };

export const deg = (p) => (p.length === 1 && isZero(p[0]) ? -Infinity : p.length - 1);
export const isZeroPoly = (p) => deg(p) === -Infinity;
const lead = (p) => p[p.length - 1];

export function mul(p, q) {
  if (isZeroPoly(p) || isZeroPoly(q)) return [ZERO];
  const r = new Array(p.length + q.length - 1).fill(ZERO);
  for (let i = 0; i < p.length; i++) {
    if (isZero(p[i])) continue;
    for (let j = 0; j < q.length; j++) r[i + j] = r[i + j].add(p[i].multiply(q[j]));
  }
  return trim(r);
}

export function divmod(p, q) {
  if (isZeroPoly(q)) throw new RangeError("division by the zero polynomial");
  let r = trim(p.slice());
  const dq = deg(q);
  if (deg(r) < dq) return { quo: [ZERO], rem: r };
  const quo = new Array(deg(r) - dq + 1).fill(ZERO);
  const lq = lead(q);
  while (!isZeroPoly(r) && deg(r) >= dq) {
    const k = deg(r) - dq;
    const c = lead(r).divide(lq);
    quo[k] = c;
    const next = r.slice();
    for (let j = 0; j <= dq; j++) next[j + k] = next[j + k].subtract(c.multiply(q[j]));
    next.pop(); // leading term cancels exactly
    r = trim(next.length ? next : [ZERO]);
  }
  return { quo: trim(quo), rem: r };
}

export const monic = (p) => (isZeroPoly(p) ? p : scale(p, lead(p).reciprocal()));

export function gcd(p, q) {
  let a = trim(p);
  let b = trim(q);
  while (!isZeroPoly(b)) [a, b] = [b, divmod(a, b).rem];
  return monic(a);
}

/** Yun: p = c · Π a_i^i with a_i square-free and pairwise coprime. → [{ factor, multiplicity }] */
export function squareFree(p) {
  const out = [];
  if (deg(p) < 1) return out;
  let a = gcd(p, derivative(p));
  let b = divmod(p, a).quo;
  let c = divmod(derivative(p), a).quo;
  let d = sub(c, derivative(b));
  for (let i = 1; deg(b) >= 1; i++) {
    a = gcd(b, d);
    if (deg(a) >= 1) out.push({ factor: monic(a), multiplicity: i });
    b = divmod(b, a).quo;
    c = divmod(d, a).quo;
    d = sub(c, derivative(b));
  }
  return out;
}

/** Sturm sequence of a square-free polynomial. */
export function sturm(p) {
  const s = [p, derivative(p)];
  while (deg(s.at(-1)) > 0) {
    const r = divmod(s.at(-2), s.at(-1)).rem;
    if (isZeroPoly(r)) break;
    s.push(scale(r, new Rational(-1n)));
  }
  return s;
}

function variations(seq, x) {
  let v = 0;
  let last = 0;
  for (const p of seq) {
    const s = sign(evaluate(p, x));
    if (s === 0) continue;
    if (last !== 0 && s !== last) v++;
    last = s;
  }
  return v;
}

/** Number of distinct real roots in (a, b] of a square-free p with Sturm sequence seq. */
export const sturmCount = (seq, a, b) => variations(seq, a) - variations(seq, b);

// ---- rational functions from trees -----------------------------------------

const P1 = () => [ONE];

/**
 * { num, den } with num/den equal to the tree as a function of `variable`,
 * or null when the tree is not a rational function with rational
 * coefficients (pi, e, functions, interval parameters, huge degrees).
 */
export function rationalFunction(ast, variable, params = {}, maxDegree = 256) {
  const go = (n) => {
    switch (n.type) {
      case "num":
        return { num: [n.value], den: P1() };
      case "var": {
        if (n.name === variable) return { num: [ZERO, ONE], den: P1() };
        const v = params[n.name];
        return v instanceof Rational ? { num: [v], den: P1() } : null;
      }
      case "op": {
        const [a, b] = n.args.map(go);
        if (!a || (n.op !== "neg" && n.op !== "^" && !b)) return null;
        switch (n.op) {
          case "neg": return { num: scale(a.num, new Rational(-1n)), den: a.den };
          case "+": return { num: add(mul(a.num, b.den), mul(b.num, a.den)), den: mul(a.den, b.den) };
          case "-": return { num: sub(mul(a.num, b.den), mul(b.num, a.den)), den: mul(a.den, b.den) };
          case "*": return { num: mul(a.num, b.num), den: mul(a.den, b.den) };
          case "/":
            if (isZeroPoly(b.num)) return null;
            return { num: mul(a.num, b.den), den: mul(a.den, b.num) };
          case "^": {
            const e = n.args[1];
            if (e.type !== "num" && !(e.type === "op" && e.op === "neg" && e.args[0].type === "num")) return null;
            const q = e.type === "num" ? e.value : e.args[0].value.negate();
            if (q.denominator !== 1n) return null;
            const k = Number(q.numerator);
            if (k === 0 || Math.abs(k) * Math.max(deg(a.num), deg(a.den), 0) > maxDegree) return null;
            let num = P1();
            let den = P1();
            for (let i = 0; i < Math.abs(k); i++) {
              num = mul(num, a.num);
              den = mul(den, a.den);
            }
            return k > 0 ? { num, den } : isZeroPoly(num) ? null : { num: den, den: num };
          }
        }
        return null;
      }
    }
    return null;
  };
  const r = go(ast);
  if (!r || deg(r.num) > maxDegree || deg(r.den) > maxDegree) return null;
  return r;
}
