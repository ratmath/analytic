// Uniform convergence of f_n → f on an interval, decided with a proof.
//
// With g_n = f_n − f and M_n = sup over the interval of |g_n|, the convergence
// is uniform exactly when M_n → 0.
//
// * If g_n is monotone in x on the interval for every n from some n₀ on
//   (∂g/∂x keeps one sign there, shown by a range calculation that carries
//   "n ≥ n₀" and "x in [a, b]" as intervals, the first unbounded), then
//   M_n = max(|g_n(a)|, |g_n(b)|): two ordinary sequences whose limits decide
//   the question either way.
// * Otherwise a bound for every x at once that tends to 0 proves "uniform"
//   (the asymptotic form with x standing for the whole interval), and a
//   witness x_n in the interval along which |g_n(x_n)| does not tend to 0
//   proves "not uniform": the usual choices x_n = a + c/n, b − c/n, c/n.
import { Rational } from "@ratmath/core";
import { ZERO, ONE, lt, le, gt, ge } from "./rat.js";
import { constantRational } from "./expr.js";

// ---- ranges with unbounded ends ---------------------------------------------------------------
// A range is [lo, hi] with lo, hi a Rational or ∓Infinity; it always contains
// every value the expression takes (it may be wider).

const NEG = -Infinity;
const POS = Infinity;
const ALL = [NEG, POS];
const isInf = (x) => x === NEG || x === POS;
const cmp = (a, b) => (a === b ? 0 : a === NEG || b === POS ? -1 : a === POS || b === NEG ? 1 : a.compareTo(b));
const minOf = (...xs) => xs.reduce((m, x) => (cmp(x, m) < 0 ? x : m));
const maxOf = (...xs) => xs.reduce((m, x) => (cmp(x, m) > 0 ? x : m));
const sgn = (x) => (x === POS ? 1 : x === NEG ? -1 : Math.sign(Number(x.numerator)));
const addX = (a, b) => (isInf(a) ? a : isInf(b) ? b : a.add(b)); // never called with opposite infinities
const mulX = (a, b) => {
  const s = sgn(a) * sgn(b);
  if (s === 0) return ZERO; // 0·∞ = 0 here: the factor that is 0 is exactly 0
  if (isInf(a) || isInf(b)) return s > 0 ? POS : NEG;
  return a.multiply(b);
};
const nonneg = (r) => cmp(r[0], ZERO) >= 0;
const nonpos = (r) => cmp(r[1], ZERO) <= 0;
const positive = (r) => cmp(r[0], ZERO) > 0;
const negative = (r) => cmp(r[1], ZERO) < 0;

function mulR(a, b) {
  const c = [mulX(a[0], b[0]), mulX(a[0], b[1]), mulX(a[1], b[0]), mulX(a[1], b[1])];
  return [minOf(...c), maxOf(...c)];
}
function recipR(a, info) {
  if (!positive(a) && !negative(a) && info) info.partial = true; // the denominator may vanish
  if (positive(a)) return [isInf(a[1]) ? ZERO : a[1].reciprocal(), a[0].reciprocal()];
  if (negative(a)) return [a[1].reciprocal(), isInf(a[0]) ? ZERO : a[0].reciprocal()];
  // an end at 0: the reciprocal is unbounded on that side but keeps its sign
  if (nonneg(a) && cmp(a[1], ZERO) > 0) return [isInf(a[1]) ? ZERO : a[1].reciprocal(), POS];
  if (nonpos(a) && cmp(a[0], ZERO) < 0) return [NEG, isInf(a[0]) ? ZERO : a[0].reciprocal()];
  return ALL;
}
function powInt(a, k, info) {
  if (k === 0) return [ONE, ONE];
  if (k < 0) return recipR(powInt(a, -k), info);
  const p = (x) => (isInf(x) ? (x === POS || k % 2 === 0 ? POS : NEG) : x.pow(k));
  if (k % 2 === 1) return [p(a[0]), p(a[1])];
  if (nonneg(a)) return [p(a[0]), p(a[1])];
  if (nonpos(a)) return [p(a[1]), p(a[0])];
  return [ZERO, maxOf(p(a[0]), p(a[1]))];
}

/**
 * The range of a tree when each variable lies in its range in `env`.
 * `info.partial` is set when the tree may be undefined somewhere there (a
 * denominator that may vanish, a root or logarithm of a number that may be
 * negative or 0).
 */
export function rangeOf(ast, env, info = {}) {
  const go = (t) => {
    switch (t.type) {
      case "num":
        return [t.value, t.value];
      case "const":
        return t.name === "pi" ? [new Rational(3n), new Rational(22n, 7n)] : t.name === "e" ? [new Rational(2n), new Rational(3n)] : ALL;
      case "var":
        return env[t.name] ?? ALL;
      case "op": {
        const a = go(t.args[0]);
        if (t.op === "neg") return [isInf(a[1]) ? (a[1] === POS ? NEG : POS) : a[1].negate(), isInf(a[0]) ? (a[0] === NEG ? POS : NEG) : a[0].negate()];
        const b = go(t.args[1]);
        switch (t.op) {
          case "+":
            return [a[0] === NEG || b[0] === NEG ? NEG : addX(a[0], b[0]), a[1] === POS || b[1] === POS ? POS : addX(a[1], b[1])];
          case "-":
            return go({ type: "op", op: "+", args: [t.args[0], { type: "op", op: "neg", args: [t.args[1]] }] });
          case "*":
            return mulR(a, b);
          case "/":
            return mulR(a, recipR(b, info));
          case "^": {
            const k = constantRational(t.args[1]);
            if (k !== null && k.denominator === 1n && k.abs().numerator <= 64n) return powInt(a, Number(k.numerator), info);
            // a real power: defined for a base ≥ 0 (0 only with an exponent ≥ 0)
            if (!nonneg(a)) {
              info.partial = true;
              return ALL;
            }
            if (!positive(a) && !nonneg(b)) info.partial = true; // 0 to a negative power
            if (nonneg(b)) {
              // base in [0, 1] stays in [0, 1]; base ≥ 1 stays ≥ 1
              if (cmp(a[1], ONE) <= 0) return [ZERO, ONE];
              if (cmp(a[0], ONE) >= 0) return [ONE, POS];
              return [ZERO, POS];
            }
            if (nonpos(b)) {
              if (!positive(a)) return [ZERO, POS];
              if (cmp(a[0], ONE) >= 0) return [ZERO, ONE];
              if (cmp(a[1], ONE) <= 0) return [ONE, POS];
            }
            return [ZERO, POS];
          }
        }
        return ALL;
      }
      case "call": {
        const a = go(t.args[0]);
        switch (t.name) {
          case "exp":
            return nonneg(a) ? [ONE, POS] : nonpos(a) ? [ZERO, ONE] : [ZERO, POS];
          case "log":
          case "ln":
            if (!positive(a)) info.partial = true;
            if (!positive(a) && !(nonneg(a) && cmp(a[1], ZERO) > 0)) return ALL;
            return cmp(a[0], ONE) >= 0 ? [ZERO, POS] : cmp(a[1], ONE) <= 0 ? [NEG, ZERO] : ALL;
          case "sqrt":
            if (!nonneg(a)) {
              info.partial = true;
              return ALL;
            }
            return cmp(a[1], ONE) <= 0 ? [ZERO, ONE] : cmp(a[0], ONE) >= 0 ? [ONE, POS] : [ZERO, POS];
          case "abs":
            return nonneg(a) ? a : [ZERO, POS];
          case "sin":
          case "cos":
          case "tanh":
          case "erf":
            return [ONE.negate(), ONE];
          case "atan":
            return nonneg(a) ? [ZERO, new Rational(2n)] : nonpos(a) ? [new Rational(-2n), ZERO] : [new Rational(-2n), new Rational(2n)];
          case "cosh":
            return [ONE, POS];
          case "sinh":
            return nonneg(a) ? [ZERO, POS] : nonpos(a) ? [NEG, ZERO] : ALL;
        }
        info.partial = true; // a function this calculation does not know
        return ALL;
      }
    }
    return ALL;
  };
  return go(ast);
}

/** 1 when the tree is ≥ 0 throughout, −1 when ≤ 0 throughout, 0 when neither is shown. */
export function weakSign(ast, env) {
  const info = {};
  const r = rangeOf(ast, env, info);
  if (info.partial) return 0;
  return nonneg(r) ? 1 : nonpos(r) ? -1 : 0;
}
/** Whether the tree is defined for every value of the variables in `env`, as far as this calculation can show. */
export function definedOn(ast, env) {
  const info = {};
  rangeOf(ast, env, info);
  return !info.partial;
}
export const UNBOUNDED = POS;
