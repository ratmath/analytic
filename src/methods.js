// The classical numerical methods as objects that show their work.
//
// The rest of this library avoids these methods on purpose: it returns proven
// answers. That makes it a good place to study them. Each method here runs
// the way a textbook runs it, in floating point, and keeps its table of
// steps; and because the certified answer is available, the TRUE error of
// every step is shown beside the textbook error estimate.
//
// Floating point itself is a subject: every double is an exact rational, so
// the rounding error of each operation is a number that can be computed
// exactly, not estimated.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, toQ } from "./rat.js";
import { toAst, format, compileFloat, derivative, simplify, freeVariables, constantRational, num, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { fn } from "./fn.js";
import { zeros, extrema } from "./roots.js";
import { quad1 } from "./quad.js";
import { solve as odeSolve } from "./ode.js";
import * as P from "./rpoly.js";
import { solveLinear } from "./antiderivative.js";

const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const qOf = (x) => (x instanceof Rational ? x : typeof x === "string" ? toRational(x) : typeof x === "number" && !Number.isInteger(x) ? exactOf(x) : toQ(x));
const out = (iv) => iv.toRationalInterval();
const absIv = (iv) => (iv.lo.numerator >= 0n ? iv : iv.hi.numerator <= 0n ? iv.neg() : new Iv(ZERO, iv.mag));
const midNumber = (iv) => Iv.from(iv).mid.toNumber();
/** A starting value or bracket end as a float: a JS number as it is, anything exact ("1/2", R`1/2`, 2n) read exactly and rounded once. */
const startOf = (v) => (typeof v === "number" ? v : toQ(v).toNumber());

// ---------------------------------------------------------------- floating point

const view = new DataView(new ArrayBuffer(8));
/** The exact rational value of a double. */
export function exactOf(x) {
  if (!Number.isFinite(x)) refuse("not-finite", "only finite doubles have a rational value");
  if (x === 0) return ZERO;
  view.setFloat64(0, x);
  const hi = view.getUint32(0);
  const lo = view.getUint32(4);
  const sign = hi >>> 31 ? -1n : 1n;
  const e = (hi >>> 20) & 0x7ff;
  let m = (BigInt(hi & 0xfffff) << 32n) | BigInt(lo);
  let exp;
  if (e === 0) exp = -1074; // subnormal
  else {
    m |= 1n << 52n;
    exp = e - 1075;
  }
  return exp >= 0 ? new Rational(sign * m * (1n << BigInt(exp))) : new Rational(sign * m, 1n << BigInt(-exp));
}
/** The double nearest to a rational (ties to even), by exact comparison. */
export function nearestDouble(q) {
  const guess = q.toNumber();
  if (!Number.isFinite(guess)) return guess;
  // toNumber may be off by an ulp for long fractions: compare the neighbours exactly
  let best = guess;
  let bestErr = exactOf(guess).subtract(q).abs();
  for (const cand of [nextUp(guess), nextDown(guess)]) {
    const err = exactOf(cand).subtract(q).abs();
    const c = err.compareTo(bestErr);
    if (c < 0 || (c === 0 && evenMantissa(cand))) {
      best = cand;
      bestErr = err;
    }
  }
  return best;
}
const evenMantissa = (x) => {
  view.setFloat64(0, x);
  return (view.getUint32(4) & 1) === 0;
};
function nextUp(x) {
  if (x === 0) return Number.MIN_VALUE;
  view.setFloat64(0, x);
  let bits = view.getBigUint64(0);
  bits += x > 0 ? 1n : -1n;
  view.setBigUint64(0, bits);
  return view.getFloat64(0);
}
function nextDown(x) {
  return -nextUp(-x);
}

/**
 * A double taken apart: { value, sign, exponent, mantissa, bits, exact, ulp,
 * next, previous }, where `exact` is the rational the double IS and `ulp`
 * the gap to the next double. With a decimal string as the second argument
 * (what was typed), also { intended, error, relativeError }: how far the
 * stored double is from the number that was meant, exactly.
 */
export function floatParts(x, intended) {
  const exact = exactOf(x);
  view.setFloat64(0, x);
  const raw = view.getBigUint64(0);
  const e = Number((raw >> 52n) & 0x7ffn);
  const frac = raw & ((1n << 52n) - 1n);
  const up = nextUp(Math.abs(x));
  const res = {
    value: x,
    sign: x < 0 || Object.is(x, -0) ? -1 : 1,
    /** x = ±mantissa·2^exponent with 1 ≤ mantissa < 2 (0 ≤ mantissa < 1 for subnormals) */
    exponent: e === 0 ? -1022 : e - 1023,
    mantissa: new Rational((e === 0 ? 0n : 1n << 52n) + frac, 1n << 52n),
    bits: raw.toString(2).padStart(64, "0").replace(/^(.)(.{11})(.{52})$/, "$1 $2 $3"),
    exact,
    ulp: exactOf(up).subtract(exactOf(Math.abs(x))),
    next: nextUp(x),
    previous: nextDown(x),
    subnormal: e === 0 && x !== 0,
  };
  if (intended !== undefined) {
    const want = typeof intended === "string" ? toRational(intended) : toQ(intended);
    res.intended = want;
    res.error = exact.subtract(want);
    res.relativeError = want.numerator === 0n ? null : res.error.divide(want).abs();
  }
  return res;
}

/**
 * One floating-point operation examined: floatOp("+", 0.1, 0.2) →
 * { result, exact, error, relativeError, exactlyRepresentable } where `exact`
 * is the true result of the operation on the two doubles (a rational) and
 * `error` what rounding to a double added.
 */
export function floatOp(op, a, b) {
  const [A, B] = [exactOf(a), exactOf(b)];
  let result;
  let exact;
  switch (op) {
    case "+": [result, exact] = [a + b, A.add(B)]; break;
    case "-": [result, exact] = [a - b, A.subtract(B)]; break;
    case "*": [result, exact] = [a * b, A.multiply(B)]; break;
    case "/":
      if (b === 0) refuse("division-by-zero", "division by zero");
      [result, exact] = [a / b, A.divide(B)];
      break;
    default: refuse("bad-operation", "the operation is +, -, * or /");
  }
  const error = exactOf(result).subtract(exact);
  return { result, exact, error, relativeError: exact.numerator === 0n ? null : error.divide(exact).abs(), exactlyRepresentable: error.numerator === 0n };
}

/**
 * A whole calculation followed in doubles and exactly, side by side.
 * roundoff("(1 - cos(x))/x^2", { x: 1e-8 }) → { float, exact, error,
 * relativeError, digitsLost, steps }. The inputs are taken to be the doubles
 * given (their exact rational values); `exact` encloses the true value of
 * the formula at those inputs, and `steps` lists every subexpression with
 * its double, its true value and its relative error, which shows the
 * operation where the digits are lost.
 */
export function roundoff(expression, inputs = {}, opts = {}) {
  const ast = toAst(expression);
  const bits = opts.bits ?? 256;
  const env = {};
  const fenv = {};
  for (const [k, val] of Object.entries(inputs)) {
    const x = typeof val === "number" ? val : nearestDouble(qOf(val));
    fenv[k] = x;
    env[k] = Iv.point(exactOf(x));
  }
  for (const name of freeVariables(ast)) if (!(name in env) && name !== "pi" && name !== "e") refuse("unbound", `${name} has no value`);
  const steps = [];
  const seen = new Set();
  const walk = (node) => {
    if (node.args) node.args.forEach(walk);
    if (node.type === "num" || node.type === "var") return;
    const text = format(node);
    if (seen.has(text)) return;
    seen.add(text);
    const fl = compileFloat(node)(fenv);
    let exact = null;
    let rel = null;
    try {
      exact = encloseAst(node, env, bits);
      if (Number.isFinite(fl)) {
        const err = absIv(Iv.point(exactOf(fl)).sub(exact));
        const size = exact.mig;
        rel = size.numerator === 0n ? null : err.hi.divide(size).toNumber();
      }
    } catch {
      // not defined at these inputs
    }
    steps.push({ expression: text, float: fl, exact: exact && out(exact.roundOut(80)), relativeError: rel });
  };
  walk(ast);
  const last = steps.at(-1) ?? { float: compileFloat(ast)(fenv), exact: out(encloseAst(ast, env, bits)), relativeError: 0 };
  const errorIv = last.exact && Number.isFinite(last.float) ? Iv.point(exactOf(last.float)).sub(Iv.from(last.exact)) : null;
  return {
    float: last.float,
    exact: last.exact,
    error: errorIv && out(errorIv),
    relativeError: last.relativeError,
    /** decimal digits lost out of the 16 a double carries */
    digitsLost: last.relativeError ? Math.max(0, Math.round((Math.log10(last.relativeError) + 15.95) * 10) / 10) : 0,
    steps,
  };
}

// ---------------------------------------------------------------- root finding

function prepare(f, opts) {
  const variable = opts.variable ?? "x";
  const ast = toAst(f);
  return { ast, variable, F: compileFloat(ast), dAst: simplify(derivative(ast, variable)) };
}
/** the certified root nearest to a guess, searched in a bracket around the iterates */
function certifiedRoot(ast, variable, lo, hi, near, digits) {
  try {
    const zs = zeros(ast, [toRational(lo.toFixed(12)), toRational(hi.toFixed(12))], { variable, tolerance: 10 ** -Math.min(digits, 30) }).exact();
    let best = null;
    for (const z of zs) {
      if (z.kind && z.kind !== "zero" && z.kind !== "root" && z.unique === false) continue;
      const mid = (z.lo.toNumber() + z.hi.toNumber()) / 2;
      if (best === null || Math.abs(mid - near) < Math.abs(best.mid - near)) best = { mid, iv: new RationalInterval(z.lo, z.hi) };
    }
    return best && best.iv;
  } catch {
    return null;
  }
}
/** the certified root the iterates are heading for: searched over the span of the last iterates */
function rootNear(ast, variable, rows, opts) {
  const xs = rows.map((r) => r.x).filter(Number.isFinite);
  const last = xs.at(-1);
  const tail = xs.slice(-4);
  const spread = Math.max(...tail) - Math.min(...tail);
  const pad = Math.max(1e-6, 1e-3 * Math.abs(last), 2 * spread);
  return certifiedRoot(ast, variable, last - pad, last + pad, last, opts.digits ?? 25);
}
const trueError = (x, root) => {
  if (!root || !Number.isFinite(x)) return null;
  const e = absIv(Iv.point(exactOf(x)).sub(Iv.from(root)));
  return e.hi.toNumber();
};
/** observed order: log(e_{n+1}/e_n)/log(e_n/e_{n−1}) from the last usable errors */
function observedOrder(errors) {
  const es = errors.filter((e) => e !== null && e > 1e-300);
  const out2 = [];
  for (let i = 2; i < es.length; i++) {
    const p = Math.log(es[i] / es[i - 1]) / Math.log(es[i - 1] / es[i - 2]);
    if (Number.isFinite(p)) out2.push(p);
  }
  // rounding spoils the last ratios: take the last one whose errors are still well above it
  const usable = out2.filter((_, i) => es[i + 2] > 1e-13 * Math.max(1, Math.abs(es[0])));
  return usable.length ? usable.at(-1) : out2.length ? out2.at(-1) : null;
}
function finishRoots(name, rows, root, extra = {}) {
  const errors = rows.map((r) => r.error);
  return { method: name, iterations: rows, root, estimate: rows.at(-1).x, order: observedOrder(errors), ...extra };
}

/**
 * Bisection on [a, b] with f(a)·f(b) < 0: { iterations: [{ n, a, b, x, fx,
 * bound, error }], root, order }. `bound` is the textbook guarantee
 * (b − a)/2ⁿ⁺¹, `error` the true distance from the midpoint to the root.
 */
export function bisection(f, [a, b], opts = {}) {
  const { ast, variable, F } = prepare(f, opts);
  let lo = startOf(a);
  let hi = startOf(b);
  let flo = F({ [variable]: lo });
  if (!(flo * F({ [variable]: hi }) < 0)) refuse("no-bracket", "bisection needs f(a) and f(b) of opposite signs");
  const root = certifiedRoot(ast, variable, lo, hi, (lo + hi) / 2, opts.digits ?? 25);
  const rows = [];
  const steps = opts.steps ?? 20;
  for (let n = 0; n < steps; n++) {
    const x = lo + (hi - lo) / 2;
    const fx = F({ [variable]: x });
    rows.push({ n, a: lo, b: hi, x, fx, bound: (hi - lo) / 2, error: trueError(x, root) });
    if (fx === 0) break;
    if (flo * fx < 0) hi = x;
    else [lo, flo] = [x, fx];
  }
  return finishRoots("bisection", rows, root);
}

/**
 * Newton's method x ← x − f(x)/f′(x): { iterations: [{ n, x, fx, dfx, error }], root, order, derivative }.
 *
 * With { exact: true } every step is done in exact rational arithmetic, as by
 * hand with fractions: x, fx and dfx are Core Rationals, each row also gives
 * the size of x's denominator in digits (it roughly doubles per step, as the
 * correct digits do), and `floats` holds the double-precision iterates from
 * the same start for comparison. f must be built from + − × ÷ and integer
 * powers so that f(x) and f′(x) are exact; the default is 6 steps.
 */
export function newton(f, x0, opts = {}) {
  if (opts.exact) return exactNewton(f, x0, opts);
  const { ast, variable, F, dAst } = prepare(f, opts);
  const dF = compileFloat(dAst);
  const rows = [];
  let x = startOf(x0);
  const steps = opts.steps ?? 10;
  for (let n = 0; n <= steps; n++) {
    const fx = F({ [variable]: x });
    const dfx = dF({ [variable]: x });
    rows.push({ n, x, fx, dfx });
    if (fx === 0 || !Number.isFinite(fx) || dfx === 0) break;
    const next = x - fx / dfx;
    // stop when the iterate no longer moves, or flips between two neighbouring doubles
    if (next === x || (rows.length >= 2 && next === rows.at(-2).x)) break;
    x = next;
  }
  const root = rootNear(ast, variable, rows, opts);
  for (const r of rows) r.error = trueError(r.x, root);
  return finishRoots("newton", rows, root, { derivative: format(dAst) });
}

function exactNewton(f, x0, opts) {
  const { ast, variable, dAst } = prepare(f, opts);
  const at = (tree, x) => constantRational(tree, { [variable]: x });
  let x = qOf(x0);
  if (at(ast, x) === null || at(dAst, x) === null) refuse("not-rational", "exact Newton needs f built from + − × ÷ and integer powers, so that f(x) and f′(x) are exact fractions");
  const rows = [];
  const steps = opts.steps ?? 6;
  for (let n = 0; n <= steps; n++) {
    const fx = at(ast, x);
    const dfx = at(dAst, x);
    if (fx === null || dfx === null) refuse("undefined", `f or f′ is undefined at ${x}`);
    rows.push({ n, x, fx, dfx, denominatorDigits: x.denominator.toString().length });
    if (fx.numerator === 0n || dfx.numerator === 0n || n === steps) break;
    x = x.subtract(fx.divide(dfx));
  }
  const floats = newton(f, startOf(x0), { ...opts, exact: false, steps: rows.length - 1 }).iterations.map((r) => r.x);
  const last = rows.at(-1).x.toNumber();
  const root = rows.at(-1).fx.numerator === 0n ? new RationalInterval(rows.at(-1).x, rows.at(-1).x) : certifiedRoot(ast, variable, last - 1e-6 - 1e-3 * Math.abs(last), last + 1e-6 + 1e-3 * Math.abs(last), last, opts.digits ?? 40);
  for (const r of rows) r.error = root ? absIv(Iv.point(r.x).sub(Iv.from(root))).hi.toNumber() : null;
  return { ...finishRoots("newton", rows, root, { derivative: format(dAst), exact: true, floats }), estimate: rows.at(-1).x };
}

/** The secant method:/** The secant method: { iterations: [{ n, x, fx, error }], root, order } (the order tends to (1 + √5)/2). */
export function secant(f, x0, x1, opts = {}) {
  const { ast, variable, F } = prepare(f, opts);
  let [a, b] = [startOf(x0), startOf(x1)];
  let [fa, fb] = [F({ [variable]: a }), F({ [variable]: b })];
  const rows = [{ n: 0, x: a, fx: fa }, { n: 1, x: b, fx: fb }];
  const steps = opts.steps ?? 12;
  for (let n = 2; n <= steps; n++) {
    if (fb === fa || fb === 0) break;
    const c = b - (fb * (b - a)) / (fb - fa);
    if (!Number.isFinite(c)) break;
    [a, fa, b] = [b, fb, c];
    fb = F({ [variable]: b });
    rows.push({ n, x: b, fx: fb });
    if (b === a) break;
  }
  const root = rootNear(ast, variable, rows, opts);
  for (const r of rows) r.error = trueError(r.x, root);
  return finishRoots("secant", rows, root);
}

/**
 * Fixed-point iteration x ← g(x): { iterations: [{ n, x, error }], root,
 * multiplier, order }. `root` is the certified fixed point and `multiplier`
 * the enclosure of g′ there: the factor by which each step multiplies the
 * error, and the reason the iteration converges (|g′| < 1) or does not.
 */
export function fixedPoint(g, x0, opts = {}) {
  const variable = opts.variable ?? "x";
  const gAst = toAst(g);
  const G = compileFloat(gAst);
  const rows = [];
  let x = startOf(x0);
  const steps = opts.steps ?? 25;
  for (let n = 0; n <= steps; n++) {
    rows.push({ n, x });
    const next = G({ [variable]: x });
    if (!Number.isFinite(next) || next === x) break;
    x = next;
  }
  const hAst = { type: "op", op: "-", args: [gAst, { type: "var", name: variable }] };
  const root = rootNear(hAst, variable, rows, opts);
  for (const r of rows) r.error = trueError(r.x, root);
  let multiplier = null;
  if (root) {
    try {
      multiplier = out(encloseAst(simplify(derivative(gAst, variable)), { [variable]: Iv.from(root) }, 128).roundOut(80));
    } catch {
      multiplier = null;
    }
  }
  const errs = rows.map((r) => r.error).filter((e) => e !== null && e > 1e-14);
  return { ...finishRoots("fixed point", rows, root), multiplier, ratio: errs.length >= 2 ? errs.at(-1) / errs.at(-2) : null };
}

// ---------------------------------------------------------------- interpolation

const polyText = (p, x = "x") => {
  const parts = [];
  for (let k = p.length - 1; k >= 0; k--) {
    const c = p[k];
    if (c.numerator === 0n) continue;
    const a = c.numerator < 0n ? c.negate() : c;
    const mono = k === 0 ? `${a}` : `${a.equals(ONE) ? "" : `${a}*`}${x}${k > 1 ? `^${k}` : ""}`;
    parts.push(`${c.numerator < 0n ? (parts.length ? "- " : "-") : parts.length ? "+ " : ""}${mono}`);
  }
  return parts.join(" ") || "0";
};

/**
 * The polynomial through given points, with exact arithmetic.
 *   interpolate([[0, 1], [1, 3], [2, 2]])
 *   interpolate("1/(1 + 25*x^2)", { nodes: equallySpaced(-1, 1, 11) })
 * Returns { nodes, values, dividedDifferences, newton, lagrange, polynomial,
 * coefficients, at(x), error(x), maxError([a, b]) }; the last two need the
 * function. Values of a formula at rational nodes are exact when the formula
 * is rational and otherwise correct to about 30 digits.
 */
export function interpolate(source, opts = {}) {
  let xs;
  let ys;
  let ast = null;
  const variable = opts.variable ?? "x";
  if (Array.isArray(source)) {
    xs = source.map((p) => qOf(p[0]));
    ys = source.map((p) => qOf(p[1]));
  } else {
    ast = toAst(source);
    xs = (opts.nodes ?? refuse("bad-nodes", "pass { nodes } with a formula")).map(qOf);
    ys = xs.map((x) => {
      const iv = encloseAst(ast, { [variable]: Iv.point(x) }, 160);
      return iv.isPoint ? iv.lo : roundQ(iv.mid, 120);
    });
  }
  const n = xs.length;
  if (new Set(xs.map(String)).size !== n) refuse("bad-nodes", "the nodes must be distinct");
  // divided differences: table[k][i] = f[x_i, …, x_{i+k}]
  const table = [ys.slice()];
  for (let k = 1; k < n; k++) {
    const prev = table[k - 1];
    table.push(Array.from({ length: n - k }, (_, i) => prev[i + 1].subtract(prev[i]).divide(xs[i + k].subtract(xs[i]))));
  }
  const cs = table.map((row) => row[0]);
  // Newton form expanded to coefficients
  let poly = [ZERO];
  let basis = [ONE];
  for (let k = 0; k < n; k++) {
    poly = P.add(poly, P.scale(basis, cs[k]));
    basis = P.mul(basis, [xs[k].negate(), ONE]);
  }
  const nodal = basis; // Π (x − x_i)
  const factor = (x) => (x.numerator === 0n ? variable : x.numerator < 0n ? `(${variable} + ${x.negate()})` : `(${variable} - ${x})`);
  const newtonText = cs.map((c, k) => [`${c}`, ...xs.slice(0, k).map(factor)].join("*")).join(" + ").replaceAll("+ -", "- ");
  const lagrangeText = ys.map((y, i) => `${y}*${xs.map((x, j) => (j === i ? "" : `${factor(x)}/(${xs[i].subtract(x)})`)).filter(Boolean).join("*")}`).join(" + ");
  const res = {
    nodes: xs,
    values: ys,
    degree: P.deg(poly) < 0 ? 0 : P.deg(poly),
    dividedDifferences: table,
    newton: newtonText,
    lagrange: lagrangeText,
    coefficients: poly,
    polynomial: polyText(poly, variable),
    /** the value of the interpolating polynomial, exact for rational x */
    at(x) {
      return P.evaluate(poly, qOf(x));
    },
  };
  if (ast) {
    // the Newton form: short coefficients and no cancellation between large monomials
    const errAst = toAst(`(${format(ast)}) - (${newtonText})`);
    /** f(x) − p(x), enclosed */
    res.error = (x) => out(encloseAst(errAst, { [variable]: Iv.point(qOf(x)) }, 160).roundOut(80));
    /**
     * { value, attained, at, textbook }: max |f − p| on [a, b] lies between
     * `attained` (the error at the point `at`) and `value`, which agree to
     * about 1%; `textbook` is the bound max|f⁽ⁿ⁾|/n!·max|Π(x − xᵢ)| when that
     * derivative is tractable.
     */
    res.maxError = ([a, b], o = {}) => {
      const sup = supAbs(errAst, variable, qOf(a), qOf(b), o.tolerance ?? 0.01);
      const value = { high: sup.upper };
      let textbook = null;
      try {
        let d = ast;
        for (let k = 0; k < n; k++) {
          d = simplify(derivative(d, variable));
          if (format(d).length > 3000) throw new RangeError("the derivative is too large to bound");
        }
        const M = Iv.from(fn(d, { variable, params: {} }).range([qOf(a), qOf(b)], { digits: 4 }).exact()).mag;
        const W = Iv.from(fn(polyText(nodal, variable), { variable, params: {} }).range([qOf(a), qOf(b)], { digits: 6 }).exact()).mag;
        let fact = ONE;
        for (let k = 2; k <= n; k++) fact = fact.multiply(Q(k));
        textbook = M.multiply(W).divide(fact);
      } catch {
        textbook = null;
      }
      const short = (qv) => (qv === null ? null : new Iv(ZERO, qv).roundOut(40).hi);
      return { value: short(value.high), attained: sup.lower, at: sup.at, textbook: short(textbook) };
    };
  }
  return res;
}
/**
 * max |g| on [a, b] by branch and bound with the mean value form
 * g(m) + g′(X)(X − m): { lower, upper, at } with lower ≤ max ≤ upper.
 */
function supAbs(ast, variable, a, b, relTol = 0.01, bits = 64) {
  const dAst = simplify(derivative(ast, variable));
  const bound = (lo, hi) => {
    const X = new Iv(lo, hi);
    const m = X.mid;
    const gm = encloseAst(ast, { [variable]: Iv.point(m) }, bits);
    let enc;
    try {
      const slope = encloseAst(dAst, { [variable]: X }, bits);
      enc = gm.add(slope.mul(X.sub(Iv.point(m)))).roundOut(bits);
    } catch {
      enc = encloseAst(ast, { [variable]: X }, bits);
    }
    return { lo, hi, upper: enc.mag, lower: gm.mig, m };
  };
  let boxes = [];
  const n0 = 16;
  const w = b.subtract(a).divide(Q(n0));
  for (let i = 0; i < n0; i++) boxes.push(bound(a.add(w.multiply(Q(i))), a.add(w.multiply(Q(i + 1)))));
  let best = { lower: ZERO, at: a };
  for (let round = 0; round < 40; round++) {
    for (const bx of boxes) if (bx.lower.compareTo(best.lower) > 0) best = { lower: bx.lower, at: bx.m };
    boxes = boxes.filter((bx) => bx.upper.compareTo(best.lower) >= 0);
    const upper = boxes.reduce((u, bx) => (bx.upper.compareTo(u) > 0 ? bx.upper : u), best.lower);
    if (upper.toNumber() <= best.lower.toNumber() * (1 + relTol) + 1e-300 || boxes.length > 4000) return { lower: best.lower, upper, at: best.at };
    const next = [];
    for (const bx of boxes) {
      const mid = bx.lo.add(bx.hi).divide(TWO);
      next.push(bound(bx.lo, mid), bound(mid, bx.hi));
    }
    boxes = next;
  }
  const upper = boxes.reduce((u, bx) => (bx.upper.compareTo(u) > 0 ? bx.upper : u), best.lower);
  return { lower: best.lower, upper, at: best.at };
}
const roundQ = (q, bits) => {
  const s = 1n << BigInt(bits);
  const n = (q.numerator * s * 2n + q.denominator) / (q.denominator * 2n);
  return new Rational(n, s);
};
/** n equally spaced nodes from a to b, exact */
export function equallySpaced(a, b, n) {
  const [A, B] = [qOf(a), qOf(b)];
  return Array.from({ length: n }, (_, i) => A.add(B.subtract(A).multiply(Q(i, n - 1))));
}
/**
 * n Chebyshev nodes on [a, b]: (a + b)/2 + (b − a)/2·cos((2i + 1)π/2n),
 * each rounded to a nearby rational (within 2⁻¹⁶ of the true node unless
 * `bits` says otherwise). Any distinct nodes are valid nodes, and short
 * rationals keep the exact polynomial short.
 */
export function chebyshevNodes(a, b, n, bits = 16) {
  const [A, B] = [qOf(a), qOf(b)];
  const half = B.subtract(A).divide(TWO);
  const mid = A.add(B).divide(TWO);
  return Array.from({ length: n }, (_, i) => {
    const c = encloseAst(toAst(`cos(${2 * i + 1}*pi/${2 * n})`), {}, 96);
    return mid.add(half.multiply(roundQ(c.mid, bits)));
  }).reverse();
}

/**
 * The natural cubic spline through points with increasing x, exact:
 * { pieces: [{ from, to, coefficients, polynomial }], at(x), moments }.
 * Each piece is a cubic in (x − from).
 */
export function spline(points) {
  const xs = points.map((p) => qOf(p[0]));
  const ys = points.map((p) => qOf(p[1]));
  const n = xs.length - 1;
  if (n < 2) refuse("bad-nodes", "a spline needs at least three points");
  const h = Array.from({ length: n }, (_, i) => xs[i + 1].subtract(xs[i]));
  if (h.some((v) => v.numerator <= 0n)) refuse("bad-nodes", "the x values must increase");
  // second derivatives M_0 … M_n with M_0 = M_n = 0
  const size = n - 1;
  const A = Array.from({ length: size }, () => new Array(size).fill(ZERO));
  const rhs = [];
  for (let i = 1; i < n; i++) {
    if (i > 1) A[i - 1][i - 2] = h[i - 1];
    A[i - 1][i - 1] = h[i - 1].add(h[i]).multiply(TWO);
    if (i < n - 1) A[i - 1][i] = h[i];
    rhs.push(ys[i + 1].subtract(ys[i]).divide(h[i]).subtract(ys[i].subtract(ys[i - 1]).divide(h[i - 1])).multiply(Q(6)));
  }
  const inner = solveLinear(A, rhs);
  const M = [ZERO, ...inner, ZERO];
  const pieces = [];
  for (let i = 0; i < n; i++) {
    const c0 = ys[i];
    const c1 = ys[i + 1].subtract(ys[i]).divide(h[i]).subtract(h[i].multiply(M[i].multiply(TWO).add(M[i + 1])).divide(Q(6)));
    const c2 = M[i].divide(TWO);
    const c3 = M[i + 1].subtract(M[i]).divide(h[i].multiply(Q(6)));
    const coefficients = [c0, c1, c2, c3];
    pieces.push({ from: xs[i], to: xs[i + 1], coefficients, polynomial: polyText(coefficients, xs[i].numerator === 0n ? "x" : `(x - ${xs[i]})`) });
  }
  return {
    pieces,
    moments: M,
    at(x) {
      const X = qOf(x);
      const p = pieces.find((pc) => X.compareTo(pc.from) >= 0 && X.compareTo(pc.to) <= 0) ?? refuse("outside-domain", "x is outside the spline");
      return P.evaluate(p.coefficients, X.subtract(p.from));
    },
  };
}

/** The least-squares polynomial of a given degree through points, by the normal equations in exact arithmetic: { coefficients, polynomial, residual, at(x) }. */
export function leastSquares(points, degree = 1) {
  const xs = points.map((p) => qOf(p[0]));
  const ys = points.map((p) => qOf(p[1]));
  const m = degree + 1;
  if (xs.length < m) refuse("bad-nodes", "more points than coefficients are needed");
  const pow = xs.map((x) => {
    const row = [ONE];
    for (let k = 1; k <= 2 * degree; k++) row.push(row[k - 1].multiply(x));
    return row;
  });
  const A = Array.from({ length: m }, (_, i) => Array.from({ length: m }, (_, j) => pow.reduce((s, row) => s.add(row[i + j]), ZERO)));
  const b = Array.from({ length: m }, (_, i) => pow.reduce((s, row, k) => s.add(row[i].multiply(ys[k])), ZERO));
  const coefficients = solveLinear(A, b) ?? refuse("singular", "the normal equations are singular: the x values do not determine the polynomial");
  const residual = xs.reduce((s, x, k) => {
    const d = P.evaluate(coefficients, x).subtract(ys[k]);
    return s.add(d.multiply(d));
  }, ZERO);
  return { coefficients, polynomial: polyText(coefficients), residual, at: (x) => P.evaluate(coefficients, qOf(x)) };
}

// ---------------------------------------------------------------- differentiation

/**
 * Difference quotients for f′(x) (or f″ with kind "second") over a list of
 * step sizes, in doubles as a program would compute them, each with its true
 * error: { exact, rows: [{ h, value, error, truncation }], best }. The error
 * falls as h shrinks until rounding takes over; `best` is the row where it
 * was smallest. kinds: "forward", "backward", "central", "second".
 */
export function differences(f, x, opts = {}) {
  const variable = opts.variable ?? "x";
  const kind = opts.kind ?? "central";
  const ast = toAst(f);
  const F = (t) => compileFloat(ast)({ [variable]: t });
  const x0 = typeof x === "number" ? x : nearestDouble(qOf(x));
  const X = Iv.point(exactOf(x0));
  const d1 = simplify(derivative(ast, variable));
  const d2 = simplify(derivative(d1, variable));
  const d3 = simplify(derivative(d2, variable));
  const target = kind === "second" ? d2 : d1;
  const exact = encloseAst(target, { [variable]: X }, 200);
  // leading truncation term of each formula
  const lead = { forward: [d2, 0.5, 1], backward: [d2, -0.5, 1], central: [d3, 1 / 6, 2], second: [simplify(derivative(d3, variable)), 1 / 12, 2] }[kind] ?? refuse("bad-kind", "kind is forward, backward, central or second");
  const leadValue = midNumber(encloseAst(lead[0], { [variable]: X }, 128));
  const hs = opts.steps ?? Array.from({ length: 12 }, (_, i) => 10 ** -(i + 1));
  const f0 = F(x0);
  const rows = hs.map((h) => {
    let value;
    if (kind === "forward") value = (F(x0 + h) - f0) / h;
    else if (kind === "backward") value = (f0 - F(x0 - h)) / h;
    else if (kind === "central") value = (F(x0 + h) - F(x0 - h)) / (2 * h);
    else value = (F(x0 + h) - 2 * f0 + F(x0 - h)) / (h * h);
    const error = Number.isFinite(value) ? absIv(Iv.point(exactOf(value)).sub(exact)).hi.toNumber() : null;
    return { h, value, error, truncation: Math.abs(leadValue * lead[1]) * h ** lead[2] };
  });
  const best = rows.reduce((bst, r) => (r.error !== null && (bst === null || r.error < bst.error) ? r : bst), null);
  return { kind, at: x0, exact: out(exact.roundOut(80)), order: lead[2], rows, best };
}

/**
 * Richardson extrapolation of the central difference: a triangular table
 * whose first column is D(h), D(h/2), D(h/4), … and whose k-th column
 * cancels the h^{2k} error term. { table, errors, exact }.
 */
export function richardson(f, x, opts = {}) {
  const variable = opts.variable ?? "x";
  const ast = toAst(f);
  const F = compileFloat(ast);
  const x0 = typeof x === "number" ? x : nearestDouble(qOf(x));
  const levels = opts.levels ?? 5;
  let h = opts.h ?? 0.5;
  const exact = encloseAst(simplify(derivative(ast, variable)), { [variable]: Iv.point(exactOf(x0)) }, 200);
  const table = [];
  for (let i = 0; i < levels; i++) {
    const row = [(F({ [variable]: x0 + h }) - F({ [variable]: x0 - h })) / (2 * h)];
    for (let k = 1; k <= i; k++) row.push(row[k - 1] + (row[k - 1] - table[i - 1][k - 1]) / (4 ** k - 1));
    table.push(row);
    h /= 2;
  }
  const errors = table.map((row) => row.map((v) => absIv(Iv.point(exactOf(v)).sub(exact)).hi.toNumber()));
  return { table, errors, exact: out(exact.roundOut(80)) };
}

// ---------------------------------------------------------------- quadrature

/** the certified integral, for comparing */
function certifiedIntegral(ast, variable, a, b, digits = 20) {
  const bits = bitsForDigits(digits) + 32;
  return quad1(ast, variable, {}, a, b, { tol: new Rational(1n, 10n ** BigInt(digits)), bits }).iv;
}
/** sup |f⁽ᵏ⁾| on [a, b], or null */
function supDerivative(ast, variable, k, a, b) {
  try {
    let d = ast;
    for (let i = 0; i < k; i++) d = simplify(derivative(d, variable));
    return Iv.from(fn(d, { variable, params: {} }).range([a, b], { digits: 4 }).exact()).mag;
  } catch {
    return null;
  }
}
const RULES = {
  // weights on a panel of width h, points as fractions of the panel, error constant c with |E| ≤ c·(b − a)·h^p·max|f^(k)|
  midpoint: { points: [Q(1, 2)], weights: [ONE], p: 2, k: 2, c: Q(1, 24) },
  trapezoid: { points: [ZERO, ONE], weights: [Q(1, 2), Q(1, 2)], p: 2, k: 2, c: Q(1, 12) },
  simpson: { points: [ZERO, Q(1, 2), ONE], weights: [Q(1, 6), Q(4, 6), Q(1, 6)], p: 4, k: 4, c: Q(1, 2880) },
};
/**
 * A composite rule with n panels: quadrature(f, [a, b], { rule, n }) →
 * { value, exact, error, bound }. `value` encloses what the rule gives with
 * exact arithmetic (so `error` is the error of the METHOD, free of
 * rounding), `exact` is the certified integral, and `bound` the textbook
 * bound c·(b − a)·hᵖ·max|f⁽ᵏ⁾| with the maximum enclosed. rules:
 * "midpoint", "trapezoid", "simpson" (n panels, 2n + 1 points).
 */
export function quadratureRule(f, [a, b], opts = {}) {
  const variable = opts.variable ?? "x";
  const ast = toAst(f);
  const rule = RULES[opts.rule ?? "trapezoid"] ?? refuse("bad-rule", "rule is midpoint, trapezoid or simpson");
  const n = opts.n ?? 4;
  const [A, B] = [qOf(a), qOf(b)];
  const h = B.subtract(A).divide(Q(n));
  const bits = 200;
  let s = Iv.point(ZERO);
  for (let i = 0; i < n; i++) {
    const left = A.add(h.multiply(Q(i)));
    rule.points.forEach((p, j) => {
      s = s.add(encloseAst(ast, { [variable]: Iv.point(left.add(h.multiply(p))) }, bits).scale(rule.weights[j].multiply(h)));
    });
    s = s.roundOut(bits);
  }
  const exact = certifiedIntegral(ast, variable, A, B, opts.digits ?? 20);
  const M = supDerivative(ast, variable, rule.k, A, B);
  let hp = ONE;
  for (let i = 0; i < rule.p; i++) hp = hp.multiply(h);
  return {
    rule: opts.rule ?? "trapezoid",
    panels: n,
    h,
    value: out(s.roundOut(100)),
    exact: out(exact),
    error: out(s.sub(exact).roundOut(100)),
    bound: M === null ? null : rule.c.multiply(B.subtract(A)).multiply(hp).multiply(M),
    order: rule.p,
  };
}

/**
 * Lower and upper Darboux sums: darboux(f, partition) with the partition as a
 * list of points ["0", "1/2", "1"] or { interval: [a, b], n } for n equal
 * pieces. → { lower, upper, exact, pieces, integral }.
 *
 * On a piece where f′ is proven of one sign, f is monotone, so its inf and
 * sup are its end values: exact fractions when f is built from + − × ÷ and
 * powers. If every piece is like that and every end value is a fraction,
 * `exact` is true and `lower` and `upper` are Core Rationals. Otherwise the
 * inf and sup come from certified extrema (the end values and the enclosed
 * critical points), `lower` and `upper` are RationalIntervals that contain
 * the true sums, and `exact` is false. `integral` is the certified integral,
 * which lies between the two sums.
 */
export function darboux(f, partition, opts = {}) {
  const variable = opts.variable ?? "x";
  const ast = toAst(f);
  const dAst = simplify(derivative(ast, variable));
  const bits = 120;
  let points;
  if (Array.isArray(partition)) points = partition.map(qOf);
  else if (partition && partition.interval) {
    const [A, B] = partition.interval.map(qOf);
    const n = partition.n ?? 4;
    points = Array.from({ length: n + 1 }, (_, i) => A.add(B.subtract(A).multiply(Q(i, n))));
  } else refuse("bad-partition", "the partition is a list of points or { interval: [a, b], n }");
  if (points.length < 2) refuse("bad-partition", "a partition needs at least two points");
  for (let i = 1; i < points.length; i++) if (points[i].compareTo(points[i - 1]) <= 0) refuse("bad-partition", "partition points must increase");
  const value = (x) => {
    const q = constantRational(ast, { [variable]: x });
    return q !== null ? Iv.point(q) : encloseAst(ast, { [variable]: Iv.point(x) }, bits);
  };
  const minIv = (ivs) => new Iv(ivs.reduce((m, v) => (v.lo.compareTo(m) < 0 ? v.lo : m), ivs[0].lo), ivs.reduce((m, v) => (v.hi.compareTo(m) < 0 ? v.hi : m), ivs[0].hi));
  const maxIv = (ivs) => new Iv(ivs.reduce((m, v) => (v.lo.compareTo(m) > 0 ? v.lo : m), ivs[0].lo), ivs.reduce((m, v) => (v.hi.compareTo(m) > 0 ? v.hi : m), ivs[0].hi));
  let lower = Iv.point(ZERO);
  let upper = Iv.point(ZERO);
  const pieces = [];
  for (let i = 1; i < points.length; i++) {
    const [a, b] = [points[i - 1], points[i]];
    const h = b.subtract(a);
    const [fa, fb] = [value(a), value(b)];
    let slope = null;
    try {
      const d = encloseAst(dAst, { [variable]: new Iv(a, b) }, bits);
      if (d.lo.numerator >= 0n) slope = "increasing";
      else if (d.hi.numerator <= 0n) slope = "decreasing";
    } catch {
      slope = null;
    }
    let inf;
    let sup;
    if (slope === "increasing") [inf, sup] = [fa, fb];
    else if (slope === "decreasing") [inf, sup] = [fb, fa];
    else {
      const candidates = [fa, fb];
      for (const c of extrema(ast, [a, b], { variable }).exact()) candidates.push(encloseAst(ast, { [variable]: new Iv(c.lo, c.hi) }, bits));
      [inf, sup] = [minIv(candidates), maxIv(candidates)];
    }
    lower = lower.add(inf.scale(h));
    upper = upper.add(sup.scale(h));
    const show = (iv) => (iv.isPoint ? iv.lo : out(iv));
    pieces.push({ from: a, to: b, monotone: slope, inf: show(inf), sup: show(sup) });
  }
  const exact = lower.isPoint && upper.isPoint;
  return {
    lower: exact ? lower.lo : out(lower.roundOut(bits)),
    upper: exact ? upper.lo : out(upper.roundOut(bits)),
    exact,
    pieces,
    integral: out(certifiedIntegral(ast, variable, points[0], points.at(-1), opts.digits ?? 20)),
  };
}

/**
 * Romberg's table: trapezoid sums with 1, 2, 4, … panels in the first
 * column, each further column one Richardson step. { table, errors, exact }
 * with the table in doubles and the true error of every entry.
 */
export function romberg(f, [a, b], opts = {}) {
  const variable = opts.variable ?? "x";
  const ast = toAst(f);
  const F = (t) => compileFloat(ast)({ [variable]: t });
  const [A, B] = [qOf(a), qOf(b)];
  const [fa, fb] = [A.toNumber(), B.toNumber()];
  const levels = opts.levels ?? 5;
  const table = [];
  let h = fb - fa;
  let T = (h / 2) * (F(fa) + F(fb));
  for (let i = 0; i < levels; i++) {
    if (i > 0) {
      let s = 0;
      const n = 2 ** (i - 1);
      for (let k = 0; k < n; k++) s += F(fa + (k + 0.5) * h);
      T = T / 2 + (h / 2) * s;
      h /= 2;
    }
    const row = [T];
    for (let k = 1; k <= i; k++) row.push(row[k - 1] + (row[k - 1] - table[i - 1][k - 1]) / (4 ** k - 1));
    table.push(row);
  }
  const exact = certifiedIntegral(ast, variable, A, B, opts.digits ?? 20);
  const errors = table.map((row) => row.map((v) => absIv(Iv.point(exactOf(v)).sub(exact)).hi.toNumber()));
  return { table, errors, exact: out(exact) };
}

/** Legendre polynomial P_n with exact coefficients */
export function legendre(n) {
  let p0 = [ONE];
  let p1 = [ZERO, ONE];
  if (n === 0) return p0;
  for (let k = 1; k < n; k++) {
    // (k + 1) P_{k+1} = (2k + 1) x P_k − k P_{k−1}
    const next = P.scale(P.sub(P.scale(P.mul([ZERO, ONE], p1), Q(2 * k + 1)), P.scale(p0, Q(k))), Q(1, k + 1));
    [p0, p1] = [p1, next];
  }
  return p1;
}
/**
 * The Gauss-Legendre rule with n points on [−1, 1]: { polynomial, nodes,
 * weights } with every node and weight a certified enclosure. The nodes are
 * the roots of the Legendre polynomial Pₙ (whose coefficients are exact) and
 * the weights are 2/((1 − x²)·Pₙ′(x)²).
 */
export function gaussLegendre(n, opts = {}) {
  if (!Number.isInteger(n) || n < 1 || n > 24) refuse("bad-order", "n is a whole number from 1 to 24");
  const digits = opts.digits ?? 25;
  const p = legendre(n);
  const text = polyText(p, "x");
  const zs = zeros(text, [-1, 1], { tolerance: 10 ** -Math.min(digits, 30) }).exact();
  if (zs.length !== n) refuse("internal", "the Legendre roots were not all separated");
  const dp = P.derivative(p);
  const nodes = zs.map((z) => new RationalInterval(z.lo, z.hi));
  const weights = nodes.map((nd) => {
    const X = Iv.from(nd);
    // Horner in intervals
    let d = Iv.point(ZERO);
    for (let k = dp.length - 1; k >= 0; k--) d = d.mul(X).add(Iv.point(dp[k]));
    return out(Iv.point(TWO).div(Iv.point(ONE).sub(X.mul(X)).mul(d.mul(d))).roundOut(100));
  });
  return { n, polynomial: text, nodes, weights };
}
/** ∫ₐᵇ f by the n-point Gauss-Legendre rule: { value, exact, error, nodes, weights }; exact for polynomials of degree below 2n. */
export function gaussRule(f, [a, b], n = 3, opts = {}) {
  const variable = opts.variable ?? "x";
  const ast = toAst(f);
  const [A, B] = [qOf(a), qOf(b)];
  const rule = gaussLegendre(n, opts);
  const half = B.subtract(A).divide(TWO);
  const mid = A.add(B).divide(TWO);
  let s = Iv.point(ZERO);
  rule.nodes.forEach((nd, i) => {
    const X = Iv.from(nd).scale(half).add(Iv.point(mid));
    s = s.add(encloseAst(ast, { [variable]: X }, 200).mul(Iv.from(rule.weights[i])));
  });
  s = s.scale(half).roundOut(120);
  const exact = certifiedIntegral(ast, variable, A, B, opts.digits ?? 20);
  return { points: n, value: out(s), exact: out(exact), error: out(s.sub(exact).roundOut(100)), nodes: rule.nodes, weights: rule.weights };
}

// ---------------------------------------------------------------- methods for differential equations

const STEPPERS = {
  euler: { order: 1, step: (F, t, y, h) => y + h * F(t, y) },
  heun: {
    order: 2,
    step: (F, t, y, h) => {
      const k1 = F(t, y);
      return y + (h / 2) * (k1 + F(t + h, y + h * k1));
    },
  },
  midpoint: { order: 2, step: (F, t, y, h) => y + h * F(t + h / 2, y + (h / 2) * F(t, y)) },
  rk4: {
    order: 4,
    step: (F, t, y, h) => {
      const k1 = F(t, y);
      const k2 = F(t + h / 2, y + (h / 2) * k1);
      const k3 = F(t + h / 2, y + (h / 2) * k2);
      const k4 = F(t + h, y + h * k3);
      return y + (h / 6) * (k1 + 2 * k2 + 2 * k3 + k4);
    },
  },
};
/**
 * y′ = f(t, y), y(t0) = y0 by a one-step method with n equal steps, or the
 * two-step Adams-Bashforth method ("ab2", started with one Heun step):
 * { method, order, h, steps: [{ n, t, y, exact, error }], finalError }.
 * `exact` is the validated solution at each step and `error` the true
 * global error there.
 */
export function odeMethod(f, opts) {
  const time = opts.time ?? "t";
  const name = opts.variable ?? "y";
  const ast = toAst(f);
  const Fc = compileFloat(ast);
  const F = (t, y) => Fc({ [time]: t, [name]: y });
  const method = opts.method ?? "euler";
  const t0 = qOf(opts.t0 ?? 0);
  const until = qOf(opts.until);
  const n = opts.steps ?? 10;
  const hq = until.subtract(t0).divide(Q(n));
  const h = hq.toNumber();
  const y0 = qOf(opts.y0);
  const sol = opts.reference ?? odeSolve({ f: format(ast), vars: [name], time, y0, t0, until, order: opts.order ?? 10, tol: opts.tol ?? "1e-12" }).exact();
  if (!sol.complete) refuse("no-enclosure", `the validated solution stopped early: ${sol.reason}`);
  const rows = [];
  let y = y0.toNumber();
  let prevSlope = null;
  const stepper = STEPPERS[method];
  if (!stepper && method !== "ab2") refuse("bad-method", "method is euler, heun, midpoint, rk4 or ab2");
  for (let i = 0; i <= n; i++) {
    const tq = t0.add(hq.multiply(Q(i)));
    const t = tq.toNumber();
    const exact = sol.at(tq);
    const error = Number.isFinite(y) ? absIv(Iv.point(exactOf(y)).sub(Iv.from(exact))).hi.toNumber() : null;
    rows.push({ n: i, t: tq, y, exact, error });
    if (i === n || !Number.isFinite(y)) break;
    if (method === "ab2") {
      const slope = F(t, y);
      y = prevSlope === null ? STEPPERS.heun.step(F, t, y, h) : y + (h / 2) * (3 * slope - prevSlope);
      prevSlope = slope;
    } else y = stepper.step(F, t, y, h);
  }
  return { method, order: method === "ab2" ? 2 : stepper.order, h: hq, steps: rows, finalError: rows.at(-1).error, reference: sol };
}
/**
 * The same problem with several step counts: { rows: [{ steps, h, error,
 * ratio, observedOrder }] }. Halving h should divide the error by 2^order.
 */
export function stepSizeStudy(f, opts) {
  const counts = opts.counts ?? [10, 20, 40, 80, 160];
  let reference = null;
  const rows = [];
  for (const steps of counts) {
    const r = odeMethod(f, { ...opts, steps, reference: reference ?? undefined });
    reference = r.reference;
    const prev = rows.at(-1);
    const ratio = prev && r.finalError ? prev.error / r.finalError : null;
    rows.push({ steps, h: r.h, error: r.finalError, ratio, observedOrder: ratio && prev ? Math.log(ratio) / Math.log(steps / prev.steps) : null });
  }
  return { method: opts.method ?? "euler", rows };
}
/**
 * The interval of absolute stability on the negative real axis: for
 * y′ = λy the method multiplies y by R(hλ) each step, and the numerical
 * solution decays only when |R(hλ)| < 1. Returns { polynomial, interval,
 * largestStep(lambda) } for euler, heun/midpoint and rk4.
 */
export function stability(method = "euler") {
  const R = { euler: [ONE, ONE], heun: [ONE, ONE, Q(1, 2)], midpoint: [ONE, ONE, Q(1, 2)], rk4: [ONE, ONE, Q(1, 2), Q(1, 6), Q(1, 24)] }[method] ?? refuse("bad-method", "method is euler, heun, midpoint or rk4");
  const text = polyText(R, "z");
  // the left end: the negative z where R(z) = 1 or −1 first
  let left;
  if (method === "euler" || method === "heun" || method === "midpoint") left = new RationalInterval(Q(-2), Q(-2));
  else {
    const z = zeros(`${text} - 1`, [-4, "-1/10"], { variable: "z", tolerance: 1e-20 }).exact();
    left = new RationalInterval(z[0].lo, z[0].hi);
  }
  return {
    method,
    polynomial: `R(z) = ${text}`,
    interval: [left, new RationalInterval(ZERO, ZERO)],
    /** the largest step for which y′ = λy (λ < 0) decays numerically */
    largestStep(lambda) {
      const L = qOf(lambda);
      if (L.numerator >= 0n) refuse("bad-problem", "give a negative λ");
      return out(Iv.from(left).scale(L.reciprocal()));
    },
  };
}
