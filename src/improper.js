// Improper integrals and limits at infinity or at a singular point, built on
// the growth calculus of asymptotic.js. A ray [T, ∞) is cut at some X: the
// part up to X is integrated on doubling pieces with Taylor models, and the
// tail beyond X is enclosed (or shown to diverge) from the leading behaviour.
// A singular endpoint c is moved to infinity by x = c ± 1/t.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, lt, le, gt, max } from "./rat.js";
import { simplify, num, v as variable, op, format, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { quad1 } from "./quad.js";
import { rays, rayContext, nodeAt, tailOf, limitAtInfinity, describeNode, onRay } from "./asymptotic.js";

const tenTo = (d) => new Rational(1n, 10n ** BigInt(d));
const INF = Symbol("inf");
const NEG_INF = Symbol("-inf");

/** Reads an endpoint: a rational, or "inf", "-inf", ±Infinity, "∞". */
export function endpoint(x, q) {
  if (x === Infinity || x === "inf" || x === "+inf" || x === "∞" || x === "+∞" || x === "infinity" || x === "oo") return INF;
  if (x === -Infinity || x === "-inf" || x === "-∞" || x === "-infinity" || x === "-oo") return NEG_INF;
  return q(x);
}
export const isInfinite = (x) => x === INF || x === NEG_INF;

const substitute = (ast, name, by) => {
  if (ast.type === "var") return ast.name === name ? by : ast;
  if (ast.type === "op" || ast.type === "call") return { ...ast, args: ast.args.map((a) => substitute(a, name, by)) };
  return ast;
};
const paramEnv = (f, evalParams) => {
  const env = {};
  for (const [k, val] of Object.entries(evalParams(f.params))) env[k] = Iv.from(val);
  return env;
};
const definedAt = (ast, name, env, x, bits) => {
  try {
    encloseAst(ast, { ...env, [name]: Iv.point(x) }, bits);
    return true;
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
    return false;
  }
};

/**
 * The pieces an improper integral is cut into. Each is
 * { ast, from } for ∫_from^∞ ast d(name), or { ast, a, b } for an ordinary
 * integral, with a sign.
 */
function plan(f, A, B, env, bits, singular) {
  const name = f.variable;
  const X = variable(name);
  const pieces = [];
  const defined = (x) => definedAt(f.ast, name, env, x, bits);
  // ∫ over (c, c + w] with the singular end at c: x = c + 1/t, t from 1/w
  const fromRight = (c, w) => ({ ast: simplify(op("/", substitute(f.ast, name, op("+", num(c), op("/", num(1), X))), op("^", X, num(2)))), from: w.reciprocal(), what: `near ${c}` });
  const fromLeft = (c, w) => ({ ast: simplify(op("/", substitute(f.ast, name, op("-", num(c), op("/", num(1), X))), op("^", X, num(2)))), from: w.reciprocal(), what: `near ${c}` });
  const toInfinity = (from) => ({ ast: f.ast, from, what: "at +∞" });
  const toMinusInfinity = (from) => ({ ast: simplify(substitute(f.ast, name, op("neg", X))), from: from.negate(), what: "at -∞" });
  const finite = (a, b) => {
    if (a.equals(b)) return;
    const sa = !defined(a);
    const sb = !defined(b);
    if (!sa && !sb) pieces.push({ ordinary: true, a, b });
    else if (sa && sb) {
      const m = a.add(b).divide(TWO);
      pieces.push(fromRight(a, m.subtract(a)), fromLeft(b, b.subtract(m)));
    } else if (sa) pieces.push(fromRight(a, b.subtract(a)));
    else pieces.push(fromLeft(b, b.subtract(a)));
  };
  // cut at the singular points named by the caller, and at 0 for the whole line
  const cuts = [...singular].sort((x, y) => x.compareTo(y));
  const inside = (x) => (A === NEG_INF || gt(x, A)) && (B === INF || lt(x, B));
  const marks = cuts.filter(inside);
  if (A === NEG_INF && B === INF && !marks.length) marks.push(ZERO);
  let lo = A;
  for (const m of [...marks, B]) {
    if (lo === NEG_INF && m === INF) refuse("bad-interval", "no cut point");
    if (lo === NEG_INF) {
      // (−∞, m]: keep a finite stretch next to m when m is singular
      if (defined(m)) pieces.push(toMinusInfinity(m));
      else { pieces.push(toMinusInfinity(m.subtract(ONE))); finite(m.subtract(ONE), m); }
    } else if (m === INF) {
      if (defined(lo)) pieces.push(toInfinity(lo));
      else { finite(lo, lo.add(ONE)); pieces.push(toInfinity(lo.add(ONE))); }
    } else finite(lo, m);
    lo = m;
  }
  return pieces;
}

/** ∫_from^∞ ast: the cut X, the tail beyond it and the doubling pieces up to it. */
function* rayStages(f, piece, env, digits, bits, progress) {
  const name = f.variable;
  const tol = tenTo(digits);
  let chosen = null;
  let tried = 0;
  for (const X of rays(piece.from)) {
    const ctx = rayContext(name, env, X, bits);
    let tail;
    try {
      tail = tailOf(nodeAt(piece.ast, ctx), ctx, format(piece.ast));
    } catch (e) {
      if (!(e instanceof AnalyticError) || (e.code !== "larger-x" && e.code !== "overflow")) throw e;
      continue;
    }
    if (tail.kind === "diverges") return { diverges: tail.sign };
    chosen = { X, tail: tail.iv };
    tried += 1;
    // a tail known only by a bound narrows slowly, and the stretch up to X costs more the further out it goes
    if (le(tail.iv.width, tol) || (tail.loose && tail.oscillates && tried >= 8)) break;
  }
  if (!chosen) refuse("undecided", `could not bound ${format(piece.ast)} ${piece.what}`);
  const marks = [piece.from];
  let c = lt(piece.from, TWO) ? TWO : piece.from.multiply(TWO);
  while (lt(c, chosen.X)) { marks.push(c); c = c.multiply(TWO); }
  marks.push(chosen.X);
  // no piece needs more digits than the tail has
  const each = max(tol, chosen.tail.width).divide(new Rational(BigInt(4 * (marks.length - 1))));
  let sum = chosen.tail;
  let met = le(chosen.tail.width, tol);
  for (let i = 0; i + 1 < marks.length; i++) {
    const part = quad1(piece.ast, name, env, marks[i], marks[i + 1], { tol: each, bits });
    met &&= part.met;
    sum = sum.add(part.iv);
    yield progress(sum);
  }
  return { iv: sum, X: chosen.X, pieces: marks.length - 1, met };
}

export function* improperStages(f, A, B, opts, evalParams) {
  const digits = opts.digits ?? 10;
  const bits = Math.max(96, bitsForDigits(digits) + 40);
  const env = paramEnv(f, evalParams);
  const q = (x) => (typeof x === "string" ? toRational(x) : typeof x === "number" && !Number.isInteger(x) ? toRational(x) : x instanceof Rational ? x : new Rational(BigInt(x)));
  let sign = 1;
  if ((A === INF && B !== INF) || B === NEG_INF || (!isInfinite(A) && !isInfinite(B) && gt(A, B))) { [A, B] = [B, A]; sign = -1; }
  if (A === B) return { value: Iv.point(ZERO).toRationalInterval(), via: "empty interval" };
  const pieces = plan(f, A, B, env, bits, (opts.singular ?? []).map(q));
  let total = Iv.point(ZERO);
  const diverging = [];
  const notes = [];
  let wide = false;
  let done = 0;
  for (const piece of pieces) {
    if (piece.ordinary) {
      const part = quad1(f.ast, f.variable, env, piece.a, piece.b, { tol: tenTo(digits + 1), bits });
      if (!part.met) wide = true;
      total = total.add(part.iv);
    } else {
      const r = yield* rayStages(f, piece, env, digits + 1, bits, (sum) => ({ done: ++done, of: done + 1, step: `tail ${piece.what}`, partial: total.add(sum).toRationalInterval() }));
      if (r.diverges) diverging.push({ sign: r.diverges, what: piece.what });
      else {
        if (!r.met) wide = true;
        total = total.add(r.iv);
        notes.push(`${piece.what}: tail beyond ${piece.what.startsWith("near") ? `distance 1/${r.X}` : r.X} from the leading behaviour`);
      }
    }
    yield { done: ++done, of: done + 1, step: "pieces", partial: total.toRationalInterval() };
  }
  if (diverging.length) {
    const signs = new Set(diverging.map((d) => d.sign * sign));
    const where = diverging.map((d) => d.what).join(" and ");
    if (signs.size > 1) return { value: NaN, via: `diverges ${where}, with opposite signs: no value` };
    return { value: [...signs][0] > 0 ? Infinity : -Infinity, via: `diverges ${where}: the integrand is of one sign there and too large to integrate` };
  }
  const out = sign < 0 ? total.neg() : total;
  return { value: out.roundOut(bits).toRationalInterval(), via: `converges; ${notes.join("; ") || "ordinary integral"}${wide ? " (wider than asked: the tail is only known by a bound)" : ""}` };
}

/** Float preview of an improper integral: Gauss panels after x = T + s/(1 − s). */
export function improperFloat(f, A, B, gaussLegendre) {
  const g = (x) => f.float(x);
  const ray = (h, from) => gaussLegendre((s) => h(from + s / (1 - s)) / (1 - s) ** 2, 0, 1, 64);
  if (A === NEG_INF && B === INF) return ray(g, 0) + ray((x) => g(-x), 0);
  if (B === INF) return ray(g, A.toNumber());
  if (A === NEG_INF) return ray((x) => g(-x), -B.toNumber());
  if (A === INF) return -ray(g, B.toNumber());
  if (B === NEG_INF) return -ray((x) => g(-x), -A.toNumber());
  return gaussLegendre(g, A.toNumber(), B.toNumber(), 64);
}

/**
 * The limit of f at +∞ or −∞, or one-sided at a rational point
 * (side "right" or "left"): a RationalInterval holding the limit, or
 * ±Infinity.
 */
export function limitAt(f, where, side, opts, evalParams) {
  const bits = bitsForDigits(opts.digits ?? 20) + 24;
  const name = f.variable;
  const X = variable(name);
  let ast = f.ast;
  if (where === NEG_INF) ast = substitute(ast, name, op("neg", X));
  else if (where !== INF) ast = substitute(ast, name, side === "left" ? op("-", num(where), op("/", num(1), X)) : op("+", num(where), op("/", num(1), X)));
  const r = limitAtInfinity(simplify(ast), name, paramEnv(f, evalParams), bits);
  return r.kind === "infinite" ? (r.sign > 0 ? Infinity : -Infinity) : r.iv.toRationalInterval();
}

/** The leading behaviour of f at ±∞: f(x) = term·(coefficient + something that dies out). */
export function behaviourAt(f, where, opts, evalParams) {
  const bits = bitsForDigits(opts.digits ?? 20) + 24;
  const name = f.variable;
  const ast = where === NEG_INF ? simplify(substitute(f.ast, name, op("neg", variable(name)))) : f.ast;
  const node = onRay(ast, name, paramEnv(f, evalParams), bits, (n) => n);
  const d = describeNode(node, where === NEG_INF ? `(-${name})` : name);
  return d;
}
