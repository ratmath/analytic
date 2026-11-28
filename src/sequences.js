// Sequences and series, with the tests of a calculus course as named steps.
//
// A term a(n) is a formula in the index. On a ray [N, ∞) the asymptotic
// module writes it as e^(k·x)·x^p·(log x)^m·(ℓ + ρ(x)) with a proven bound on
// ρ, and everything here is read off that: limits of sequences, which test
// decides a series and with which quantities, and a bound on the tail of the
// series after N terms that holds for every later term. The sum of a series
// is then (the first N terms, exactly or enclosed) + (an interval that holds
// the tail).
//
// Factors the asymptotic form cannot hold are taken out first, by reading the
// term as
//
//     a(n) = (±1)^n · q^n · Γ-factors · r(n)
//
// so that ratios a(n+1)/a(n) simplify the way they do by hand: the powers
// leave q, and each factorial leaves a polynomial.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, HALF, toQ, lt, le, gt, ge, factorial } from "./rat.js";
import { toAst, format, derivative, simplify, freeVariables, constantRational, num, v as variable, op, call, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { rayContext, nodeAt, tailOf, signE, addE, spread, upperEnv, envAt, decreasing, tailUpper, positiveShape } from "./asymptotic.js";
import { quad1 } from "./quad.js";
import { AnalyticFunction, evalParams } from "./fn.js";
import { zeros } from "./roots.js";
import { periodOf, alongResidue } from "./periodic.js";
import { weakSign, definedOn, UNBOUNDED } from "./uniform.js";

const tenTo = (d) => new Rational(1n, 10n ** BigInt(d));
const q = (x) => (typeof x === "string" || (typeof x === "number" && !Number.isInteger(x)) ? toRational(x) : toQ(x));
const RI = (iv) => iv.toRationalInterval();
const subst = (ast, name, by) => {
  if (ast.type === "var") return ast.name === name ? by : ast;
  if (ast.args) return { ...ast, args: ast.args.map((a) => subst(a, name, by)) };
  return ast;
};
const depends = (ast, name) => freeVariables(ast).has(name);
const soft = (f, fallback = null) => {
  try {
    return f();
  } catch (e) {
    if (e instanceof AnalyticError) return fallback;
    throw e;
  }
};
/** "n!" is read as gamma(n + 1); "(2n)!" as gamma(2n + 1). */
const readTerm = (x) => {
  if (typeof x !== "string") return toAst(x);
  let text = x;
  for (let i = 0; i < 8 && text.includes("!"); i++) {
    text = text.replace(/\(([^()]*)\)!/g, "gamma(($1)+1)").replace(/([A-Za-z_]\w*|\d+)!/g, "gamma($1+1)");
  }
  return toAst(text);
};
const paramEnv = (params) => {
  const env = {};
  for (const [k, val] of Object.entries(evalParams(params ?? {}))) env[k] = Iv.from(val);
  return env;
};
const NS = [16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384];

// ---- reading a term ---------------------------------------------------------------------------

/**
 * a(n) = sign(n) · Π base^(α·n) · Π Γ(s·n + t)^power · rest(n).
 * `alternating` is true when sign(n) = (−1)^n up to a constant sign, which is
 * then inside `rest`.
 */
function decompose(ast, n, env, bits) {
  const out = { alternating: false, geo: [], gammas: [], rest: [] };
  const linear = (u) => {
    const a = constantRational(simplify(derivative(u, n)));
    if (a === null) return null;
    return { a, b: simplify(subst(u, n, num(0))) };
  };
  const push = (node, p) => out.rest.push(p === 1 ? node : op("^", node, num(p)));
  const walk = (node, p) => {
    if (!depends(node, n)) return push(node, p);
    if (node.type === "op") {
      if (node.op === "*") return node.args.forEach((a) => walk(a, p));
      if (node.op === "/") return (walk(node.args[0], p), walk(node.args[1], -p));
      if (node.op === "neg") return (push(num(-1), Math.abs(p) % 2), walk(node.args[0], p));
      if (node.op === "^") {
        const [base, e] = node.args;
        const k = constantRational(e);
        if (k !== null && k.denominator === 1n && k.abs().numerator < 64n) return walk(base, p * Number(k.numerator));
        if (!depends(base, n)) {
          const l = linear(e);
          const b = constantRational(base);
          if (l && b !== null && b.numerator < 0n && l.a.denominator === 1n) {
            // a negative base: (−1)^(a·n + b) times a positive power
            const b0 = constantRational(l.b);
            if (b0 !== null && b0.denominator === 1n) {
              if (l.a.numerator % 2n !== 0n && p % 2 !== 0) out.alternating = !out.alternating;
              if (b0.numerator % 2n !== 0n && p % 2 !== 0) out.rest.push(num(-1));
              if (!b.abs().equals(ONE)) walk(op("^", num(b.abs()), e), p);
              return undefined;
            }
          }
          const positive = soft(() => gt(encloseAst(base, env, bits).lo, ZERO), false);
          if (l && b !== null && b.equals(ONE)) return undefined; // 1^n
          if (l && positive) {
            out.geo.push({ base, alpha: l.a.multiply(new Rational(BigInt(p))) });
            return push(op("^", base, l.b), p);
          }
        }
      }
    }
    if (node.type === "call" && node.name === "exp") {
      const l = linear(node.args[0]);
      if (l) {
        out.geo.push({ base: { type: "const", name: "e" }, alpha: l.a.multiply(new Rational(BigInt(p))) });
        return push(call("exp", l.b), p);
      }
    }
    if (node.type === "call" && node.name === "gamma") {
      const l = linear(node.args[0]);
      if (l && l.a.denominator === 1n && l.a.numerator > 0n && l.a.numerator <= 6n) {
        out.gammas.push({ s: Number(l.a.numerator), u: node.args[0], power: p });
        return undefined;
      }
    }
    return push(node, p);
  };
  walk(ast, 1);
  const rest = out.rest.length ? simplify(out.rest.reduce((a, b) => op("*", a, b))) : num(1);
  // q = Π base^α, enclosed
  let Q = Iv.point(ONE);
  for (const g of out.geo) {
    const exact = constantRational(op("^", g.base, num(g.alpha)));
    Q = Q.mul(exact !== null ? Iv.point(exact) : encloseAst(op("^", g.base, num(g.alpha)), env, bits));
  }
  // Γ(u(n+1))/Γ(u(n)) = u(n)·(u(n) + 1)···(u(n) + s − 1)
  let gammaRatio = num(1);
  for (const g of out.gammas) {
    let poly = num(1);
    for (let j = 0; j < g.s; j++) poly = op("*", poly, op("+", g.u, num(j)));
    gammaRatio = g.power >= 0 ? op("*", gammaRatio, op("^", poly, num(g.power))) : op("/", gammaRatio, op("^", poly, num(-g.power)));
  }
  const hasGamma = out.gammas.length > 0;
  // powers that cancel (2^n·(1/2)^n) leave a term the comparison tests can read
  const plain = !hasGamma && (out.geo.length === 0 || (Q.isPoint && Q.lo.equals(ONE)));
  // |a(n+1)/a(n)| without its constant factor q
  const ratioRest = simplify(op("*", gammaRatio, op("/", subst(rest, n, op("+", variable(n), num(1))), rest)));
  return { alternating: out.alternating, Q, rest, ratioRest, hasGamma, plain, geo: out.geo };
}

/** Exact value of a term at a whole number, when the formula is rational there (factorials included); else null. */
function exactAt(ast, n, k) {
  const go = (t) => {
    switch (t.type) {
      case "num": return t.value;
      case "var": return t.name === n ? k : null;
      case "op": {
        const a = t.args.map(go);
        if (a.some((x) => x === null)) return null;
        switch (t.op) {
          case "+": return a[0].add(a[1]);
          case "-": return a[0].subtract(a[1]);
          case "*": return a[0].multiply(a[1]);
          case "/": return a[1].numerator === 0n ? null : a[0].divide(a[1]);
          case "neg": return a[0].negate();
          case "^": {
            if (a[1].denominator !== 1n) return null;
            const e = Number(a[1].numerator);
            if (Math.abs(e) > 100000 || (e <= 0 && a[0].numerator === 0n)) return null;
            return a[0].pow(e);
          }
        }
        return null;
      }
      case "call": {
        if (t.name === "gamma" && t.args.length === 1) {
          const a = go(t.args[0]);
          if (a !== null && a.denominator === 1n && a.numerator > 0n && a.numerator < 3000n) return new Rational(factorial(Number(a.numerator) - 1));
        }
        if (t.name === "abs" && t.args.length === 1) {
          const a = go(t.args[0]);
          return a === null ? null : a.abs();
        }
        return null;
      }
    }
    return null;
  };
  return go(ast);
}

/** Runs f(ctx) on [N, ∞) for the first N of the list where every bound holds; null when none does. */
function onRays(n, env, bits, from, f, list = NS) {
  for (const N of list) {
    if (N < from) continue;
    const ctx = rayContext(n, env, new Rational(BigInt(N)), bits);
    try {
      const r = f(ctx, N);
      if (r !== undefined) return r;
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
    }
  }
  return null;
}
/** sup of |ast| on the ray, from its node; throws when it grows. */
function supOnRay(ast, ctx) {
  const node = nodeAt(ast, ctx);
  const s = signE(node.e);
  if (s > 0) refuse("unbounded", "grows without bound");
  if (s === 0) return spread(node, ctx).mag;
  return envAt(upperEnv(node, ctx), ctx);
}
/** The sign of ast on the whole ray: 1, −1, or 0 when not settled. */
function signOnRay(ast, ctx) {
  const node = nodeAt(ast, ctx);
  if (node.osc && node.L.containsZero()) return 0;
  const S = spread(node, ctx);
  return gt(S.lo, ZERO) ? 1 : lt(S.hi, ZERO) ? -1 : 0;
}
/**
 * The sign of H on the whole ray when its node does not show one: if H → 0
 * and H′ has one sign s on the ray, H is strictly monotone there with limit
 * 0, so its sign is −s throughout. H′ is treated the same way, up to four
 * derivatives deep. This settles differences whose leading terms cancel,
 * such as log(1 + 1/x) − 1/(x + 1): its derivative is a rational function,
 * whose sign is exact. Returns 1, −1, or 0 when not settled.
 */
function chainSign(H, n, ctx, depth = 0) {
  const node = nodeAt(H, ctx);
  if (!(node.osc && node.L.containsZero())) {
    const S = spread(node, ctx);
    if (gt(S.lo, ZERO)) return 1;
    if (lt(S.hi, ZERO)) return -1;
  }
  const decays = signE(node.e) < 0 || (!node.osc && node.r && node.L.mag.numerator === 0n && signE(addE(node.e, node.r.e)) < 0);
  if (!decays || depth >= 4) return 0;
  upperEnv(node, ctx); // the decaying bound must hold on this ray
  return -chainSign(simplify(derivative(H, n)), n, ctx, depth + 1);
}
/** log of a tree, taken through products, quotients and powers: log(u^v) = v·log u. */
function logTree(ast) {
  if (ast.type === "op" && ast.op === "*") return op("+", logTree(ast.args[0]), logTree(ast.args[1]));
  if (ast.type === "op" && ast.op === "/") return op("-", logTree(ast.args[0]), logTree(ast.args[1]));
  if (ast.type === "op" && ast.op === "^") return op("*", ast.args[1], call("log", ast.args[0]));
  if (ast.type === "call" && ast.name === "exp") return ast.args[0];
  return call("log", ast);
}
const describeLimit = (L) => (L === Infinity ? "∞" : L === -Infinity ? "-∞" : L.low.equals(L.high) ? `${L.low}` : `about ${L.low.add(L.high).divide(TWO).toNumber()}`);

/** lim |a(n+1)/a(n)| as { kind: "finite", iv } or { kind: "infinite" }, or null. */
function ratioLimit(d, n, env, bits) {
  return onRays(n, env, bits, 0, (ctx) => {
    const node = nodeAt(d.ratioRest, ctx);
    const s = signE(node.e);
    if (s > 0) return { kind: "infinite" };
    if (s < 0) {
      upperEnv(node, ctx);
      return { kind: "finite", iv: Iv.point(ZERO) };
    }
    if (node.osc && !node.L.isPoint) return undefined;
    spread(node, ctx);
    const L = node.L.mul(d.Q);
    return { kind: "finite", iv: new Iv(L.mig, L.mag) };
  });
}

// ---- sequences --------------------------------------------------------------------------------

export class Sequence {
  constructor(term, { variable: n = "n", from = 1, params = {} } = {}) {
    this.ast = readTerm(term);
    this.variable = n;
    this.from = from;
    this.params = Object.freeze({ ...params });
    for (const name of freeVariables(this.ast)) if (name !== n && !(name in params)) refuse("unbound", `${name} has no value: pass it in params, or set variable`);
    Object.freeze(this);
  }
  toString() {
    return format(this.ast);
  }
  get #env() {
    return paramEnv(this.params);
  }
  /** a(n): an exact Rational where the formula is rational at n, else a certified RationalInterval. */
  term(k, { digits = 20 } = {}) {
    const K = new Rational(BigInt(k));
    const exact = Object.keys(this.params).length ? null : exactAt(this.ast, this.variable, K);
    if (exact !== null) return exact;
    return RI(encloseAst(this.ast, { ...this.#env, [this.variable]: Iv.point(K) }, bitsForDigits(digits) + 16));
  }
  terms(count = 10, opts) {
    return Array.from({ length: count }, (_, i) => this.term(this.from + i, opts));
  }
  /**
   * The limit as n → ∞: a RationalInterval that holds it, or ±Infinity.
   * Refuses ("no-limit", "undecided") where none is proven.
   */
  limit({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const f = new AnalyticFunction(this.ast, { variable: this.variable, params: this.params });
    try {
      return f.limit("inf", { digits });
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      // powers and factorials: the ratio of successive terms decides
      const d = soft(() => decompose(this.ast, this.variable, this.#env, bits));
      const L = d && !d.plain ? ratioLimit(d, this.variable, this.#env, bits) : null;
      if (L?.kind === "finite" && lt(L.iv.hi, ONE)) return new RationalInterval(ZERO, ZERO);
      if (L && (L.kind === "infinite" || gt(L.iv.lo, ONE)) && !d.alternating) {
        const s = onRays(this.variable, this.#env, bits, 0, (ctx) => soft(() => signOnRay(d.rest, ctx), 0) || (positiveShape(d.rest, ctx) ? 1 : undefined));
        if (s) return s > 0 ? Infinity : -Infinity;
      }
      // periodic factors ((−1)^n, cos(πn)): the limits along n = p·m + r decide
      const acc = soft(() => accumulation(this, { digits }));
      if (acc) {
        if (acc.converges) return acc.limsup;
        refuse("no-limit", `no limit: the terms oscillate, with lim sup ${showValue(acc.limsup)} and lim inf ${showValue(acc.liminf)} (${acc.subsequences.map((u) => `${u.along} tends to ${showValue(u.limit)}`).join("; ")})`);
      }
      const per = periodOf(this.ast, this.variable);
      if (per.blocker) refuse("no-limit", `no limit could be proven: ${per.blocker}, so the terms are not split into subsequences (${e.message})`);
      throw e;
    }
  }
  /**
   * Whether the terms rise or fall: { direction: "increasing" | "decreasing"
   * | "constant", from: N, proven: "for every n ≥ N" }. The derivative of the
   * formula has one sign on [N, ∞); between `from` and N the terms themselves
   * are compared, and N is moved back as far as they agree.
   */
  monotone({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const n = this.variable;
    const env = this.#env;
    const da = simplify(derivative(this.ast, n));
    if (da.type === "num" && da.value.numerator === 0n) return { direction: "constant", from: this.from, proven: `for every n ≥ ${this.from}` };
    let found = onRays(n, env, bits, this.from, (ctx, N) => {
      const s = signOnRay(da, ctx);
      return s ? { s, N } : undefined;
    }, [4, 8, ...NS]);
    // a derivative whose leading terms cancel (n·sin(1/n)): its sign from its own derivatives
    found ??= onRays(n, env, bits, this.from, (ctx, N) => {
      const s = chainSign(da, n, ctx);
      return s ? { s, N } : undefined;
    }, [4, 8, ...NS]);
    let how = null;
    if (!found) {
      // a positive term: a(x) rises exactly where log a(x) does, and the sign of (log a)′ is
      // settled through its own derivatives where its leading terms cancel ((1 + 1/n)^n)
      const logDa = soft(() => simplify(derivative(logTree(this.ast), n)));
      found = logDa && onRays(n, env, bits, this.from, (ctx, N) => {
        if (!positiveShape(this.ast, ctx)) return undefined;
        const s = chainSign(logDa, n, ctx);
        return s ? { s, N } : undefined;
      }, [4, 8, ...NS]);
      if (found) how = `(log a)′ = ${format(logDa)} tends to 0 and is ${found.s > 0 ? "decreasing" : "increasing"} for x ≥ ${found.N}, so it is ${found.s > 0 ? "positive" : "negative"} there`;
    }
    if (!found) return refuse("undecided", `no ray was found on which ${format(this.ast)} is proven monotone`);
    // walk back through the terms before N
    let N = found.N;
    let next = Iv.from(this.term(N, { digits }));
    while (N > this.from) {
      const here = soft(() => Iv.from(this.term(N - 1, { digits })));
      if (!here) break;
      const ok = found.s > 0 ? lt(here.hi, next.lo) : gt(here.lo, next.hi);
      if (!ok) break;
      next = here;
      N -= 1;
    }
    return { direction: found.s > 0 ? "increasing" : "decreasing", from: N, proven: `for every n ≥ ${N}`, ...(how ? { reason: how } : {}) };
  }
  /**
   * An interval that holds every term from `from` on, or null for a bound
   * that does not exist on that side: { lower, upper, bounded }.
   */
  bounds({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const n = this.variable;
    const env = this.#env;
    const tail = onRays(n, env, bits, this.from, (ctx, N) => {
      const node = nodeAt(this.ast, ctx);
      const s = signE(node.e);
      if (s > 0) {
        const sg = signOnRay(this.ast, ctx);
        if (!sg) return undefined;
        return { N, unbounded: sg };
      }
      if (s === 0) return { N, iv: spread(node, ctx) };
      const m = envAt(upperEnv(node, ctx), ctx);
      const sg = soft(() => signOnRay(this.ast, ctx), 0);
      if (!sg && N < 64) return undefined; // a little further out the sign may settle
      return { N, iv: sg > 0 ? new Iv(ZERO, m) : sg < 0 ? new Iv(m.negate(), ZERO) : new Iv(m.negate(), m) };
    }, [4, 8, ...NS]);
    if (!tail) return refuse("undecided", `no bound on ${format(this.ast)} was proven`);
    let lo = tail.iv?.lo ?? null;
    let hi = tail.iv?.hi ?? null;
    for (let k = this.from; k < tail.N; k++) {
      const t = Iv.from(this.term(k, { digits }));
      if (lo === null || lt(t.lo, lo)) lo = t.lo;
      if (hi === null || gt(t.hi, hi)) hi = t.hi;
    }
    if (tail.unbounded > 0) hi = null;
    if (tail.unbounded < 0) lo = null;
    return { lower: lo, upper: hi, bounded: lo !== null && hi !== null };
  }
  /** The series Σ a(n). */
  series() {
    return new Series(this.ast, { variable: this.variable, from: this.from, params: this.params });
  }
}

/** sequence("(1 + 1/n)^n", { variable: "n", from: 1 }) */
export const sequence = (term, opts) => new Sequence(term, opts);

// ---- recursive sequences ----------------------------------------------------------------------

export class RecursiveSequence {
  constructor(next, { start, variable: x = "x", params = {} } = {}) {
    if (start === undefined) refuse("bad-sequence", "a recursive sequence needs start: its first term");
    this.ast = toAst(next);
    this.variable = x;
    this.start = q(start);
    this.params = Object.freeze({ ...params });
    Object.freeze(this);
  }
  toString() {
    return `${this.variable} -> ${format(this.ast)}, starting at ${this.start}`;
  }
  /**
   * The first `count` terms. Exact Rationals while the fractions stay under
   * `maxDigits` digits (default 300), then certified RationalIntervals.
   */
  terms(count = 10, { digits = 30, maxDigits = 300 } = {}) {
    const bits = bitsForDigits(digits) + 16;
    const env = paramEnv(this.params);
    const exactOK = !Object.keys(this.params).length;
    const out = [this.start];
    let exact = this.start;
    let iv = Iv.point(this.start);
    for (let i = 1; i < count; i++) {
      if (exact !== null) {
        const nextExact = exactOK ? exactAt(this.ast, this.variable, exact) : null;
        if (nextExact !== null && nextExact.denominator.toString().length + nextExact.numerator.toString().length <= maxDigits) {
          exact = nextExact;
          iv = Iv.point(exact);
          out.push(exact);
          continue;
        }
        exact = null;
      }
      iv = encloseAst(this.ast, { ...env, [this.variable]: iv }, bits).roundOut(bits);
      out.push(RI(iv));
    }
    return out;
  }
  /**
   * Fixed points g(x) = x in [a, b], each with the multiplier g′ there and
   * its kind: "attracting" (|g′| < 1), "repelling" (|g′| > 1) or "neutral or
   * undecided".
   */
  fixedPoints(interval, { digits = 20 } = {}) {
    const x = this.variable;
    const bits = bitsForDigits(digits) + 24;
    const env = paramEnv(this.params);
    const dg = simplify(derivative(this.ast, x));
    const found = zeros(simplify(op("-", this.ast, variable(x))), interval, { variable: x, params: this.params, digits }).exact();
    return found.filter((z) => z.lo !== undefined).map((z) => {
      const at = new Iv(q(z.lo), q(z.hi));
      const m = soft(() => encloseAst(dg, { ...env, [x]: at }, bits));
      const kind = !m ? "neutral or undecided" : lt(m.mag, ONE) ? "attracting" : gt(m.mig, ONE) ? "repelling" : "neutral or undecided";
      return { point: RI(at), multiplier: m ? RI(m) : null, kind, unique: z.unique ?? null };
    });
  }
  /**
   * The limit, proven by contraction. An interval I around a fixed point is
   * found with g(I) inside I and |g′| ≤ rate < 1 on I; once a term lies in I
   * the sequence converges to the one fixed point there. Returns
   * { limit, enters, rate, basin } or refuses.
   */
  limit(interval, { digits = 20, maxSteps = 400 } = {}) {
    const x = this.variable;
    const bits = bitsForDigits(digits) + 32;
    const env = paramEnv(this.params);
    const dg = simplify(derivative(this.ast, x));
    const basins = [];
    for (const p of this.fixedPoints(interval, { digits })) {
      if (p.kind !== "attracting") continue;
      const P = Iv.from(p.point);
      for (let j = 1; j <= 40; j++) {
        const d = new Rational(1n, 1n << BigInt(j));
        const I = new Iv(P.lo.subtract(d), P.hi.add(d));
        const slope = soft(() => encloseAst(dg, { ...env, [x]: I }, bits));
        if (!slope || !lt(slope.mag, ONE)) continue;
        // mean value form: g(I) ⊂ g(P) + g′(I)·(I − P)
        const image = soft(() => encloseAst(this.ast, { ...env, [x]: P }, bits).add(slope.mul(I.sub(P))));
        if (image && I.contains(image)) {
          basins.push({ p, I, rate: slope.mag });
          break;
        }
      }
    }
    if (!basins.length) return refuse("undecided", "no attracting fixed point with a proven basin was found in the interval");
    let X = Iv.point(this.start);
    for (let k = 0; k <= maxSteps; k++) {
      const hit = basins.find((b) => b.I.contains(X));
      if (hit) return { limit: hit.p.point, enters: k, rate: hit.rate, basin: RI(hit.I) };
      const next = soft(() => encloseAst(this.ast, { ...env, [x]: X }, bits).roundOut(bits));
      if (!next) return refuse("undefined", `the recursion is undefined at term ${k + 1}`);
      X = next;
    }
    return refuse("undecided", `no term among the first ${maxSteps} was proven to lie in the basin of a fixed point`);
  }
}

/** recursive("x/2 + 1/x", { start: 2 }): x₀ = start, x_{k+1} = g(x_k). */
export const recursive = (next, opts) => new RecursiveSequence(next, opts);

// ---- series -----------------------------------------------------------------------------------

const verdict = (test, v, reason, more = {}) => ({ test, verdict: v, reason, ...more });

export class Series {
  #d = null;
  constructor(term, { variable: n = "n", from = 1, params = {} } = {}) {
    this.ast = readTerm(term);
    this.variable = n;
    this.from = from;
    this.params = Object.freeze({ ...params });
    for (const name of freeVariables(this.ast)) if (name !== n && !(name in params)) refuse("unbound", `${name} has no value: pass it in params, or set variable`);
  }
  toString() {
    return `sum of ${format(this.ast)} for ${this.variable} from ${this.from}`;
  }
  get #env() {
    return paramEnv(this.params);
  }
  #parts(bits = 96) {
    this.#d ??= decompose(this.ast, this.variable, this.#env, bits);
    return this.#d;
  }
  /** One term: an exact Rational where possible, else a certified RationalInterval. */
  term(k, opts) {
    return new Sequence(this.ast, { variable: this.variable, from: this.from, params: this.params }).term(k, opts);
  }
  #termIv(k, bits) {
    const K = new Rational(BigInt(k));
    const exact = Object.keys(this.params).length ? null : exactAt(this.ast, this.variable, K);
    return exact !== null ? Iv.point(exact) : encloseAst(this.ast, { ...this.#env, [this.variable]: Iv.point(K) }, bits);
  }
  #partialIv(N, bits) {
    let sum = Iv.point(ZERO);
    for (let k = this.from; k <= N; k++) {
      sum = sum.add(this.#termIv(k, bits));
      if (N - this.from > 48) sum = sum.roundOut(bits + 32);
    }
    return sum;
  }
  /** The sum of the terms up to n = N: exact when every term is, else a certified RationalInterval. */
  partial(N, { digits = 20 } = {}) {
    const sum = this.#partialIv(N, bitsForDigits(digits) + 32);
    return sum.isPoint ? sum.lo : RI(sum);
  }

  // ---- the tests ----

  /** The nth-term test: a series whose terms do not go to 0 diverges. */
  divergenceTest({ digits = 20 } = {}) {
    const name = "nth term";
    let L;
    try {
      L = new Sequence(this.#absAst(), { variable: this.variable, from: this.from, params: this.params }).limit({ digits });
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      return verdict(name, "inconclusive", `the limit of the terms was not found (${e.message})`);
    }
    if (L === Infinity || L === -Infinity) return verdict(name, "divergent", "the terms grow without bound", { limit: L });
    if (gt(L.low, ZERO)) return verdict(name, "divergent", `|a(n)| tends to ${describeLimit(L)}, which is not 0`, { limit: L });
    if (L.low.equals(ZERO) && L.high.equals(ZERO)) return verdict(name, "inconclusive", "the terms tend to 0, which every convergent series does and some divergent ones do", { limit: L });
    return verdict(name, "inconclusive", "the limit of the terms could not be told from 0", { limit: L });
  }
  #absAst() {
    // |a(n)| with the alternating sign dropped, so that (−1)^n does not reach real-variable code
    const d = this.#parts();
    let ast = call("abs", d.rest);
    for (const g of d.geo) ast = op("*", ast, op("^", g.base, op("*", num(g.alpha), variable(this.variable))));
    return d.hasGamma ? this.ast : simplify(ast);
  }
  /** The ratio test: L = lim |a(n+1)/a(n)|. */
  ratioTest({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const d = this.#parts();
    const L = ratioLimit(d, this.variable, this.#env, bits);
    if (!L) return verdict("ratio", "inconclusive", "the limit of |a(n+1)/a(n)| was not found");
    if (L.kind === "infinite") return verdict("ratio", "divergent", "|a(n+1)/a(n)| grows without bound", { limit: Infinity });
    const limit = RI(L.iv);
    const text = describeLimit(limit);
    if (lt(L.iv.hi, ONE)) return verdict("ratio", "convergent", `|a(n+1)/a(n)| tends to ${text}, which is below 1: the series converges absolutely`, { limit });
    if (gt(L.iv.lo, ONE)) return verdict("ratio", "divergent", `|a(n+1)/a(n)| tends to ${text}, which is above 1`, { limit });
    return verdict("ratio", "inconclusive", `|a(n+1)/a(n)| tends to ${text}: the test says nothing at 1`, { limit });
  }
  /** The root test: L = lim |a(n)|^(1/n). */
  rootTest({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const d = this.#parts();
    if (d.hasGamma) return verdict("root", "inconclusive", "the nth root of a factorial is not followed here: use the ratio test");
    const n = this.variable;
    const k = onRays(n, this.#env, bits, 0, (ctx) => {
      const node = nodeAt(d.rest, ctx);
      if (node.osc || node.L.containsZero()) return undefined;
      spread(node, ctx);
      return { k: node.e.k };
    });
    if (!k) return verdict("root", "inconclusive", "the limit of |a(n)|^(1/n) was not found");
    const L = d.Q.mul(encloseAst(call("exp", num(k.k)), {}, bits));
    const limit = RI(L);
    const text = describeLimit(limit);
    if (lt(L.hi, ONE)) return verdict("root", "convergent", `|a(n)|^(1/n) tends to ${text}, which is below 1: the series converges absolutely`, { limit });
    if (gt(L.lo, ONE)) return verdict("root", "divergent", `|a(n)|^(1/n) tends to ${text}, which is above 1`, { limit });
    return verdict("root", "inconclusive", `|a(n)|^(1/n) tends to ${text}: the test says nothing at 1`, { limit });
  }
  /**
   * Limit comparison with the scale n^p·(log n)^m: the term is written as
   * ℓ·n^p·(log n)^m·(1 + something that dies out), and Σ n^p·(log n)^m
   * converges exactly when p < −1, or p = −1 and m < −1. Decides absolute
   * convergence.
   */
  comparisonTest({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const d = this.#parts();
    if (!d.plain) return verdict("comparison", "inconclusive", "the term has powers of n in an exponent or factorials: use the ratio test");
    const n = this.variable;
    const r = onRays(n, this.#env, bits, 0, (ctx) => {
      const node = nodeAt(d.rest, ctx);
      const ub = upperEnv(node, ctx);
      const leading = !node.osc && !node.L.containsZero();
      if (!leading && !(lt(ub.e.p, ONE.negate()) || ub.e.k.numerator < 0n || (ub.e.p.equals(ONE.negate()) && lt(ub.e.m, ONE.negate())))) return undefined;
      if (leading) spread(node, ctx);
      return { e: leading ? node.e : ub.e, L: leading ? node.L : null, C: ub.C };
    });
    if (!r) return verdict("comparison", "inconclusive", "no comparison with a power of n was proven");
    const part = (x, s) => (x.numerator === 0n ? "" : s(x.denominator === 1n ? `${x.numerator}` : `(${x})`));
    const like = [part(r.e.k, (t) => `exp(${t}*${n})`), part(r.e.p, (t) => (t === "1" ? n : `${n}^${t}`)), part(r.e.m, (t) => (t === "1" ? `log(${n})` : `log(${n})^${t}`))].filter(Boolean).join("*") || "1";
    const converges = r.e.k.numerator < 0n || (r.e.k.numerator === 0n && (lt(r.e.p, ONE.negate()) || (r.e.p.equals(ONE.negate()) && lt(r.e.m, ONE.negate()))));
    const more = { like, exponent: r.e.p, log: r.e.m, coefficient: r.L ? RI(r.L) : null };
    if (converges) return verdict("comparison", "convergent", r.L ? `|a(n)| behaves like ${describeLimit(RI(new Iv(r.L.mig, r.L.mag)))}·${like}, and the sum of ${like} converges: the series converges absolutely` : `|a(n)| is at most a constant times ${like}, and the sum of ${like} converges: the series converges absolutely`, more);
    if (r.L) return verdict("comparison", "divergent", `|a(n)| behaves like ${describeLimit(RI(new Iv(r.L.mig, r.L.mag)))}·${like}, and the sum of ${like} diverges${d.alternating ? ": the series does not converge absolutely" : ""}`, { ...more, absoluteOnly: d.alternating });
    return verdict("comparison", "inconclusive", "only an upper bound was found, and it is not summable", more);
  }
  /** The integral test, for terms that are positive and decreasing from some N on. */
  integralTest({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const d = this.#parts();
    if (!d.plain || d.alternating) return verdict("integral", "inconclusive", "the test needs a positive decreasing function of n; this term alternates or has n in an exponent");
    const n = this.variable;
    const da = simplify(derivative(d.rest, n));
    const r = onRays(n, this.#env, bits, this.from, (ctx, N) => {
      if (signOnRay(d.rest, ctx) <= 0 || signOnRay(da, ctx) >= 0) return undefined;
      const tail = tailOf(nodeAt(d.rest, ctx), ctx, format(d.rest));
      return { N, tail };
    });
    if (!r) return verdict("integral", "inconclusive", "the term was not proven positive and decreasing on a ray");
    if (r.tail.kind === "diverges") return verdict("integral", "divergent", `the term is positive and decreasing for ${n} ≥ ${r.N}, and its integral from ${r.N} to ∞ diverges`, { from: r.N });
    return verdict("integral", "convergent", `the term is positive and decreasing for ${n} ≥ ${r.N}, and its integral from ${r.N} to ∞ converges`, { from: r.N, integral: RI(r.tail.iv) });
  }
  /** The alternating series test: (−1)^n·b(n) with b decreasing to 0. */
  alternatingTest({ digits = 20 } = {}) {
    const bits = bitsForDigits(digits) + 24;
    const d = this.#parts();
    if (!d.alternating) return verdict("alternating", "inconclusive", "the signs of the terms do not alternate as (-1)^n");
    const r = this.#decreasingToZero(d, bits);
    if (!r) return verdict("alternating", "inconclusive", "the sizes of the terms were not proven to decrease to 0");
    return verdict("alternating", "convergent", `the signs alternate and |a(n)| decreases to 0 for ${this.variable} ≥ ${r.N}; the error after N terms is below the next term`, { from: r.N });
  }
  /**
   * For an alternating series: how many terms make the error below ε. The
   * alternating test proves |a(n)| decreasing to 0 from some n₀; from there the
   * error after the term n = N is at most |a(N + 1)|, so this is the first N
   * (with N + 1 ≥ n₀) where |a(N + 1)| ≤ ε, found by doubling and bisection.
   * Returns { terms, last, bound, from }: `terms` counted from the first index,
   * `last` the index of the last term used, `bound` = |a(last + 1)|.
   */
  termsForError(eps, { digits = 20 } = {}) {
    const e = toQ(eps);
    if (e.numerator <= 0n) refuse("bad-argument", "ε must be positive");
    const t = this.alternatingTest({ digits });
    if (t.verdict !== "convergent") refuse("not-alternating", `termsForError needs an alternating series whose terms are proven to decrease to 0 (${t.reason})`);
    const n0 = Math.max(t.from ?? this.from, this.from + 1);
    // is |a(k)| ≤ ε? decided from enclosures at rising precision
    const small = (k) => {
      for (let bits = bitsForDigits(digits) + 24; bits <= 8192; bits *= 2) {
        const a = this.#termIv(k, bits);
        if (le(a.mag, e)) return true;
        if (gt(a.mig, e)) return false;
      }
      refuse("precision", `|a(${k})| is too close to ε to decide`);
    };
    // the first k ≥ n0 with |a(k)| ≤ ε: the sizes decrease from n0, so the test is monotone
    let lo = n0 - 1;
    let hi = n0;
    while (!small(hi)) {
      lo = hi;
      hi = hi + Math.max(1, hi - n0 + 1); // doubling the distance from n0, whatever the sign of the index
      if (hi > 2 ** 52) refuse("budget", "the terms stay above ε for every index tried");
    }
    while (hi - lo > 1) {
      const mid = Math.floor((lo + hi) / 2);
      if (small(mid)) hi = mid;
      else lo = mid;
    }
    const last = hi - 1;
    const bound = this.#termIv(hi, bitsForDigits(digits) + 24);
    return { terms: last - this.from + 1, last, bound: bound.isPoint ? bound.lo.abs() : RI(new Iv(bound.mig, bound.mag)), from: n0, reason: `|a(n)| decreases to 0 for ${this.variable} ≥ ${t.from}, so the error after ${this.variable} = ${last} is below |a(${hi})| ≤ ${e}` };
  }
  /** N from which |a(n)| is proven decreasing with limit 0, or null. */
  #decreasingToZero(d, bits, from = this.from) {
    const n = this.variable;
    return onRays(n, this.#env, bits, from, (ctx, N) => {
      if (d.plain) {
        const node = nodeAt(d.rest, ctx);
        if (signE(node.e) >= 0) return undefined;
        upperEnv(node, ctx);
        const sg = signOnRay(d.rest, ctx);
        if (!sg) return undefined;
        const slope = signOnRay(simplify(derivative(d.rest, n)), ctx);
        return slope === -sg ? { N } : undefined;
      }
      // with powers or factorials: the ratio stays below 1
      const rho = d.Q.mag.multiply(supOnRay(d.ratioRest, ctx));
      return lt(rho, ONE) ? { N, rho } : undefined;
    });
  }
  /** Every test, in the order a course tries them. */
  tests(opts) {
    return [this.divergenceTest(opts), this.ratioTest(opts), this.rootTest(opts), this.comparisonTest(opts), this.integralTest(opts), this.alternatingTest(opts)];
  }
  /**
   * "absolutely convergent", "conditionally convergent", "divergent" or
   * "undecided", with the test that decided: { convergence, by, reason }.
   */
  convergence(opts = {}) {
    const d = this.#parts();
    const first = d.plain ? [this.comparisonTest(opts)] : [this.ratioTest(opts), this.rootTest(opts)];
    for (const t of first) if (t.verdict === "convergent") return { convergence: "absolutely convergent", by: t.test, reason: t.reason, test: t };
    const div = [...first.filter((t) => !t.absoluteOnly), this.divergenceTest(opts)].find((t) => t.verdict === "divergent");
    if (div) return { convergence: "divergent", by: div.test, reason: div.reason, test: div };
    const alt = this.alternatingTest(opts);
    if (alt.verdict === "convergent") {
      const absDiverges = first.find((t) => t.verdict === "divergent");
      if (absDiverges) return { convergence: "conditionally convergent", by: "alternating", reason: `${alt.reason}; and ${absDiverges.reason}`, test: alt };
      return { convergence: "convergent", by: "alternating", reason: `${alt.reason} (whether it converges absolutely was not decided)`, test: alt };
    }
    const integral = this.integralTest(opts);
    if (integral.verdict !== "inconclusive") return { convergence: integral.verdict === "convergent" ? "absolutely convergent" : "divergent", by: "integral", reason: integral.reason, test: integral };
    return { convergence: "undecided", by: null, reason: "no test decided" };
  }

  /**
   * The tail Σ_{n > N} a(n) as an interval, with the argument used:
   * { iv, by }. Throws AnalyticError where no bound holds from N on.
   */
  #tail(N, ctx, d, bits) {
    const n = this.variable;
    const env = this.#env;
    if (!d.plain) {
      // ratio: |a(n+1)| ≤ ρ·|a(n)| for n ≥ N, so the tail is at most |a(N+1)|/(1 − ρ)
      const rho = d.Q.mag.multiply(supOnRay(d.ratioRest, ctx));
      if (!lt(rho, ONE)) refuse("larger-x", "the ratio is not yet below 1");
      const first = this.#termIv(N + 1, bits);
      if (d.alternating) {
        // decreasing sizes and alternating signs: the tail lies between 0 and its first term
        return { iv: first.hull(Iv.point(ZERO)), by: "alternating series bound: the tail lies between 0 and its first term" };
      }
      const U = first.mag.divide(ONE.subtract(rho));
      const sg = signOnRay(d.rest, ctx);
      return { iv: sg > 0 ? new Iv(first.lo, U) : sg < 0 ? new Iv(U.negate(), first.hi) : new Iv(U.negate(), U), by: `ratio bound: |a(n+1)/a(n)| ≤ ${rho.toNumber().toPrecision(4)} from n = ${N}, so the tail is at most |a(${N + 1})|/(1 − ratio)` };
    }
    const a = d.rest;
    if (d.alternating) {
      const node = nodeAt(a, ctx);
      if (signE(node.e) >= 0) refuse("divergent", "the terms do not tend to 0");
      upperEnv(node, ctx);
      const sg = signOnRay(a, ctx);
      const slope = signOnRay(simplify(derivative(a, n)), ctx);
      if (!sg || slope !== -sg) refuse("larger-x", "the sizes are not yet decreasing");
      const first = this.#termIv(N + 1, bits);
      const convex = soft(() => signOnRay(simplify(derivative(derivative(a, n), n)), ctx) === sg, false);
      if (convex) {
        // the steps b(n) − b(n+1) shrink too, which pins the tail between half its first term and half the term before
        const prev = this.#termIv(N, bits);
        return { iv: first.scale(HALF).hull(prev.scale(HALF).neg()), by: `alternating series with convex sizes: the tail lies between a(${N + 1})/2 and −a(${N})/2` };
      }
      return { iv: first.hull(Iv.point(ZERO)), by: "alternating series bound: the tail lies between 0 and its first term" };
    }
    const node = nodeAt(a, ctx);
    const sg = signOnRay(a, ctx);
    const d1 = simplify(derivative(a, n));
    if (sg && signOnRay(d1, ctx) === -sg) {
      const tail = tailOf(node, ctx, format(a));
      if (tail.kind === "diverges") refuse("divergent", "the integral test shows the series diverges");
      if (!tail.loose) {
        const I = tail.iv; // ∫_N^∞ a
        const aN = this.#termIv(N, bits);
        const convex = soft(() => signOnRay(simplify(derivative(d1, n)), ctx) === sg, false);
        if (convex) {
          // trapezoids lie above a convex curve and midpoint rectangles below it
          const half = quad1(a, n, env, new Rational(BigInt(N)), new Rational(BigInt(2 * N + 1), 2n), { tol: new Rational(1n, 1n << BigInt(bits - 8)), bits }).iv;
          const lo = I.sub(aN.scale(HALF));
          const hi = I.sub(half);
          const iv = sg > 0 ? new Iv(lo.lo, hi.hi) : new Iv(hi.lo, lo.hi);
          return { iv, by: `integral bounds for a convex term: the tail lies between ∫ from ${N} to ∞ minus a(${N})/2 and ∫ from ${N} + 1/2 to ∞` };
        }
        const iv = sg > 0 ? new Iv(I.lo.subtract(aN.hi), I.hi) : new Iv(I.lo, I.hi.subtract(aN.lo));
        return { iv, by: `integral test bounds: the tail lies between ∫ from ${N + 1} to ∞ and ∫ from ${N} to ∞` };
      }
    }
    // only a bound on the size: |a(x)| ≤ C·T(x) with T decreasing, so the tail is at most C·∫_N^∞ T
    const ub = upperEnv(node, ctx);
    if (!decreasing(ub.e, ctx)) refuse("larger-x", "the bound is not yet decreasing");
    if (!(ub.e.k.numerator < 0n || lt(ub.e.p, ONE.negate()) || (ub.e.p.equals(ONE.negate()) && lt(ub.e.m, ONE.negate())))) refuse("undecided", "the bound on the terms is not summable");
    const U = tailUpper(ub, ctx);
    return { iv: new Iv(U.negate(), U), by: `comparison: |a(n)| is below a multiple of a summable power from n = ${N}, and the tail is below its integral` };
  }
  /**
   * The sum: { enclosure, terms, tail, by, met }. `enclosure` is a
   * RationalInterval that holds the sum: the first `terms` terms plus the
   * proven interval `tail` for all the rest. `met` says whether the width
   * asked for (digits, default 8) was reached within maxTerms (default 8192).
   * Refuses when the series is not proven to converge.
   */
  sum({ digits = 8, maxTerms = 8192 } = {}) {
    const bits = Math.max(96, bitsForDigits(digits) + 48);
    const d = this.#parts();
    const tol = tenTo(digits);
    let best = null;
    let why = null;
    for (const N of NS) {
      if (N < this.from || N > maxTerms) continue;
      const ctx = rayContext(this.variable, this.#env, new Rational(BigInt(N)), bits);
      let t;
      try {
        t = this.#tail(N, ctx, d, bits);
      } catch (e) {
        if (!(e instanceof AnalyticError)) throw e;
        why = e;
        if (e.code === "divergent") break;
        continue;
      }
      best = { N, ...t };
      if (le(t.iv.width, tol)) break;
    }
    if (!best) {
      const c = this.convergence();
      if (c.convergence === "divergent") return refuse("divergent", `the series diverges (${c.by} test: ${c.reason})`);
      return refuse("undecided", `no bound on the tail of the series was proven${why ? ` (${why.message})` : ""}`);
    }
    const partial = this.#partialIv(best.N, bits);
    const total = partial.add(best.iv);
    return { enclosure: RI(total), terms: best.N - this.from + 1, upTo: best.N, partial: partial.isPoint ? partial.lo : RI(partial), tail: RI(best.iv), by: best.by, met: le(total.width, tol) };
  }
}

/** sum("1/n^2", { variable: "n", from: 1 }): the series Σ a(n). */
export const sum = (term, opts) => new Series(term, opts);

// ---- power series -----------------------------------------------------------------------------

export class PowerSeries {
  constructor(coefficient, { index = "n", from = 0, centre = 0, variable: x = "x" } = {}) {
    this.coefficientAst = readTerm(coefficient);
    this.index = index;
    this.from = from;
    this.centre = q(centre);
    this.variable = x;
    Object.freeze(this);
  }
  toString() {
    const h = this.centre.numerator === 0n ? this.variable : `(${this.variable} - ${this.centre})`;
    return `sum of (${format(this.coefficientAst)})*${h}^${this.index} for ${this.index} from ${this.from}`;
  }
  /** c(n): exact where the formula is rational. */
  coefficient(k, opts) {
    return new Sequence(this.coefficientAst, { variable: this.index }).term(k, opts);
  }
  /**
   * The radius of convergence R = 1 / lim |c(n+1)/c(n)|: { radius, limit, by }
   * with radius a RationalInterval, 0 or Infinity.
   */
  radius({ digits = 20 } = {}) {
    const t = new Series(this.coefficientAst, { variable: this.index, from: this.from }).ratioTest({ digits });
    if (t.limit === undefined) return refuse("undecided", `the radius of convergence was not found: ${t.reason}`);
    if (t.limit === Infinity) return { radius: 0, limit: Infinity, by: "ratio" };
    if (t.limit.high.numerator === 0n) return { radius: Infinity, limit: t.limit, by: "ratio" };
    if (t.limit.low.numerator === 0n) return refuse("undecided", "the limit of |c(n+1)/c(n)| could not be told from 0");
    return { radius: new RationalInterval(t.limit.high.reciprocal(), t.limit.low.reciprocal()), limit: t.limit, by: "ratio" };
  }
  /** The numerical series at a rational point x. */
  at(x) {
    const h = q(x).subtract(this.centre);
    return new Series(op("*", this.coefficientAst, op("^", num(h), variable(this.index))), { variable: this.index, from: this.from });
  }
  /**
   * The interval of convergence, with each end examined:
   * { radius, left, right, text }. `left` and `right` are
   * { point, convergence, by, reason } when the radius is an exact number.
   */
  interval(opts = {}) {
    const r = this.radius(opts);
    const c = this.centre;
    if (r.radius === Infinity) return { radius: Infinity, left: null, right: null, text: "(-inf, inf)" };
    if (r.radius === 0) return { radius: 0, left: null, right: null, text: `{${c}}` };
    if (!r.radius.low.equals(r.radius.high)) return { radius: r.radius, left: null, right: null, text: `centre ${c}, radius about ${r.radius.low.toNumber()}; the ends were not examined because the radius is not an exact rational` };
    const R = r.radius.low;
    const end = (point) => ({ point, ...this.at(point).convergence(opts) });
    const left = end(c.subtract(R));
    const right = end(c.add(R));
    const closed = (e) => /convergent/.test(e.convergence) && e.convergence !== "undecided";
    const mark = (e, open, shut) => (e.convergence === "undecided" ? "?" : closed(e) ? shut : open);
    return { radius: R, left, right, text: `${mark(left, "(", "[")}${left.point}, ${right.point}${mark(right, ")", "]")}` };
  }
  /** The partial sum up to the power N, as an AnalyticFunction of x (coefficients must be exact). */
  partial(N) {
    let ast = num(0);
    const h = this.centre.numerator === 0n ? variable(this.variable) : op("-", variable(this.variable), num(this.centre));
    for (let k = this.from; k <= N; k++) {
      const c = this.coefficient(k);
      if (!(c instanceof Rational)) refuse("not-exact", "partial(N) needs coefficients that are exact rationals");
      if (c.numerator !== 0n) ast = op("+", ast, k === 0 ? num(c) : op("*", num(c), op("^", h, num(k))));
    }
    return new AnalyticFunction(simplify(ast), { variable: this.variable });
  }
  /** The value at a rational x inside the interval of convergence: see Series.sum. */
  value(x, opts) {
    return this.at(x).sum(opts);
  }
  /** Term by term: Σ (n + 1)·c(n + 1)·(x − a)^n. Same radius. */
  derivative() {
    const n = variable(this.index);
    const shifted = subst(this.coefficientAst, this.index, op("+", n, num(1)));
    return new PowerSeries(simplify(op("*", op("+", n, num(1)), shifted)), { index: this.index, from: Math.max(0, this.from - 1), centre: this.centre, variable: this.variable });
  }
  /** Term by term, with constant 0: Σ c(n − 1)/n·(x − a)^n. Same radius. */
  integral() {
    const n = variable(this.index);
    const shifted = subst(this.coefficientAst, this.index, op("-", n, num(1)));
    return new PowerSeries(simplify(op("/", shifted, n)), { index: this.index, from: this.from + 1, centre: this.centre, variable: this.variable });
  }
}

/** powerSeries("1/n", { from: 1 }): Σ c(n)·(x − centre)^n. */
export const powerSeries = (coefficient, opts) => new PowerSeries(coefficient, opts);

/**
 * Taylor's theorem with its remainder, checked. For f on [a, b] about c:
 * { coefficients, M, bound, actual, holds }. M encloses max |f^(n+1)| on the
 * interval, bound = M·r^(n+1)/(n+1)! is Lagrange's bound on |f − T_n|, and
 * `actual` encloses the true maximum of |f − T_n| there.
 */
export function taylorRemainder(f, { about = 0, order = 4, on, variable: x = "x", digits = 10 } = {}) {
  if (!on) refuse("bad-arguments", "taylorRemainder needs on: [a, b]");
  const F = f instanceof AnalyticFunction ? f : new AnalyticFunction(f, { variable: x });
  const c = q(about);
  const I = Iv.from([q(on[0]), q(on[1])]);
  const coefficients = F.taylor(c, order, { digits: digits + 10 });
  let d = F.ast;
  for (let k = 0; k <= order; k++) d = simplify(derivative(d, F.variable));
  const range = new AnalyticFunction(d, { variable: F.variable }).range(I.toRationalInterval(), { digits }).exact();
  const M = Iv.from(range).mag;
  const r = lt(c.subtract(I.lo).abs(), I.hi.subtract(c).abs()) ? I.hi.subtract(c).abs() : c.subtract(I.lo).abs();
  const bound = M.multiply(r.pow(order + 1)).divide(new Rational(factorial(order + 1)));
  // T_n with coefficients at the midpoints of their enclosures; the widths go into the comparison
  const h = c.numerator === 0n ? variable(F.variable) : op("-", variable(F.variable), num(c));
  let T = num(0);
  let slack = ZERO;
  coefficients.forEach((iv, k) => {
    const mid = iv.low.add(iv.high).divide(TWO);
    T = op("+", T, k === 0 ? num(mid) : op("*", num(mid), op("^", h, num(k))));
    slack = slack.add(iv.high.subtract(iv.low).divide(TWO).multiply(r.pow(k)));
  });
  const diff = new AnalyticFunction(simplify(op("-", F.ast, T)), { variable: F.variable }).range(I.toRationalInterval(), { digits }).exact();
  const D = Iv.from(diff);
  // the largest value is at least what is seen at the ends, and at most the range's bound
  const ends = [I.lo, I.hi].map((p) => soft(() => encloseAst(op("-", F.ast, T), { [F.variable]: Iv.point(p) }, bitsForDigits(digits) + 32).mig, ZERO));
  const seen = ends.reduce((m, e) => (gt(e, m) ? e : m), ZERO);
  const actual = new RationalInterval(gt(seen.subtract(slack), ZERO) ? seen.subtract(slack) : ZERO, D.mag.add(slack));
  return { coefficients, M: new RationalInterval(Iv.from(range).mig, M), radius: r, bound, actual, holds: le(actual.low, bound) };
}

// ---- sequences of functions -------------------------------------------------------------------

/**
 * 1^e = 1, and 0^e = 0 when e = k·n with k > 0 (so e ≥ k for every n ≥ 1):
 * what substituting x = 1 or x = 0 into x^n leaves, folded before the limit
 * code meets an exponential of 0·log.
 */
function foldPowers(ast, n) {
  if (ast.type !== "op" && ast.type !== "call") return ast;
  const args = ast.args.map((a) => foldPowers(a, n));
  if (ast.type === "op" && ast.op === "^") {
    const base = constantRational(args[0]);
    if (base !== null && base.equals(ONE)) return num(ONE);
    if (base !== null && base.numerator === 0n) {
      const e = args[1];
      const k = e.type === "var" && e.name === n ? ONE : e.type === "op" && e.op === "*" && e.args[1]?.type === "var" && e.args[1].name === n ? constantRational(e.args[0]) : null;
      if (k !== null && gt(k, ZERO)) return num(ZERO);
    }
  }
  const out = { ...ast, args };
  return args.every((a, i) => a === ast.args[i]) ? ast : simplify(out);
}

export class FunctionSequence {
  constructor(term, { variable: x = "x", index = "n" } = {}) {
    this.ast = readTerm(term);
    this.variable = x;
    this.index = index;
    Object.freeze(this);
  }
  toString() {
    return format(this.ast);
  }
  /** f_n as an AnalyticFunction of x. */
  member(n) {
    return new AnalyticFunction(simplify(subst(this.ast, this.index, num(n))), { variable: this.variable });
  }
  /** The pointwise limit at a rational x: a RationalInterval or ±Infinity. */
  pointwise(x, opts) {
    // x is put into the term itself: as a parameter it was never substituted by the limit code
    const term = foldPowers(simplify(subst(this.ast, this.variable, num(q(x)))), this.index);
    const lone = constantRational(term);
    if (lone !== null) return new RationalInterval(lone, lone);
    return new Sequence(term, { variable: this.index }).limit(opts);
  }
  /**
   * sup over [a, b] of |f_n − f|, enclosed: the upper end is a proven bound
   * on the supremum, and the lower end is a value the difference takes.
   */
  supDistance(n, interval, limit = "0", { digits = 8, samples = 33 } = {}) {
    const I = Iv.from([q(interval[0]), q(interval[1])]);
    const diff = simplify(op("-", subst(this.ast, this.index, num(n)), toAst(limit)));
    const range = Iv.from(new AnalyticFunction(diff, { variable: this.variable }).range(I.toRationalInterval(), { digits }).exact());
    const bits = bitsForDigits(digits) + 24;
    let seen = ZERO;
    for (let i = 0; i < samples; i++) {
      const p = I.lo.add(I.width.multiply(new Rational(BigInt(i), BigInt(samples - 1))));
      const val = soft(() => encloseAst(diff, { [this.variable]: Iv.point(p) }, bits).mig, ZERO);
      if (gt(val, seen)) seen = val;
    }
    return new RationalInterval(seen, range.mag);
  }
  /**
   * Is the convergence to `limit` uniform on [a, b]?
   * { verdict, table, reason }. The table gives the enclosed supremum of
   * |f_n − f| for each n tried. "uniform" is returned only with a proof (a
   * bound on the difference that holds for every x in the interval at once
   * and tends to 0); "not uniform so far" means the suprema in the table are
   * proven to stay above a positive number for the n tried, which is evidence
   * and not a proof about every n.
   */
  uniform(interval, limit = "0", { ns = [1, 2, 4, 8, 16, 32], digits = 8 } = {}) {
    const I = Iv.from([q(interval[0]), q(interval[1])]);
    const table = ns.map((n) => ({ n, sup: soft(() => this.supDistance(n, interval, limit, { digits })) }));
    const bits = bitsForDigits(digits) + 32;
    const diff = simplify(op("-", this.ast, toAst(limit)));
    const decided = decideUniform(this, diff, I, digits);
    if (decided) return { ...decided, table };
    if (table.some((r) => r.sup === null)) return { verdict: "undecided", table, reason: "the difference could not be bounded on the interval" };
    // the same asymptotic bound, with x standing for the whole interval
    const proof = onRays(this.index, { [this.variable]: I }, bits, 0, (ctx, N) => {
      const node = nodeAt(diff, ctx);
      if (signE(node.e) >= 0) return undefined;
      const ub = upperEnv(node, ctx);
      return { N, bound: envAt(ub, ctx) };
    }, [4, 8, 16, 32, 64, 128, 256, 1024, 4096]);
    if (proof) return { verdict: "uniform", table, reason: `for every x in the interval at once, |f_n(x) − f(x)| is below a bound that tends to 0 (it is at most ${proof.bound.toNumber().toPrecision(3)} from n = ${proof.N})`, from: proof.N };
    const last = table[table.length - 1].sup;
    const floor = table.reduce((m, r) => (lt(r.sup.low, m) ? r.sup.low : m), table[0].sup.low);
    if (gt(floor, ZERO) && ge(last.low, table[0].sup.low.divide(new Rational(4n)))) return { verdict: "not uniform so far", table, reason: `the supremum of |f_n − f| stays above ${floor.toNumber().toPrecision(3)} for every n tried; that is evidence against uniform convergence, not a proof for all n` };
    return { verdict: "undecided", table, reason: "the suprema in the table shrink, but no bound for every n was proven" };
  }
}

/** functionSequence("x^n", { variable: "x", index: "n" }) */
export const functionSequence = (term, opts) => new FunctionSequence(term, opts);


// ---- lim sup, lim inf, suprema and an N for ε ---------------------------------------------------

const showValue = (L) => (L === Infinity ? "∞" : L === -Infinity ? "-∞" : L instanceof Rational ? `${L}` : L.low.equals(L.high) ? `${L.low}` : `about ${L.low.add(L.high).divide(TWO).toNumber()}`);
const lowEnd = (L) => (L === Infinity || L === -Infinity ? L : L instanceof Rational ? L : L.low);
const highEnd = (L) => (L === Infinity || L === -Infinity ? L : L instanceof Rational ? L : L.high);
/** a < b for values that may be ±Infinity or Rationals. */
const below = (a, b) => (a === b ? false : a === -Infinity || b === Infinity ? true : a === Infinity || b === -Infinity ? false : lt(a, b));
/** 1, −1, 0 (equal points) or null (enclosures overlap) for two limits/values. */
function compareValues(a, b) {
  if (below(highEnd(a), lowEnd(b))) return -1;
  if (below(highEnd(b), lowEnd(a))) return 1;
  const point = (L) => L === Infinity || L === -Infinity || L instanceof Rational || L.low.equals(L.high);
  if (point(a) && point(b)) return 0;
  return null;
}
const tidyValue = (L) => (L instanceof RationalInterval && L.low.equals(L.high) ? L.low : L);

/** The subsequences a(p·m + r) of a sequence with periodic factors, each an ordinary Sequence in m. */
function subsequencesOf(seq) {
  const n = seq.variable;
  const per = periodOf(seq.ast, n);
  if (per.period === null) refuse("undecided", per.blocker);
  const p = per.period;
  if (p === 1) return { period: 1, list: [{ residue: 0, period: 1, along: n, sequence: seq, index: (m) => m }] };
  const list = [];
  // the subsequences count in m (k when the index is already called m)
  const mv = n === "m" ? "k" : "m";
  const rename = (t) => (t.type === "var" ? (t.name === n ? variable(mv) : t) : t.args ? { ...t, args: t.args.map(rename) } : t);
  for (let r = 0; r < p; r++) {
    const term = rename(alongResidue(seq.ast, n, p, r));
    const m0 = Math.ceil((seq.from - r) / p);
    list.push({
      residue: r,
      period: p,
      along: `${n} = ${p}${mv}${r ? ` + ${r}` : ""}`,
      sequence: new Sequence(term, { variable: mv, from: m0, params: seq.params }),
      index: (m) => p * m + r,
    });
  }
  return { period: p, list };
}

/**
 * The accumulation points of a sequence with periodic factors: the limit of
 * each subsequence a(p·m + r). → { period, subsequences: [{ along, term,
 * limit }], limsup, liminf, converges }. Refuses where a subsequence has no
 * proven limit, or where a factor such as sin(n) does not repeat.
 */
function accumulation(seq, { digits = 20 } = {}) {
  const { period, list } = subsequencesOf(seq);
  if (period === 1) {
    const f = new AnalyticFunction(seq.ast, { variable: seq.variable, params: seq.params });
    const L = f.limit("inf", { digits });
    return { period, subsequences: [{ along: seq.variable, term: format(seq.ast), limit: L }], limsup: L, liminf: L, converges: true };
  }
  const subs = list.map((u) => ({ along: u.along, term: format(u.sequence.ast), limit: u.sequence.limit({ digits }) }));
  let hi = subs[0].limit;
  let lo = subs[0].limit;
  let converges = true;
  for (const u of subs.slice(1)) {
    const c = compareValues(u.limit, hi);
    if (c === null || compareValues(u.limit, lo) === null) refuse("undecided", `the limits along ${subs.map((x) => x.along).join(" and ")} are too close to tell apart at this precision`);
    if (c > 0) hi = u.limit;
    if (compareValues(u.limit, lo) < 0) lo = u.limit;
  }
  converges = compareValues(hi, lo) === 0;
  return { period, subsequences: subs, limsup: hi, liminf: lo, converges };
}

Sequence.prototype.accumulation = function (opts) {
  return accumulation(this, opts);
};
/** lim sup a(n): the largest limit of a subsequence a(p·m + r). A RationalInterval or ±Infinity. */
Sequence.prototype.limsup = function (opts) {
  return accumulation(this, opts).limsup;
};
/** lim inf a(n). */
Sequence.prototype.liminf = function (opts) {
  return accumulation(this, opts).liminf;
};

/**
 * sup or inf of one sequence without periodic factors, from its proven
 * monotone tail: the tail's sup is its limit (not attained) when it rises and
 * its first term when it falls; the finitely many terms before the tail are
 * compared one by one.
 */
function extremeOfPlain(seq, sign, digits) {
  const mono = seq.monotone({ digits });
  const val = (k) => seq.term(k, { digits });
  const better = (a, b) => {
    const c = compareValues(a, b);
    if (c === null) refuse("precision", "two candidates for the extreme value are too close to tell apart");
    return sign > 0 ? c : -c;
  };
  if (mono.direction === "constant") return { value: val(seq.from), attained: true, at: seq.from, reason: "the sequence is constant" };
  const rising = (mono.direction === "increasing") === (sign > 0); // moving towards the extreme side
  let best;
  if (rising) {
    const L = seq.limit({ digits });
    best = { value: tidyValue(L), attained: false, at: null, reason: `the terms ${mono.direction === "increasing" ? "rise" : "fall"} for ${seq.variable} ≥ ${mono.from}, so they approach their limit ${showValue(L)} without reaching it` };
  } else {
    best = { value: val(mono.from), attained: true, at: mono.from, reason: `the terms ${mono.direction === "increasing" ? "rise" : "fall"} for ${seq.variable} ≥ ${mono.from}, so the term at ${seq.variable} = ${mono.from} is the ${sign > 0 ? "largest" : "smallest"} of them` };
  }
  for (let k = mono.from - 1; k >= seq.from; k--) {
    const t = val(k);
    const c = better(t, best.value);
    if (c > 0 || (c === 0 && !best.attained)) best = { value: t, attained: true, at: k, reason: `the term at ${seq.variable} = ${k} is ${sign > 0 ? "above" : "below"} every later term` };
  }
  return best;
}
function extremeOf(seq, sign, { digits = 20 } = {}) {
  const { period, list } = subsequencesOf(seq);
  let best = null;
  for (const u of list) {
    const e = extremeOfPlain(u.sequence, sign, digits);
    const cand = { ...e, at: e.at === null ? null : u.index(e.at), along: period > 1 ? u.along : undefined };
    if (best === null) best = cand;
    else {
      const c = compareValues(cand.value, best.value);
      if (c === null) refuse("precision", "two candidates for the extreme value are too close to tell apart");
      if ((sign > 0 ? c : -c) > 0 || (c === 0 && cand.attained && !best.attained)) best = cand;
    }
  }
  const out = { value: best.value, attained: best.attained, at: best.at, reason: period > 1 ? `along ${best.along}: ${best.reason}` : best.reason };
  if (out.value === Infinity || out.value === -Infinity) out.reason = `the terms are unbounded ${sign > 0 ? "above" : "below"}`;
  return out;
}
/**
 * The supremum of the terms: { value, attained, at, reason }. `value` is a
 * Rational, a RationalInterval that encloses it, or Infinity; `attained` says
 * whether some term equals it, and `at` is that index.
 */
Sequence.prototype.supremum = function (opts) {
  return extremeOf(this, 1, opts);
};
/** The infimum of the terms: { value, attained, at, reason }. */
Sequence.prototype.infimum = function (opts) {
  return extremeOf(this, -1, opts);
};

const memoBits = (f) => {
  const seen = new Map();
  return (bits) => {
    if (!seen.has(bits)) seen.set(bits, f(bits));
    return seen.get(bits);
  };
};
/** |a(k) − L| as an interval, from an exact term where there is one. */
function distanceAt(seq, k, L, bits) {
  const K = new Rational(BigInt(k));
  // an exact value is used unless it would be enormous: a power whose exponent moves, far out
  const moving = (t) => (t.type === "op" && t.op === "^" && depends(t.args[1], seq.variable)) || (t.args ? t.args.some(moving) : false);
  const exact = Object.keys(seq.params).length || (k > 512 && moving(seq.ast)) ? null : exactAt(seq.ast, seq.variable, K);
  let a = null;
  if (exact !== null) a = Iv.point(exact);
  else {
    try {
      a = encloseAst(seq.ast, { ...paramEnv(seq.params), [seq.variable]: Iv.point(K) }, bits);
    } catch (err) {
      // (−1)^k has no real-variable enclosure: fall back on the exact value
      const ex = err instanceof AnalyticError ? exactAt(seq.ast, seq.variable, K) : null;
      if (ex === null) throw err;
      a = Iv.point(ex);
    }
  }
  const d = a.sub(L);
  return new Iv(d.mig, d.mag);
}
/** Is |a(k) − L| < ε? Decided from enclosures at rising precision. */
function closeAt(seq, k, L, e, digits) {
  for (let bits = bitsForDigits(digits) + 24; bits <= 4096; bits *= 2) {
    const d = distanceAt(seq, k, L(bits), bits);
    if (lt(d.hi, e)) return true;
    if (ge(d.lo, e)) return false;
  }
  return refuse("precision", `|a(${k}) − L| is too close to ε to decide`);
}

/**
 * For one sequence without periodic factors: the least N with
 * |a(n) − L| < ε for every n ≥ N, and how the tail is proven.
 */
function thresholdPlain(seq, L, e, { digits, maxWalk }) {
  const n = seq.variable;
  const ok = (k) => closeAt(seq, k, L, e, digits);
  const mono = soft(() => seq.monotone({ digits }));
  if (mono && mono.direction === "constant") return { N: seq.from, least: true, method: "constant", detail: "the sequence is constant" };
  if (mono) {
    // a monotone convergent tail moves towards its limit, so |a(n) − L| never grows from mono.from on
    const M = mono.from;
    let hi = M;
    let lo = M - 1;
    for (let step = 1; !ok(hi); step *= 2) {
      lo = hi;
      hi += step;
      if (hi > 2 ** 52) refuse("budget", "no index was found where the terms are within ε of the limit");
    }
    while (hi - lo > 1 && lo >= M) {
      const mid = Math.floor((lo + hi) / 2);
      if (ok(mid)) hi = mid;
      else lo = mid;
    }
    let N = hi;
    if (N === M) for (let k = M - 1; k >= seq.from && ok(k); k--) N = k;
    return {
      N,
      least: true,
      method: "monotone tail",
      monotone: mono,
      detail: `the terms ${mono.direction === "increasing" ? "rise" : "fall"} to the limit for ${n} ≥ ${M}, so |a(${n}) − L| never grows from there; it is below ε at ${n} = ${N}${N > seq.from ? ` and not at ${n} = ${N - 1}` : ""}`,
    };
  }
  // no monotone tail: an explicit dominating sequence C·e^(k·n)·n^p·(log n)^m from the asymptotic form
  const bits = bitsForDigits(digits) + 24;
  const diff = op("-", seq.ast, variable("__limit"));
  const env = { ...paramEnv(seq.params), __limit: L(bits) };
  const dom = onRays(n, env, bits, seq.from, (ctx, X) => {
    const node = nodeAt(diff, ctx);
    const ub = !node.osc && node.r && node.L.mag.numerator === 0n ? { C: node.r.C, e: addE(node.e, node.r.e) } : upperEnv(node, ctx);
    if (signE(ub.e) >= 0 || !decreasing(ub.e, ctx)) return undefined;
    envAt(ub, ctx);
    return { X, ub };
  }, [4, 8, ...NS]);
  if (!dom) refuse("undecided", `no bound on |a(${n}) − L| that tends to 0 was proven`);
  const boundAt = (k) => envAt(dom.ub, rayContext(n, env, new Rational(BigInt(k)), bits));
  let hi = dom.X;
  let lo = dom.X - 1;
  for (let step = 1; !lt(boundAt(hi), e); step *= 2) {
    lo = hi;
    hi += step;
    if (hi > 2 ** 52) refuse("budget", "the dominating sequence stays above ε for every index tried");
  }
  while (hi - lo > 1 && lo >= dom.X) {
    const mid = Math.floor((lo + hi) / 2);
    if (lt(boundAt(mid), e)) hi = mid;
    else lo = mid;
  }
  // every n ≥ hi is within ε; walk back through the terms themselves to the last one that is not
  let N = hi;
  let least = false;
  for (let steps = 0; steps <= maxWalk; steps++) {
    if (N === seq.from) {
      least = true;
      break;
    }
    if (!ok(N - 1)) {
      least = true;
      break;
    }
    N -= 1;
  }
  const { C, e: E } = dom.ub;
  const parts = [];
  if (E.k.numerator !== 0n) parts.push(`e^(${E.k}·${n})`);
  if (E.p.numerator !== 0n) parts.push(`${n}^(${E.p})`);
  if (E.m.numerator !== 0n) parts.push(`(log ${n})^(${E.m})`);
  const text = `${C.toNumber().toPrecision(4)}·${parts.join("·")}`;
  return {
    N,
    least,
    method: "dominating sequence",
    bound: { C, exponents: E, from: dom.X, text, belowEpsilonFrom: hi },
    detail: `|a(${n}) − L| ≤ ${text} for ${n} ≥ ${dom.X}, which decreases and is below ε from ${n} = ${hi}; the terms before that were checked one by one${least ? `, and ${N > seq.from ? `the term at ${n} = ${N - 1} is not within ε` : "all of them are within ε"}` : ` back to ${n} = ${N}`}`,
  };
}

/**
 * An N for a given ε: |a(n) − L| < ε for every n ≥ N, with its proof.
 *
 *   sequence("1/sqrt(n)").nFor("1/100")      // N = 10001, the least one
 *
 * L is the limit (found, or given as { limit } and then checked against the
 * one found). The tail is proven by a monotone tail where the sequence has
 * one, by an explicit dominating sequence otherwise, and along each
 * subsequence n = p·m + r when the term has periodic factors such as (−1)^n.
 * → { N, least, limit, epsilon, method, reason, certificate }; `least` says
 * N − 1 would not do. verifyCertificate(result.certificate) rechecks it.
 */
Sequence.prototype.nFor = function (eps, { limit, digits = 20, maxWalk = 200000 } = {}) {
  const e = q(eps);
  if (e.numerator <= 0n) refuse("bad-argument", "ε must be positive");
  const found = this.limit({ digits: Math.max(digits, 30) });
  if (found === Infinity || found === -Infinity) refuse("no-limit", "the sequence is unbounded, so no N exists for any ε");
  let L = memoBits((bits) => (bits <= bitsForDigits(Math.max(digits, 30)) ? Iv.from(found) : Iv.from(this.limit({ digits: Math.ceil(bits / 3) }))));
  let limitText = showValue(found);
  if (limit !== undefined) {
    const ast = toAst(typeof limit === "number" ? String(limit) : limit instanceof Rational ? num(limit) : limit);
    const given = (bits) => encloseAst(ast, {}, bits);
    const g = given(bitsForDigits(digits) + 24);
    const f = Iv.from(found);
    if (lt(g.hi, f.lo) || gt(g.lo, f.hi)) refuse("bad-argument", `${format(ast)} is not the limit, which is ${limitText}`);
    L = memoBits(given);
    limitText = format(ast);
  }
  const { period, list } = subsequencesOf(this);
  const parts = list.map((u) => ({ u, t: thresholdPlain(u.sequence, L, e, { digits, maxWalk }) }));
  // all n ≥ N are within ε exactly when N is past the last index that is not
  let N = this.from;
  let least = true;
  for (const { u, t } of parts) {
    if (!t.least) least = false;
    // the last bad index in this class is one period before its threshold (none when the threshold is its first index)
    if (t.N > u.sequence.from || !t.least) N = Math.max(N, u.index(t.N - 1) + 1);
  }
  if (period > 1 && least) {
    // within one period above the last bad index every class is already good; N is that index + 1
  }
  const method = parts.map((x) => x.t.method).every((m) => m === parts[0].t.method) ? parts[0].t.method : "mixed";
  const reason = period === 1 ? parts[0].t.detail : parts.map((x) => `along ${x.u.along}: ${x.t.detail}`).join("; ");
  const certificate = Object.freeze({
    kind: "N for ε",
    claim: `|a(${this.variable}) − L| < ε for every ${this.variable} ≥ N`,
    term: format(this.ast),
    variable: this.variable,
    from: this.from,
    params: this.params,
    limit: limitText,
    epsilon: e,
    N,
    least,
    parts: parts.map((x) => ({ along: x.u.along, period: x.u.period, residue: x.u.residue, term: format(x.u.sequence.ast), variable: x.u.sequence.variable, from: x.u.sequence.from, N: x.t.N, method: x.t.method, monotone: x.t.monotone ?? null, bound: x.t.bound ?? null })),
  });
  return { N, least, limit: tidyValue(found), epsilon: e, method, reason, certificate };
};

/**
 * Recheck an "N for ε" certificate without trusting the search that made
 * it: the inequality at N (and its failure at N − 1 when N is claimed
 * least) at a higher precision, the tail argument re-derived (the monotone
 * direction proven afresh, or the dominating bound compared with the terms
 * and with ε), and the inequality itself at a spread of later indices.
 * → { valid, checks: [{ check, ok }] }.
 */
export function verifySequenceCertificate(cert) {
  const checks = [];
  const note = (check, ok) => checks.push({ check, ok: !!ok });
  const seq = new Sequence(cert.term, { variable: cert.variable, from: cert.from, params: cert.params });
  const digits = 40;
  const limAst = soft(() => toAst(cert.limit));
  const found = seq.limit({ digits });
  const L = memoBits((bits) => (limAst && !/^about/.test(cert.limit) ? encloseAst(limAst, {}, bits) : bits <= bitsForDigits(digits) ? Iv.from(found) : Iv.from(seq.limit({ digits: Math.ceil(bits / 3) }))));
  note("the limit agrees with the one found afresh", !lt(L(160).hi, Iv.from(found).lo) && !gt(L(160).lo, Iv.from(found).hi));
  const e = cert.epsilon;
  const ok = (k) => closeAt(seq, k, L, e, digits);
  note(`|a(${cert.N}) − L| < ε`, ok(cert.N));
  if (cert.least && cert.N > cert.from) note(`|a(${cert.N - 1}) − L| ≥ ε, so N is least`, !ok(cert.N - 1));
  // the parts must be the subsequences of this very sequence, one for each residue class
  const classes = soft(() => subsequencesOf(seq));
  const parts = Array.isArray(cert.parts) ? cert.parts : [];
  const bound = classes !== null && parts.length === classes.list.length && classes.list.every((u) => parts.some((p) => p.period === u.period && p.residue === u.residue && p.from === u.sequence.from && p.term === format(u.sequence.ast)));
  note(classes && classes.period > 1 ? `the parts are the ${classes.period} subsequences n = ${classes.period}m + r of the sequence` : "the part is the sequence itself", bound);
  // tailStart: an index from which the tail arguments give the inequality for every class
  let tailStart = cert.N;
  let covered = bound;
  for (const part of parts) {
    const pv = part.variable ?? cert.variable;
    const sub = new Sequence(part.term, { variable: pv, from: part.from, params: cert.params });
    const index = (m) => part.period * m + part.residue;
    let T = null; // in the part's own index: the inequality holds there and the tail argument carries it on
    if (part.method === "constant") T = part.from;
    else if (part.method === "monotone tail" && part.monotone) T = Math.max(part.from, part.N, part.monotone.from);
    else if (part.method === "dominating sequence" && part.bound) T = Math.max(part.from, part.bound.from, part.bound.belowEpsilonFrom);
    if (T === null || !Number.isSafeInteger(T)) covered = false;
    else {
      const okT = soft(() => closeAt(sub, T, L, e, digits), false);
      if (!okT) covered = false;
      tailStart = Math.max(tailStart, index(T));
    }
    if (part.method === "constant") {
      const again = soft(() => sub.monotone({ digits }));
      note(`along ${part.along}: the terms are constant`, again && again.direction === "constant");
    } else if (part.method === "monotone tail") {
      const again = soft(() => sub.monotone({ digits }));
      note(`along ${part.along}: the tail is ${part.monotone.direction} from ${part.monotone.from}`, again && again.direction === part.monotone.direction && again.from <= part.monotone.from);
    } else if (part.method === "dominating sequence") {
      const { C, exponents: E, from: X, belowEpsilonFrom: B } = part.bound;
      const bits = 200;
      const env = paramEnv(cert.params);
      const boundAt = (k) => envAt({ C, e: E }, rayContext(pv, env, new Rational(BigInt(k)), bits));
      note(`along ${part.along}: the dominating sequence decays`, signE(E) < 0 && decreasing(E, rayContext(pv, env, new Rational(BigInt(X)), bits)));
      note(`along ${part.along}: it is below ε at ${B}`, lt(boundAt(B), e));
      let dominated = true;
      for (let k = X, i = 0; i < 40 && k <= 100000; i++, k = Math.ceil(k * 1.5) + 1) {
        const d = soft(() => distanceAt(sub, k, L(bits), bits));
        if (d && gt(d.lo, boundAt(k))) dominated = false;
      }
      note(`along ${part.along}: the terms stay under it at sampled indices`, dominated);
    }
  }
  // from N up to where every tail argument takes over, each index is checked one by one
  const gap = tailStart - cert.N;
  let between = covered && Number.isSafeInteger(gap) && gap <= 200000;
  for (let k = cert.N; between && k < tailStart; k++) if (!soft(() => ok(k), false)) between = false;
  note(gap > 0 ? `|a(n) − L| < ε at each of the ${gap} indices from ${cert.N} to ${tailStart - 1}, before the tail arguments take over at ${tailStart}` : `the tail arguments cover every n ≥ ${cert.N}`, between);
  let later = true;
  let tried = 0;
  for (let k = cert.N, i = 0; i < 60; i++, k = i < 30 ? k + 1 : Math.ceil(k * 1.7) + 1) {
    if (k > Math.max(100000, 2 * cert.N)) break; // far out the terms themselves are too large to write down
    const good = soft(() => ok(k), null);
    if (good === null) break;
    tried++;
    if (!good) later = false;
  }
  note(`the inequality holds at ${tried} later indices`, later && tried > 0);
  return { valid: checks.every((c) => c.ok), checks };
}


// ---- uniform convergence, decided ---------------------------------------------------------------

/** lim of a sequence given by a tree in n: a RationalInterval, ±Infinity, or null when not found. */
function limitOfTree(term, n, digits) {
  const folded = foldPowers(simplify(term), n);
  const lone = constantRational(folded);
  if (lone !== null) return new RationalInterval(lone, lone);
  return soft(() => new Sequence(folded, { variable: n }).limit({ digits }));
}
const isZeroLimit = (L) => L instanceof RationalInterval && L.low.numerator === 0n && L.high.numerator === 0n;
const awayFromZero = (L) => L === Infinity || L === -Infinity || (L instanceof RationalInterval && (gt(L.low, ZERO) || lt(L.high, ZERO)));

/**
 * Decide uniform convergence of g_n = f_n − f to 0 on I = [a, b]; null when
 * neither proof goes through. See src/uniform.js for the two routes.
 */
function decideUniform(fs, diff, I, digits) {
  const [x, n] = [fs.variable, fs.index];
  const [a, b] = [I.lo, I.hi];
  const at = (p) => subst(diff, x, typeof p === "object" && p.type ? p : num(p));
  const showL = (L) => showValue(L);
  // 1. monotone in x for every n ≥ n₀: the sup is at an end
  const dx = soft(() => simplify(derivative(diff, x)));
  if (dx) {
    for (const n0 of [1, 2, 4, 16]) {
      const env = { [x]: [a, b], [n]: [new Rational(BigInt(n0)), UNBOUNDED] };
      const s = weakSign(dx, env);
      if (!s || !definedOn(diff, env)) continue;
      const [La, Lb] = [limitOfTree(at(a), n, digits), limitOfTree(at(b), n, digits)];
      if (La === null || Lb === null) break;
      const sup = `sup |f_n − f| on [${a}, ${b}] is the larger of |f_n − f| at ${x} = ${a} and at ${x} = ${b}, because f_n − f is ${s > 0 ? "increasing" : "decreasing"} in ${x} there for every ${n} ≥ ${n0}`;
      if (isZeroLimit(La) && isZeroLimit(Lb)) return { verdict: "uniform", method: "monotone in x", from: n0, reason: `${sup}; both end values tend to 0` };
      const bad = awayFromZero(La) ? [a, La] : awayFromZero(Lb) ? [b, Lb] : null;
      if (bad) return { verdict: "not uniform", method: "monotone in x", from: n0, witness: { x: `${bad[0]}`, limit: bad[1] }, reason: `${sup}; at ${x} = ${bad[0]} it tends to ${showL(bad[1])}, not 0, so the sup does not tend to 0 (on the interval without that end the sup is the same, by continuity)` };
      break;
    }
  }
  // 2. a bound for every x at once that tends to 0
  const bits = bitsForDigits(digits) + 32;
  const proof = soft(() => onRays(n, { [x]: I }, bits, 0, (ctx, N) => {
    const node = nodeAt(diff, ctx);
    if (signE(node.e) >= 0) return undefined;
    const ub = upperEnv(node, ctx);
    return { N, bound: envAt(ub, ctx) };
  }, [4, 8, 16, 32, 64, 128, 256, 1024, 4096]));
  if (proof) return { verdict: "uniform", method: "uniform bound", from: proof.N, reason: `for every x in the interval at once, |f_n(x) − f(x)| is below a bound that tends to 0 (it is at most ${proof.bound.toNumber().toPrecision(3)} from n = ${proof.N})` };
  // 3. a witness x_n inside the interval along which |f_n − f| does not tend to 0
  const N = variable(n);
  const w = I.width;
  const moving = [];
  for (const c of [ONE, TWO, HALF]) {
    const step = op("/", num(c.multiply(w)), N); // c·(b − a)/n: inside (a, b) for n > c
    moving.push({ tree: op("-", num(b), step), text: `${b} − ${c.multiply(w)}/${n}` });
    moving.push({ tree: op("+", num(a), step), text: a.numerator === 0n ? `${c.multiply(w)}/${n}` : `${a} + ${c.multiply(w)}/${n}` });
  }
  if (le(a, ZERO) && gt(b, ZERO)) for (const c of [ONE, TWO, HALF]) moving.push({ tree: op("/", num(c), N), text: `${c}/${n}` });
  for (const cand of moving) {
    const L = limitOfTree(simplify(at(cand.tree)), n, digits);
    if (L !== null && awayFromZero(L)) return { verdict: "not uniform", method: "witness", witness: { x: cand.text, limit: L }, reason: `at ${x} = ${cand.text}, which lies in the interval for large ${n}, f_n − f tends to ${showL(L)}, not 0; so sup |f_n − f| does not tend to 0` };
  }
  return null;
}
