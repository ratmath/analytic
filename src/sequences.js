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
import { rayContext, nodeAt, tailOf, signE, spread, upperEnv, envAt, decreasing, tailUpper } from "./asymptotic.js";
import { quad1 } from "./quad.js";
import { AnalyticFunction, evalParams } from "./fn.js";
import { zeros } from "./roots.js";

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
        const s = onRays(this.variable, this.#env, bits, 0, (ctx) => signOnRay(d.rest, ctx) || undefined);
        if (s) return s > 0 ? Infinity : -Infinity;
      }
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
    const found = onRays(n, env, bits, this.from, (ctx, N) => {
      const s = signOnRay(da, ctx);
      return s ? { s, N } : undefined;
    }, [4, 8, ...NS]);
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
    return { direction: found.s > 0 ? "increasing" : "decreasing", from: N, proven: `for every n ≥ ${N}` };
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
    const table = ns.map((n) => ({ n, sup: this.supDistance(n, interval, limit, { digits }) }));
    const bits = bitsForDigits(digits) + 32;
    const diff = simplify(op("-", this.ast, toAst(limit)));
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
