// Functions given as expressions, with fast previews that sharpen into
// certified enclosures. Every question (value, range, integral) returns a
// Refinement: `quick` is a Float64 answer computed at once, and the exact
// stage is a certified RationalInterval at the requested precision.
import { Rational } from "@ratmath/core";
import { Refinement } from "./refine.js";
import { Iv } from "./interval.js";
import { TaylorModel, Domain, DEFAULTS } from "./model.js";
import { AnalyticError, refuse } from "./errors.js";
import { ONE, TWO, ZERO, toQ, lt, le, max, min, isZero, log2Approx } from "./rat.js";
import { toAst, format, compileFloat, floatEnv, modelOf, derivative, simplify, freeVariables, toRational } from "./expr.js";
import { bitsForDigits } from "./scope.js";
import { PiecewiseFunction, parsePiecewiseText } from "./piecewise.js";
import { cancelHoles } from "./holes.js";
import { encloseAst } from "./ieval.js";
import { boxBounder } from "./roots.js";

const q = (v) => (typeof v === "string" ? toRational(v) : typeof v === "number" && !Number.isInteger(v) ? toRational(v) : toQ(v));
const tenTo = (d) => new Rational(1n, 10n ** BigInt(d));

/** Target width for `digits` significant digits of a value of size `iv`. */
function targetWidth(iv, digits) {
  const scale = max(ONE, iv.mag);
  return scale.multiply(tenTo(digits));
}

/**
 * Target for a single value: `digits` significant digits. An enclosure that
 * still contains 0 has no significant digit yet, so it is never narrow enough
 * (the caller stops at its bit budget; a value that is exactly 0 ends there).
 */
function valueNarrow(iv, digits) {
  if (iv.isPoint) return true;
  if (iv.containsZero()) return false;
  return le(iv.width, iv.mig.multiply(tenTo(digits)));
}

export function evalParams(p) {
  const out = {};
  for (const [k, val] of Object.entries(p)) out[k] = typeof val === "string" || typeof val === "number" ? q(val) : val;
  return out;
}

export class AnalyticFunction {
  #float;
  #regular;
  constructor(expression, { variable = "x", params: p = {} } = {}) {
    this.ast = toAst(expression);
    this.variable = variable;
    this.params = Object.freeze({ ...p });
    const free = freeVariables(this.ast);
    for (const name of free) {
      if (name !== variable && !(name in p)) refuse("unbound", `${name} has no value: pass it in params, or set variable`);
    }
    Object.freeze(this);
  }

  /** Calculator notation for the function's formula. */
  toString() {
    return format(this.ast);
  }

  /** Same formula with other parameter values (for sliders). */
  with(p) {
    return new AnalyticFunction(this.ast, { variable: this.variable, params: { ...this.params, ...p } });
  }

  /** Symbolic derivative d/d(variable), as a new AnalyticFunction. */
  derivative() {
    return new AnalyticFunction(simplify(derivative(this.ast, this.variable)), { variable: this.variable, params: this.params });
  }

  /**
   * The same function with removable singularities of its rational summands
   * cancelled: (x^2 - 1)/(x - 1) + sin(x) becomes x + 1 + sin(x). Equal to f
   * wherever f is defined; used for integrals and ranges, which do not see
   * single points.
   */
  regular() {
    if (this.#regular === undefined) {
      const p = evalParams(this.params);
      const exact = Object.values(p).every((v) => v instanceof Rational);
      const c = exact ? cancelHoles(this.ast, this.variable, p) : null;
      this.#regular = c ? new AnalyticFunction(c.ast, { variable: this.variable, params: this.params }) : this;
    }
    return this.#regular;
  }

  /** Float value at a JS number (fast; no guarantee). */
  float(x) {
    const f = (this.#float ??= compileFloat(this.ast));
    const env = floatEnv(this.params);
    env[this.variable] = x;
    return f(env);
  }

  /** Certified Taylor model on a domain. */
  model(domain, opts = {}) {
    const D = Domain(domain, opts.centre !== undefined ? { centre: q(opts.centre) } : undefined);
    const x = TaylorModel.x(D, { order: opts.order ?? DEFAULTS.order, bits: opts.bits ?? DEFAULTS.bits });
    return modelOf(this.ast, { ...evalParams(this.params), [this.variable]: x }, x);
  }

  /**
   * f(x) at a rational point: float preview, then certified to `digits`
   * significant digits (default 20). Exact rationals for rational-only
   * formulas come out as point intervals.
   */
  value(x, opts = {}) {
    const digits = opts.digits ?? 20;
    const X = Iv.from(typeof x === "number" || typeof x === "string" ? q(x) : x);
    return new Refinement(
      () => {
        const value = this.float(X.mid.toNumber());
        return { value, trust: Number.isFinite(value) ? "good" : "unsure" };
      },
      () => valueStages(this, X, digits, opts.maxBits ?? 8192),
    );
  }

  /**
   * Taylor coefficients a_0 … a_n of f about the rational point c, each a
   * certified interval: a_k = f^(k)(c)/k!. Exact points for rational-only
   * formulas. The derivatives are symbolic, so n is limited to 16.
   */
  taylor(c, n = 6, opts = {}) {
    if (!Number.isInteger(n) || n < 0 || n > 16) refuse("bad-order", "taylor needs an order between 0 and 16");
    const at = q(c);
    const bits = bitsForDigits(opts.digits ?? 20) + 16;
    const out = [];
    let g = this;
    let fact = 1n;
    for (let k = 0; k <= n; k++) {
      if (k > 0) {
        g = g.derivative();
        fact *= BigInt(k);
      }
      let v = pointValue(g, at, bits);
      if (!v) {
        try {
          v = Iv.from(g.limit(at, opts));
        } catch (e) {
          if (!(e instanceof AnalyticError)) throw e;
          refuse(e.code, `taylor: the derivative of order ${k} cannot be evaluated at ${at} (${e.message})`);
        }
      }
      out.push(v.scale(new Rational(1n, fact)).toRationalInterval());
    }
    return out;
  }

  /**
   * The limit of f at the rational point c, as a certified interval: the
   * value where f is defined (every function here is continuous on its
   * domain), and at a removable point of a quotient (sin(x)/x at 0) the
   * L'Hôpital enclosure. Refuses at poles and outside the domain.
   */
  limit(c, opts = {}) {
    const at = q(c);
    const bits = bitsForDigits(opts.digits ?? 20) + 16;
    const direct = pointValue(this, at, bits);
    if (direct) return direct.toRationalInterval();
    return boxBounder(this, at.subtract(ONE), at.add(ONE), bits)(Iv.point(at)).toRationalInterval();
  }

  /** Range over an interval: sampled preview, then a certified enclosure. */
  range(interval, opts = {}) {
    const I = Iv.from(interval);
    return new Refinement(
      () => {
        const n = opts.samples ?? 256;
        let lo = Infinity;
        let hi = -Infinity;
        const a = I.lo.toNumber();
        const b = I.hi.toNumber();
        for (let i = 0; i <= n; i++) {
          const y = this.float(a + ((b - a) * i) / n);
          if (y < lo) lo = y;
          if (y > hi) hi = y;
          if (Number.isNaN(y)) return { value: [NaN, NaN], trust: "unsure" };
        }
        // sampling can miss a peak between samples
        return { value: [lo, hi], trust: "rough" };
      },
      () => rangeStages(this.regular(), I, opts),
    );
  }

  /** ∫_a^b f: Gauss–Legendre preview, then a certified enclosure. */
  integral(a, b, opts = {}) {
    const A = q(a);
    const B = q(b);
    return new Refinement(
      () => {
        const value = gaussLegendre((t) => this.float(t), A.toNumber(), B.toNumber(), 16);
        return { value, trust: Number.isFinite(value) ? "good" : "unsure" };
      },
      () => integralStages(this.regular(), A, B, opts),
    );
  }
}

/** fn("exp(sin(x))*x", { variable, params }) */
export function fn(expression, opts) {
  if (expression instanceof AnalyticFunction || expression instanceof PiecewiseFunction) return expression;
  if (typeof expression === "string" || Array.isArray(expression)) {
    const pieces = Array.isArray(expression) ? expression : parsePiecewiseText(expression);
    if (pieces) return new PiecewiseFunction(pieces, opts);
  }
  return new AnalyticFunction(expression, opts);
}

// ---- certified stages --------------------------------------------------------

function* valueStages(f, X, digits, maxBits) {
  let bits = Math.max(64, bitsForDigits(digits) + 16);
  // a point very close to 0 (10^-300) needs its own leading digits kept, or it rounds to an interval around 0
  if (X.isPoint && !isZero(X.lo) && lt(X.lo.abs(), ONE)) bits = Math.min(maxBits, bits + Math.max(0, -log2Approx(X.lo.abs())));
  const zeroBits = Math.min(maxBits, 16 * bits);
  const D = Domain(X);
  for (let attempt = 1; ; attempt++) {
    let r;
    try {
      // a point needs no Taylor model: interval evaluation is exact about ends of domains (sqrt(0), asin(1))
      r = X.isPoint ? pointValue(f, X.lo, bits) : null;
      r ??= Iv.from(f.model(D, { order: X.isPoint ? 0 : 8, bits }).range());
    } catch (e) {
      // an argument that only seems to leave a domain because of coarse rounding: sharpen and retry
      if (!(e instanceof AnalyticError) || !X.isPoint || bits >= Math.min(maxBits, 1024)) throw e;
      bits *= 2;
      continue;
    }
    const narrow = valueNarrow(r, digits);
    // a value that may be 0 is accepted once it is absolutely tiny at a generous precision
    const zeroish = !narrow && r.containsZero() && bits >= zeroBits && le(r.width, targetWidth(r, digits));
    if (narrow || zeroish || bits >= maxBits) {
      const note = narrow ? "" : zeroish ? " (cannot be told apart from 0; digits are absolute)" : ` (budget hit: ${maxBits} bits)`;
      return { value: r.toRationalInterval(), via: `${r.isPoint ? "exact rational arithmetic" : `certified enclosure at ${bits} bits`}${note}` };
    }
    yield { done: attempt, of: attempt + 1, step: `bits ${bits}`, partial: r.toRationalInterval() };
    bits *= 2;
  }
}

/** f at a rational point by interval evaluation, or null where that cannot be done (a removable point). */
function pointValue(f, x, bits) {
  const env = {};
  for (const [k, val] of Object.entries(evalParams(f.params))) env[k] = Iv.from(val);
  env[f.variable] = Iv.point(x);
  try {
    return encloseAst(f.ast, env, bits + 8);
  } catch (e) {
    if (!(e instanceof AnalyticError)) throw e;
    return null;
  }
}

/**
 * Adaptive bisection: keep a list of pieces with model ranges; inner bounds
 * come from certified values at piece midpoints. Split the pieces that hold
 * the outer extremes until the outer and inner bounds agree to `digits`.
 */
function* rangeStages(f, I, opts) {
  const digits = opts.digits ?? 6;
  const order = opts.order ?? 8;
  const bits = opts.bits ?? Math.max(64, bitsForDigits(digits) + 24);
  const maxPieces = opts.maxPieces ?? 256;
  let bounder = null;
  let rough = 0;
  const piece = (lo, hi) => {
    try {
      const m = f.model(Domain(new Iv(lo, hi)), { order, bits });
      const outer = m.bound(4);
      const c = Iv.from(m.at(m.domain.centre));
      return { lo, hi, outer, c };
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      // no Taylor model here (abs across 0, sqrt from 0, a model too wide): bound by intervals and let bisection close in
      bounder ??= boxBounder(f, I.lo, I.hi, bits);
      const outer = bounder(new Iv(lo, hi));
      let c;
      try {
        c = bounder(Iv.point(lo.add(hi).divide(TWO)));
      } catch (e2) {
        if (!(e2 instanceof AnalyticError)) throw e2;
        c = new Iv(outer.hi, outer.lo); // no inner information from this piece
      }
      rough++;
      return { lo, hi, outer, c, rough: true };
    }
  };
  let pieces = [piece(I.lo, I.hi)];
  for (let round = 1; ; round++) {
    let U = pieces[0], L = pieces[0], innerHi = pieces[0].c.lo, innerLo = pieces[0].c.hi;
    for (const p of pieces) {
      if (lt(U.outer.hi, p.outer.hi)) U = p;
      if (lt(p.outer.lo, L.outer.lo)) L = p;
      innerHi = max(innerHi, p.c.lo);
      innerLo = min(innerLo, p.c.hi);
    }
    const outer = new Iv(L.outer.lo, U.outer.hi);
    const tol = targetWidth(outer, digits);
    const gapHi = U.outer.hi.subtract(innerHi);
    const gapLo = innerLo.subtract(L.outer.lo);
    const done = le(gapHi, tol) && le(gapLo, tol);
    if (done || pieces.length >= maxPieces) {
      const note = done ? "" : `, budget hit at ${maxPieces} pieces`;
      const how = pieces.some((p) => p.rough) ? ", interval bounds where the function is not smooth" : "";
      return { value: outer.toRationalInterval(), via: `Taylor models (order ${order}) on ${pieces.length} piece${pieces.length > 1 ? "s" : ""}${how}${note}` };
    }
    yield { done: pieces.length, of: maxPieces, step: `pieces ${pieces.length}`, partial: outer.toRationalInterval() };
    const split = new Set();
    if (lt(tol, gapHi)) split.add(U);
    if (lt(tol, gapLo)) split.add(L);
    const next = [];
    for (const p of pieces) {
      if (!split.has(p)) next.push(p);
      else {
        const m = p.lo.add(p.hi).divide(TWO);
        next.push(piece(p.lo, m), piece(m, p.hi));
      }
    }
    pieces = next;
  }
}

function* integralStages(f, A, B, opts) {
  const digits = opts.digits ?? 12;
  const order = opts.order ?? 12;
  const bits = opts.bits ?? Math.max(64, bitsForDigits(digits) + 24);
  const maxPieces = opts.maxPieces ?? 256;
  if (A.compareTo(B) === 0) return { value: Iv.point(ZERO).toRationalInterval(), via: "empty interval" };
  const [lo, hi, sgn] = lt(A, B) ? [A, B, ONE] : [B, A, ONE.negate()];
  // Each piece is refined on its own until its share of the width budget is met.
  let pieces = [{ lo, hi }];
  let bounder = null;
  let rough = false;
  const enclose = (p) => {
    if (p.iv) return p.iv;
    try {
      p.iv = Iv.from(f.model(Domain(new Iv(p.lo, p.hi)), { order, bits }).integral());
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      // no Taylor model on this piece: (width)·(range) still encloses its integral, and bisection shrinks the piece
      bounder ??= boxBounder(f, lo, hi, bits);
      p.iv = bounder(new Iv(p.lo, p.hi)).scale(p.hi.subtract(p.lo));
      rough = true;
    }
    return p.iv;
  };
  for (let round = 1; ; round++) {
    let total = Iv.point(ZERO);
    for (const p of pieces) total = total.add(enclose(p));
    const tol = targetWidth(total, digits);
    if (le(total.width, tol) || pieces.length >= maxPieces) {
      const note = le(total.width, tol) ? "" : `, budget hit at ${maxPieces} pieces`;
      const how = rough ? ", interval bounds where the function is not smooth" : "";
      return { value: total.scale(sgn).toRationalInterval(), via: `Taylor models (order ${order}) on ${pieces.length} piece${pieces.length > 1 ? "s" : ""}${how}${note}` };
    }
    yield { done: pieces.length, of: maxPieces, step: `pieces ${pieces.length}`, partial: total.scale(sgn).toRationalInterval() };
    const len = hi.subtract(lo);
    const next = [];
    let count = pieces.length;
    for (const p of pieces) {
      const share = tol.multiply(p.hi.subtract(p.lo)).divide(len);
      if (le(p.iv.width, share) || count >= maxPieces) next.push(p);
      else {
        count++;
        const m = p.lo.add(p.hi).divide(TWO);
        next.push({ lo: p.lo, hi: m }, { lo: m, hi: p.hi });
      }
    }
    pieces = next;
  }
}

// ---- float helpers -----------------------------------------------------------

const GL = (() => {
  // 8-point Gauss–Legendre nodes/weights on [-1, 1]
  const x = [0.1834346424956498, 0.525532409916329, 0.7966664774136267, 0.9602898564975363];
  const w = [0.362683783378362, 0.3137066458778873, 0.2223810344533745, 0.1012285362903763];
  return { x, w };
})();

export function gaussLegendre(g, a, b, panels = 8) {
  const h = (b - a) / panels;
  let s = 0;
  for (let k = 0; k < panels; k++) {
    const m = a + (k + 0.5) * h;
    for (let i = 0; i < 4; i++) {
      const dx = (GL.x[i] * h) / 2;
      s += GL.w[i] * (g(m - dx) + g(m + dx));
    }
  }
  return (s * h) / 2;
}

export { AnalyticError };
