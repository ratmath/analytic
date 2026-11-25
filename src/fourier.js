// Fourier series with certified coefficients. On [a, b] with L = b − a,
//
//   f(x) ~ a₀/2 + Σ aₙ·cos(2πn·x/L) + bₙ·sin(2πn·x/L),
//   aₙ = (2/L)·∫ f(x)·cos(2πn·x/L) dx,   bₙ likewise with sin,
//
// or the half-range sine or cosine series in πn·(x − a)/L. Each coefficient
// is an integral enclosed by the fixed-point quadrature, piece by piece for
// a piecewise function (a square wave, a sawtooth). Parseval's identity
// then gives a proven mean-square error for every partial sum.
import { Rational, RationalInterval } from "@ratmath/core";
import { Refinement } from "@ratmath/core/refine";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, lt, le, toQ } from "./rat.js";
import { toRational, num, v as variable, op, call, simplify, format } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { fn, AnalyticFunction, evalParams, gaussLegendre } from "./fn.js";
import { PiecewiseFunction } from "./piecewise.js";
import { quad1 } from "./quad.js";

const q = (x) => (typeof x === "string" ? toRational(x) : typeof x === "number" && !Number.isInteger(x) ? toRational(x) : toQ(x));
const PI = { type: "const", name: "pi" };
const tenTo = (d) => new Rational(1n, 10n ** BigInt(d));
const KINDS = new Set(["full", "sine", "cosine"]);

/** The smooth stretches of f on [A, B], each an AnalyticFunction. */
function stretches(f, A, B) {
  if (!(f instanceof PiecewiseFunction)) return [{ lo: A, hi: B, f }];
  return f.segments(A, B).filter((s) => !s.at && lt(s.lo, s.hi)).map((s) => {
    if (!s.f) refuse("undefined", `no piece is defined on (${s.lo}, ${s.hi})`);
    return { lo: s.lo, hi: s.hi, f: s.f };
  });
}
const envOf = (f) => {
  const env = {};
  for (const [k, val] of Object.entries(evalParams(f.params))) env[k] = Iv.from(val);
  return env;
};

/** The angle of the n-th harmonic as a tree in `name`. */
function angle(kind, n, name, A, L) {
  const x = variable(name);
  if (kind === "full") return op("/", op("*", op("*", num(2 * n), PI), x), num(L));
  return op("/", op("*", op("*", num(n), PI), op("-", x, num(A))), num(L));
}

export class FourierSeries {
  #f;
  #energy = null;
  constructor(f, A, B, kind, a, b, digits) {
    this.#f = f;
    this.interval = [A, B];
    /** The length of [a, b]: the period of a full series, half the period of a sine or cosine series. */
    this.length = B.subtract(A);
    this.period = kind === "full" ? this.length : this.length.multiply(TWO);
    this.kind = kind;
    this.variable = f.variable;
    this.digits = digits;
    /** a[0] is a₀ (the mean is a₀/2); a[n] and b[n] are RationalIntervals. b[0] is 0. */
    this.a = a;
    this.b = b;
    this.terms = a.length - 1;
    Object.freeze(this);
  }
  /** { a, b } for the n-th harmonic. */
  coefficient(n) {
    if (!Number.isInteger(n) || n < 0 || n > this.terms) refuse("bad-order", `this series was computed for n up to ${this.terms}`);
    return { a: this.a[n], b: this.b[n] };
  }
  /** √(aₙ² + bₙ²), enclosed. */
  amplitude(n, bits = 96) {
    const { a, b } = this.coefficient(n);
    const s = Iv.from(a).mul(Iv.from(a)).add(Iv.from(b).mul(Iv.from(b)));
    return encloseAst(call("sqrt", variable("u")), { u: new Iv(lt(s.lo, ZERO) ? ZERO : s.lo, s.hi) }, bits).toRationalInterval();
  }
  #count(N) {
    const n = N ?? this.terms;
    if (!Number.isInteger(n) || n < 0 || n > this.terms) refuse("bad-order", `this series was computed for n up to ${this.terms}`);
    return n;
  }
  /** The partial sum with harmonics up to N as a function (coefficients at the midpoints of their enclosures, for plotting). */
  partial(N) {
    const n = this.#count(N);
    const [A] = this.interval;
    const mid = (iv) => {
      const m = iv.low.add(iv.high).divide(TWO);
      // a coefficient that cannot be told apart from 0 is left out
      if (iv.low.numerator <= 0n && iv.high.numerator >= 0n && le(iv.high.subtract(iv.low), tenTo(Math.max(4, this.digits - 2)))) return null;
      return m.denominator <= 1000000n ? m : toRational(m.toNumber().toPrecision(15));
    };
    let ast = null;
    const add = (t) => { ast = ast ? op("+", ast, t) : t; };
    const a0 = mid(this.a[0]);
    if (a0) add(num(a0.divide(TWO)));
    for (let k = 1; k <= n; k++) {
      const th = angle(this.kind, k, this.variable, A, this.length);
      const ak = mid(this.a[k]);
      const bk = mid(this.b[k]);
      if (ak) add(op("*", num(ak), call("cos", th)));
      if (bk) add(op("*", num(bk), call("sin", th)));
    }
    return new AnalyticFunction(simplify(ast ?? num(0)), { variable: this.variable });
  }
  /** The partial sum at a rational point, enclosed with the coefficient enclosures. */
  value(x, N, bits = 96) {
    const n = this.#count(N);
    const [A] = this.interval;
    const env = { [this.variable]: Iv.point(q(x)) };
    let s = Iv.from(this.a[0]).scale(new Rational(1n, 2n));
    for (let k = 1; k <= n; k++) {
      const th = angle(this.kind, k, this.variable, A, this.length);
      s = s.add(Iv.from(this.a[k]).mul(encloseAst(call("cos", th), env, bits))).add(Iv.from(this.b[k]).mul(encloseAst(call("sin", th), env, bits)));
    }
    return s.roundOut(bits).toRationalInterval();
  }
  /** (1/L)·∫ f² over the interval: the mean square of f. */
  meanSquare() {
    if (this.#energy) return this.#energy;
    const [A, B] = this.interval;
    let total = Iv.point(ZERO);
    const parts = stretches(this.#f, A, B);
    for (const s of parts) {
      const part = quad1(op("^", s.f.ast, num(2)), s.f.variable, envOf(s.f), s.lo, s.hi, { tol: tenTo(this.digits).divide(new Rational(BigInt(parts.length))), bits: bitsForDigits(this.digits) + 40 });
      total = total.add(part.iv);
    }
    return (this.#energy = total.scale(this.length.reciprocal()).toRationalInterval());
  }
  /**
   * The mean-square error (1/L)·∫ (f − S_N)² of the partial sum, by
   * Parseval: mean square of f minus a₀²/4 + ½·Σ (aₙ² + bₙ²).
   */
  meanSquareError(N) {
    const n = this.#count(N);
    const sq = (iv) => { const x = Iv.from(iv); return x.mul(x); };
    let used = sq(this.a[0]).scale(new Rational(1n, 4n));
    for (let k = 1; k <= n; k++) used = used.add(sq(this.a[k]).add(sq(this.b[k])).scale(new Rational(1n, 2n)));
    const rest = Iv.from(this.meanSquare()).sub(used);
    return new Iv(lt(rest.lo, ZERO) ? ZERO : rest.lo, lt(rest.hi, ZERO) ? ZERO : rest.hi).toRationalInterval();
  }
  /** The partial sum written with decimal coefficients, such as "0.6366*sin(pi*x) - 0.3183*sin(2*pi*x)". */
  toString(N, places = 6) {
    const n = this.#count(N);
    const [A] = this.interval;
    const x = A.numerator === 0n || this.kind === "full" ? this.variable : `(${this.variable} - ${A})`;
    const w = (k) => {
      const c = (this.kind === "full" ? new Rational(BigInt(2 * k)) : new Rational(BigInt(k))).divide(this.length);
      const head = c.equals(ONE) ? "" : c.denominator === 1n ? `${c.numerator}*` : `${c.numerator === 1n ? "" : `${c.numerator}*`}`;
      return `${head}pi*${x}${c.denominator === 1n ? "" : `/${c.denominator}`}`;
    };
    const parts = [];
    const put = (iv, text) => {
      const m = iv.low.add(iv.high).divide(TWO).toNumber();
      if (Math.abs(m) < 0.5 * 10 ** -places) return;
      const size = Number(Math.abs(m).toFixed(places));
      parts.push(`${m < 0 ? (parts.length ? " - " : "-") : parts.length ? " + " : ""}${size}${text}`);
    };
    put(new RationalInterval(this.a[0].low.divide(TWO), this.a[0].high.divide(TWO)), "");
    for (let k = 1; k <= n; k++) {
      put(this.a[k], `*cos(${w(k)})`);
      put(this.b[k], `*sin(${w(k)})`);
    }
    return parts.join("") || "0";
  }
}

/**
 * fourier(f, [a, b], { terms, digits, kind, params }) → Refinement. `f` is
 * an expression, an AnalyticFunction or a piecewise function; `kind` is
 * "full" (default), "sine" or "cosine". The preview holds Float64
 * coefficients { a, b }; the exact stage is a FourierSeries.
 */
export function fourier(f, interval, opts = {}) {
  const g = fn(f, opts.params || opts.variable ? { params: opts.params ?? {}, variable: opts.variable ?? "x" } : undefined);
  const A = q(interval[0]);
  const B = q(interval[1]);
  if (!lt(A, B)) refuse("bad-interval", "fourier needs an interval [a, b] with a < b");
  const kind = opts.kind ?? "full";
  if (!KINDS.has(kind)) refuse("bad-kind", "kind is \"full\", \"sine\" or \"cosine\"");
  const N = opts.terms ?? 10;
  if (!Number.isInteger(N) || N < 0 || N > 500) refuse("bad-order", "terms is a whole number up to 500");
  const digits = opts.digits ?? 10;
  const L = B.subtract(A);
  const scale = TWO.divide(L);
  const wantA = kind !== "sine";
  const wantB = kind !== "cosine";
  return new Refinement(
    () => {
      const Lf = L.toNumber();
      const Af = A.toNumber();
      const parts = stretches(g, A, B);
      const coefficient = (n, trig) => {
        const w = kind === "full" ? (2 * Math.PI * n) / Lf : (Math.PI * n) / Lf;
        const shift = kind === "full" ? 0 : Af;
        let s = 0;
        for (const p of parts) s += gaussLegendre((x) => p.f.float(x) * trig(w * (x - shift)), p.lo.toNumber(), p.hi.toNumber(), 16 + 2 * n);
        return (2 / Lf) * s;
      };
      const a = [];
      const b = [];
      for (let n = 0; n <= N; n++) {
        a.push(wantA ? coefficient(n, Math.cos) : 0);
        b.push(wantB && n > 0 ? coefficient(n, Math.sin) : 0);
      }
      return { value: { a, b }, trust: [...a, ...b].every(Number.isFinite) ? "good" : "unsure" };
    },
    function* () {
      const bits = bitsForDigits(digits) + 40;
      const parts = stretches(g, A, B);
      const tol = tenTo(digits).divide(new Rational(BigInt(2 * parts.length)));
      const zero = new RationalInterval(ZERO, ZERO);
      let pieces = 0;
      const coefficient = (n, name) => {
        let s = Iv.point(ZERO);
        for (const p of parts) {
          const ast = n === 0 ? p.f.ast : op("*", p.f.ast, call(name, angle(kind, n, p.f.variable, A, L)));
          const r = quad1(ast, p.f.variable, envOf(p.f), p.lo, p.hi, { tol, bits });
          pieces += r.pieces;
          s = s.add(r.iv);
        }
        return s.scale(scale).roundOut(bits).toRationalInterval();
      };
      const a = [];
      const b = [];
      for (let n = 0; n <= N; n++) {
        a.push(wantA ? coefficient(n, "cos") : zero);
        b.push(wantB && n > 0 ? coefficient(n, "sin") : zero);
        yield { done: n + 1, of: N + 1, step: `harmonic ${n}` };
      }
      return { value: new FourierSeries(g, A, B, kind, a, b, digits), via: `${(wantA ? N + 1 : 0) + (wantB ? N : 0)} coefficient integrals by Taylor series on ${pieces} pieces` };
    },
  );
}
