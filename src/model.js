// Taylor models: f(x) − P(x − c) ∈ I for every x in the domain D, where P has
// exact Rational coefficients and I is a Rational interval.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv, IV_ZERO } from "./interval.js";
import * as poly from "./poly.js";
import { ZERO, ONE, toQ, lt, le, gt, eq, isZero, max, roundDyadic, bitLen, log2Approx, describeValue } from "./rat.js";
import { refuse, AnalyticError } from "./errors.js";
import { reciprocal } from "./elementary.js";

export const DEFAULTS = { order: 12, bits: 96 };

// ------------------------------------------------------------------ Domain

export class DomainClass {
  constructor(lo, hi, centre) {
    if (gt(lo, hi)) [lo, hi] = [hi, lo];
    if (centre === undefined) centre = lo.add(hi).divide(new Rational(2n));
    if (lt(centre, lo) || gt(centre, hi)) {
      refuse("centre-outside", `centre ${centre} is not inside the domain [${lo}, ${hi}]`);
    }
    this.lo = lo;
    this.hi = hi;
    this.centre = centre;
    this.t = new Iv(lo.subtract(centre), hi.subtract(centre));
    Object.freeze(this);
  }
  get interval() {
    return new RationalInterval(this.lo, this.hi);
  }
  get width() {
    return this.hi.subtract(this.lo);
  }
  /** max |x − c| over the domain */
  get radius() {
    return this.t.mag;
  }
  contains(x) {
    const v = Iv.from(x);
    return le(this.lo, v.lo) && le(v.hi, this.hi);
  }
  equals(o) {
    return o instanceof DomainClass && eq(this.lo, o.lo) && eq(this.hi, o.hi) && eq(this.centre, o.centre);
  }
  toString() {
    return `[${this.lo}, ${this.hi}] about ${this.centre}`;
  }
  toJSON() {
    return { lo: this.lo.toString(), hi: this.hi.toString(), centre: this.centre.toString() };
  }
}

/**
 * Domain(R`0:1/2`), Domain([a, b]), Domain(a, b), each with optional
 * { centre } as the last argument. A point gives a degenerate domain.
 */
export function Domain(a, b, opts) {
  const isOpts = (v) => v && typeof v === "object" && !Array.isArray(v) && ("centre" in v || "center" in v);
  if (a instanceof DomainClass) {
    const c = (isOpts(b) ? b : opts)?.centre ?? (isOpts(b) ? b : opts)?.center;
    return c === undefined ? a : new DomainClass(a.lo, a.hi, toQ(c));
  }
  let iv;
  if (b === undefined || isOpts(b)) {
    opts = b;
    iv = Iv.from(a);
  } else {
    iv = new Iv(toQ(a), toQ(b));
  }
  const c = opts?.centre ?? opts?.center;
  return new DomainClass(iv.lo, iv.hi, c === undefined ? undefined : toQ(c));
}
Domain.prototype = DomainClass.prototype;

// ------------------------------------------------------------------ Model

export class TaylorModel {
  constructor({ domain, coeffs, rem = IV_ZERO, order = DEFAULTS.order, bits = DEFAULTS.bits, notes = [], assumed = false }) {
    this.domain = domain;
    this.order = order;
    this.bits = bits;
    this.notes = [...new Set(notes)];
    this.assumed = assumed;
    let c = poly.trim(coeffs.length ? coeffs : [ZERO]);
    let r = rem;
    if (c.length - 1 > order) {
      const high = c.map((v, i) => (i > order ? v : ZERO));
      r = r.add(Iv.sym(poly.magBound(high, domain.t.mag)));
      c = poly.trim(c.slice(0, order + 1));
    }
    // Sweep: replace coefficients with huge denominators by nearby dyadics and
    // move the difference into the remainder.
    const limit = 2 * bits + 64;
    const tm = domain.t.mag;
    let tk = ONE;
    for (let j = 0; j < c.length; j++) {
      if (bitLen(c[j].denominator) > limit) {
        const e = log2Approx(c[j].abs());
        const d = roundDyadic(c[j], Math.max(bits + 16 - (Number.isFinite(e) ? e : 0), 8));
        const diff = c[j].subtract(d).abs().multiply(tk);
        r = r.add(Iv.sym(diff));
        c[j] = d;
      }
      tk = tk.multiply(tm);
    }
    this.coeffs = c;
    this.rem = r.roundOut(bits + 8);
    Object.freeze(this);
  }

  // -------- construction

  static x(domain, opts = {}) {
    const D = Domain(domain);
    return new TaylorModel({ domain: D, coeffs: [D.centre, ONE], ...settings(opts), notes: ["x"] });
  }

  static constant(domain, value, opts = {}) {
    const D = Domain(domain);
    const iv = Iv.from(value);
    if (iv.isPoint) return new TaylorModel({ domain: D, coeffs: [iv.lo], ...settings(opts), notes: ["constant"] });
    const m = iv.mid;
    return new TaylorModel({ domain: D, coeffs: [m], rem: iv.sub(m), ...settings(opts), notes: ["constant interval"] });
  }

  /** Polynomial given by coefficients in powers of x (not x − c). */
  static polynomial(domain, coefficients, opts = {}) {
    const D = Domain(domain);
    const p = coefficients.map(toQ);
    return new TaylorModel({ domain: D, coeffs: poly.shift(p, D.centre), ...settings(opts), notes: ["polynomial"] });
  }

  // -------- accessors

  get centre() {
    return this.domain.centre;
  }
  /** Exact coefficients of P in powers of (x − centre). */
  get coefficients() {
    return this.coeffs.slice();
  }
  /** Coefficients of P in powers of x. */
  get coefficientsInX() {
    return poly.shift(this.coeffs, this.domain.centre.negate());
  }
  get remainder() {
    return this.rem.toRationalInterval();
  }
  get isExact() {
    return this.rem.isPoint && isZero(this.rem.lo) && !this.assumed;
  }
  get degree() {
    return this.coeffs.length - 1;
  }

  /** Enclosure of the polynomial part over the domain (internal Iv). */
  polyBound(depth = 0) {
    return poly.range(this.coeffs, this.domain.t.lo, this.domain.t.hi, { depth });
  }
  /** Enclosure of the function over the domain (internal Iv). */
  bound(depth = 0) {
    return this.polyBound(depth).add(this.rem);
  }

  // -------- evaluation

  /** Certified enclosure of f(x) for a point or sub-interval x of the domain. */
  at(x, { depth = 6 } = {}) {
    const v = Iv.from(x);
    if (!this.domain.contains(v)) {
      refuse("outside-domain", `${v.isPoint ? v.lo : v} is outside the model's domain ${this.domain}`);
    }
    const t = v.sub(this.domain.centre);
    const p = t.isPoint ? Iv.point(poly.evaluate(this.coeffs, t.lo)) : poly.rangeOn(this.coeffs, t, { depth });
    return p.add(this.rem).toRationalInterval();
  }

  /** Certified enclosure of the range of f over the domain. */
  range({ depth = 6 } = {}) {
    return this.bound(depth).toRationalInterval();
  }

  // -------- arithmetic

  #other(o, op) {
    if (o instanceof TaylorModel) {
      if (!o.domain.equals(this.domain)) {
        refuse("domain-mismatch", `cannot ${op} models on different domains (${this.domain} and ${o.domain})`);
      }
      return o;
    }
    try {
      return TaylorModel.constant(this.domain, o, { order: this.order, bits: this.bits });
    } catch (e) {
      if (e instanceof AnalyticError) refuse("bad-operand", `cannot ${op} a Taylor model and ${describeValue(o)}`);
      throw e;
    }
  }

  #make(coeffs, rem, o, extraNotes = []) {
    return new TaylorModel({
      domain: this.domain,
      coeffs,
      rem,
      order: o ? Math.min(this.order, o.order) : this.order,
      bits: o ? Math.max(this.bits, o.bits) : this.bits,
      notes: [...this.notes, ...(o ? o.notes : []), ...extraNotes],
      assumed: this.assumed || (o ? o.assumed : false),
    });
  }

  add(o) {
    o = this.#other(o, "add");
    return this.#make(poly.add(this.coeffs, o.coeffs), this.rem.add(o.rem), o);
  }
  subtract(o) {
    o = this.#other(o, "subtract");
    return this.#make(poly.sub(this.coeffs, o.coeffs), this.rem.sub(o.rem), o);
  }
  negate() {
    return this.#make(this.coeffs.map((c) => c.negate()), this.rem.neg());
  }
  multiply(o) {
    if (!(o instanceof TaylorModel)) {
      const iv = Iv.from(o);
      if (iv.isPoint) {
        return this.#make(poly.scale(this.coeffs, iv.lo), this.rem.scale(iv.lo));
      }
    }
    o = this.#other(o, "multiply");
    const order = Math.min(this.order, o.order);
    const { low, high } = poly.mulSplit(this.coeffs, o.coeffs, order);
    const t = this.domain.t;
    let rem = high.length ? Iv.sym(poly.magBound(high, t.mag)) : IV_ZERO;
    const bp = Iv.sym(poly.magBound(this.coeffs, t.mag));
    const bq = Iv.sym(poly.magBound(o.coeffs, t.mag));
    rem = rem.add(bp.mul(o.rem)).add(bq.mul(this.rem)).add(this.rem.mul(o.rem));
    return this.#make(low, rem, o);
  }
  divide(o) {
    if (!(o instanceof TaylorModel)) {
      const iv = Iv.from(o);
      if (iv.isPoint) {
        if (isZero(iv.lo)) refuse("division-by-zero", "division by zero");
        return this.multiply(iv.lo.reciprocal());
      }
    }
    o = this.#other(o, "divide");
    return this.multiply(reciprocal(o));
  }
  /** Integer power by repeated squaring (negative powers use the reciprocal). */
  pow(n) {
    n = Number(typeof n === "object" ? toQ(n).toString() : n);
    if (!Number.isInteger(n)) refuse("bad-exponent", `pow needs an integer exponent; use exp(a·log(f)) for ${n}`);
    if (n < 0) return reciprocal(this).pow(-n);
    let result = TaylorModel.constant(this.domain, ONE, { order: this.order, bits: this.bits });
    let base = this;
    while (n > 0) {
      if (n & 1) result = result.multiply(base);
      n >>= 1;
      if (n) base = base.multiply(base);
    }
    return result;
  }

  // -------- calculus

  /** Antiderivative F with F(centre) = 0 (∫ from the centre to x). */
  integrate() {
    const P = poly.antiderivative(this.coeffs);
    const rem = this.rem.mul(this.domain.t); // ∫_c^x r(s) ds = (x−c)·ρ, ρ ∈ I
    return new TaylorModel({
      domain: this.domain, coeffs: P, rem, order: this.order, bits: this.bits,
      notes: [...this.notes, "integrate"], assumed: this.assumed,
    });
  }

  /** Certified enclosure of ∫_a^b f (defaults to the whole domain). */
  integral(a = this.domain.lo, b = this.domain.hi) {
    a = toQ(a);
    b = toQ(b);
    for (const v of [a, b]) {
      if (!this.domain.contains(v)) refuse("outside-domain", `integration limit ${v} is outside ${this.domain}`);
    }
    const P = poly.antiderivative(this.coeffs);
    const c = this.domain.centre;
    const exact = poly.evaluate(P, b.subtract(c)).subtract(poly.evaluate(P, a.subtract(c)));
    return Iv.point(exact).add(this.rem.scale(b.subtract(a))).toRationalInterval();
  }

  /**
   * Derivative. Exact for models with zero remainder (polynomials). A nonzero
   * remainder says nothing about the derivative, so this refuses: rebuild the
   * model from the derivative's formula instead.
   */
  derivative() {
    if (!(this.rem.isPoint && isZero(this.rem.lo))) {
      refuse(
        "derivative-of-model",
        "the remainder of a Taylor model does not bound the derivative's error; build a model of f' from its formula instead",
      );
    }
    return new TaylorModel({
      domain: this.domain, coeffs: poly.derivative(this.coeffs), order: this.order, bits: this.bits,
      notes: [...this.notes, "derivative"], assumed: this.assumed,
    });
  }

  // -------- display

  describe() {
    const lines = [
      `Taylor model on ${this.domain}`,
      `  order ${this.order}, degree ${this.degree}, ${this.bits} bits`,
      `  remainder ${fmtIv(this.rem)} (width ${fmtQ(this.rem.width)})`,
      `  built from: ${this.notes.join(", ") || "—"}`,
    ];
    if (this.assumed) lines.push("  note: uses an assumed bound supplied by the caller (not proven by the library)");
    return lines.join("\n");
  }

  toString() {
    const c = this.domain.centre;
    const v = isZero(c) ? "x" : `(x - ${c})`;
    const terms = this.coeffs
      .map((a, j) => (isZero(a) ? null : j === 0 ? fmtQ(a) : `${fmtQ(a)}·${v}${j > 1 ? "^" + j : ""}`))
      .filter(Boolean);
    return `${terms.join(" + ") || "0"} + ${fmtIv(this.rem)}`;
  }

  toJSON() {
    return {
      type: "TaylorModel",
      domain: this.domain.toJSON(),
      order: this.order,
      coefficients: this.coeffs.map(String),
      remainder: [this.rem.lo.toString(), this.rem.hi.toString()],
      notes: this.notes,
      assumed: this.assumed,
    };
  }
}

export const TM = TaylorModel;

export function settings(opts = {}) {
  return { order: opts.order ?? DEFAULTS.order, bits: opts.bits ?? DEFAULTS.bits };
}

function fmtQ(q, digits = 8) {
  if (q.denominator === 1n || q.toString().length <= 16) return q.toString();
  const n = q.toNumber();
  return Number.isFinite(n) && n !== 0 ? n.toPrecision(digits) : q.toDecimal(digits);
}

function fmtIv(iv) {
  if (iv.isPoint) return `[${fmtQ(iv.lo)}]`;
  return `[${fmtQ(iv.lo)}, ${fmtQ(iv.hi)}]`;
}
