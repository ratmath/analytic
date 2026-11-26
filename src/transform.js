// Fourier transforms beside the Fourier series: the transform on the whole
// line as a pair of certified improper integrals, the standard pairs as
// formulas that are checked against those integrals before they are
// returned, convolution, Parseval's identity, the heat equation on the
// line, and the discrete transform done exactly in the field of the n-th
// roots of unity, with the fast algorithm beside the definition.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { refuse } from "./errors.js";
import { ZERO, ONE, TWO, isZero, toQ } from "./rat.js";
import { toAst, format, num, v as variable, op, call, simplify, derivative, freeVariables, constantRational, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { bitsForDigits } from "./scope.js";
import { fn } from "./fn.js";
import { quad1 } from "./quad.js";
import * as P from "./rpoly.js";
import { tidy } from "./tidy.js";

const qOf = (x) => (x instanceof Rational ? x : typeof x === "string" || typeof x === "number" ? toRational(x) : toQ(x));
const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const A = (x) => (typeof x === "string" || typeof x === "number" ? toAst(String(x)) : x instanceof Rational ? num(x) : toAst(x));
const F = (ast) => format(ast);
const add = (a, b) => op("+", a, b);
const sub = (a, b) => op("-", a, b);
const mul = (a, b) => op("*", a, b);
const div = (a, b) => op("/", a, b);
const pw = (a, b) => op("^", a, b);
const neg = (a) => op("neg", a);
const isNum = (a, k) => a.type === "num" && a.value.equals(Q(k));
const out = (iv) => iv.toRationalInterval();
const overlap = (a, b) => a.low.compareTo(b.high) <= 0 && b.low.compareTo(a.high) <= 0;
const isInf = (x) => x === "inf" || x === "-inf" || x === Infinity || x === -Infinity;

function subst(ast, name, replacement) {
  switch (ast.type) {
    case "var":
      return ast.name === name ? replacement : ast;
    case "op":
      return op(ast.op, ...ast.args.map((a) => subst(a, name, replacement)));
    case "call":
      return call(ast.name, ...ast.args.map((a) => subst(a, name, replacement)));
    default:
      return ast;
  }
}
const depends = (ast, name) => freeVariables(ast).has(name);

/** ∫ of a formula tree over [a, b], either end possibly infinite, enclosed */
function integral(ast, name, a, b, digits) {
  const c = constantRational(ast);
  if (c !== null && isZero(c)) return new RationalInterval(ZERO, ZERO);
  if (isInf(a) || isInf(b)) {
    const r = fn(ast, { variable: name, params: {} }).improperIntegral(a, b, { digits }).exact();
    if (!(r instanceof RationalInterval)) refuse("no-transform", `the integral of ${F(ast)} does not converge absolutely, so it has no certified value here`);
    return r;
  }
  const bits = bitsForDigits(digits) + 32;
  return out(quad1(ast, name, {}, qOf(a), qOf(b), { tol: new Rational(1n, 10n ** BigInt(digits)), bits }).iv);
}

// ---------------------------------------------------------------- the pairs

/** the factors of a product, each with the power it carries */
function flatten(ast, power = 1, list = []) {
  if (ast.type === "op") {
    if (ast.op === "*") return flatten(ast.args[1], power, flatten(ast.args[0], power, list));
    if (ast.op === "/") return flatten(ast.args[1], -power, flatten(ast.args[0], power, list));
    if (ast.op === "neg") {
      list.push({ node: num(-1), power: 1 });
      return flatten(ast.args[0], power, list);
    }
    if (ast.op === "^") {
      const e = constantRational(ast.args[1]);
      if (e !== null && e.denominator === 1n && ast.args[0].type !== "num") return flatten(ast.args[0], power * Number(e.numerator), list);
    }
  }
  list.push({ node: ast, power });
  return list;
}
const product = (list) => {
  let top = null;
  let bottom = null;
  for (const { node, power } of list) {
    const f = Math.abs(power) === 1 ? node : pw(node, num(Math.abs(power)));
    if (power > 0) top = top ? mul(top, f) : f;
    else bottom = bottom ? mul(bottom, f) : f;
  }
  top = top ?? num(1);
  return bottom ? div(top, bottom) : top;
};
/** split the additive terms of a tree */
function terms(ast, sign = 1, list = []) {
  if (ast.type === "op" && ast.op === "+") return terms(ast.args[1], sign, terms(ast.args[0], sign, list));
  if (ast.type === "op" && ast.op === "-") return terms(ast.args[1], -sign, terms(ast.args[0], sign, list));
  if (ast.type === "op" && ast.op === "neg") return terms(ast.args[0], -sign, list);
  list.push(sign < 0 ? neg(ast) : ast);
  return list;
}

/** multiply a complex formula by x: (re, im) ↦ i·d/dω (re + i·im) */
const timesX = ({ re, im }, w) => ({ re: simplify(neg(derivative(im, w))), im: simplify(derivative(re, w)) });
/** Σ c_k x^k applied to a base transform */
function applyPolynomial(poly, base, w) {
  let cur = base;
  let re = null;
  let im = null;
  for (let k = 0; k < poly.length; k++) {
    if (k > 0) cur = timesX(cur, w);
    if (isZero(poly[k])) continue;
    const scale = (t) => (poly[k].equals(ONE) ? t : mul(num(poly[k]), t));
    re = re ? add(re, scale(cur.re)) : scale(cur.re);
    im = im ? add(im, scale(cur.im)) : scale(cur.im);
  }
  return { re: simplify(re ?? num(0)), im: simplify(im ?? num(0)) };
}
/** multiply by e^{−i·m·ω} */
function shift({ re, im }, m, w) {
  if (isZero(m)) return { re, im };
  const mag = m.abs();
  const arg = mag.equals(ONE) ? variable(w) : mul(num(mag), variable(w));
  const c = call("cos", arg);
  const s = m.numerator < 0n ? neg(call("sin", arg)) : call("sin", arg);
  // (re + i im)(c − i s)
  const zero = (t) => {
    const q = constantRational(t);
    return q !== null && isZero(q);
  };
  return {
    re: simplify(zero(im) ? mul(re, c) : add(mul(re, c), mul(im, s))),
    im: simplify(zero(im) ? neg(mul(re, s)) : sub(mul(im, c), mul(re, s))),
  };
}
const sqrtAst = (q) => {
  // √q, as a rational when it is one
  const root = (n) => {
    const r = BigInt(Math.round(Math.sqrt(Number(n))));
    for (const c of [r - 1n, r, r + 1n]) if (c >= 0n && c * c === n) return c;
    return null;
  };
  const a = root(q.numerator);
  const b = root(q.denominator);
  return a !== null && b !== null ? num(new Rational(a, b)) : call("sqrt", num(q));
};

/**
 * The transform of one term as a formula in ω (angular convention), or null
 * when the term is not one of the standard pairs.
 */
function pairOf(term, x, w, support) {
  const W = variable(w);
  let constant = [];
  const rest = [];
  let expArg = null;
  for (const f of flatten(term)) {
    if (!depends(f.node, x)) constant.push(f);
    else if (f.node.type === "call" && f.node.name === "exp") {
      const piece = f.power === 1 ? f.node.args[0] : mul(num(f.power), f.node.args[0]);
      expArg = expArg ? add(expArg, piece) : piece;
    } else rest.push(f);
  }
  const R = P.rationalFunction(product(rest), x);
  if (!R) return null;
  const g = P.gcd(R.num, R.den);
  let top = P.divmod(R.num, g).quo;
  let bottom = P.divmod(R.den, g).quo;
  const lead = bottom[bottom.length - 1];
  top = P.scale(top, lead.reciprocal());
  bottom = P.scale(bottom, lead.reciprocal());
  const polynomial = P.deg(bottom) === 0;
  let name = null;
  let base = null;
  let poly = top;

  if (support) {
    const [a, b] = support;
    if (!isInf(a) && !isInf(b) && !expArg && polynomial && P.deg(top) === 0) {
      // a box: ∫ₐᵇ e^{−iωx} dx = (sin bω − sin aω)/ω + i(cos bω − cos aω)/ω
      const arg = (q) => (q.abs().equals(ONE) ? W : mul(num(q.abs()), W));
      const sinAt = (q) => (isZero(q) ? num(0) : q.numerator < 0n ? neg(call("sin", arg(q))) : call("sin", arg(q)));
      const cosAt = (q) => (isZero(q) ? num(1) : call("cos", arg(q)));
      name = "box";
      const [qa, qb] = [qOf(a), qOf(b)];
      base = qa.negate().equals(qb)
        ? { re: div(mul(num(2), sinAt(qb)), W), im: num(0) }
        : { re: simplify(div(sub(sinAt(qb), sinAt(qa)), W)), im: simplify(div(sub(cosAt(qb), cosAt(qa)), W)) };
    } else if (!isInf(a) && isZero(qOf(a)) && isInf(b) && expArg && polynomial) {
      const e = P.rationalFunction(expArg, x);
      if (!e || P.deg(e.den) !== 0 || P.deg(e.num) !== 1) return null;
      const rate = e.num[1].divide(e.den[0]).negate();
      if (rate.numerator <= 0n) return null;
      const c0 = e.num[0].divide(e.den[0]);
      if (!isZero(c0)) constant.push({ node: call("exp", num(c0)), power: 1 });
      // ∫₀^∞ x^k e^{−ax} e^{−iωx} dx = k!/(a + iω)^{k+1} = k!·(a − iω)^{k+1}/(a² + ω²)^{k+1}
      name = "one-sided exponential";
      let re = null;
      let im = null;
      let fact = ONE;
      for (let k = 0; k < top.length; k++) {
        if (k > 0) fact = fact.multiply(Q(k));
        if (isZero(top[k])) continue;
        const m = k + 1;
        let pr = [ZERO];
        let pi = [ZERO];
        let power = [ONE]; // (a − iω)^m built up as real and imaginary polynomials in ω
        let ipower = [ZERO];
        for (let j = 0; j < m; j++) {
          const nr = P.add(P.scale(power, rate), P.mul(ipower, [ZERO, ONE]));
          const ni = P.sub(P.scale(ipower, rate), P.mul(power, [ZERO, ONE]));
          power = nr;
          ipower = ni;
        }
        pr = power;
        pi = ipower;
        const den = pw(add(num(rate.multiply(rate)), pw(W, num(2))), num(m));
        const coeff = top[k].multiply(fact);
        const piece = (p) => div(polyAst(P.scale(p, coeff), w), m === 1 ? den.args[0] : den);
        re = re ? add(re, piece(pr)) : piece(pr);
        im = im ? add(im, piece(pi)) : piece(pi);
      }
      base = { re: simplify(re), im: simplify(im) };
      poly = [ONE];
    } else return null;
  } else if (expArg) {
    if (!polynomial) return null;
    const e = P.rationalFunction(expArg, x);
    if (e && P.deg(e.den) === 0 && P.deg(e.num) === 2) {
      const d = e.den[0];
      const a = e.num[2].divide(d).negate();
      const b = e.num[1].divide(d);
      const c0 = e.num[0].divide(d);
      if (a.numerator <= 0n) return null;
      // ∫ e^{−ax² + bx + c} e^{−iωx} dx = √(π/a)·e^{c + (b − iω)²/(4a)}
      name = "Gaussian";
      const four = a.multiply(Q(4));
      const shiftConst = c0.add(b.multiply(b).divide(four));
      const exponent = isZero(shiftConst) ? neg(div(pw(W, num(2)), num(four))) : sub(num(shiftConst), div(pw(W, num(2)), num(four)));
      const amp = mul(a.equals(ONE) ? call("sqrt", { type: "const", name: "pi" }) : call("sqrt", div({ type: "const", name: "pi" }, num(a))), call("exp", simplify(exponent)));
      base = shift({ re: amp, im: num(0) }, b.divide(a.multiply(TWO)), w);
    } else {
      // exp(c·|p1·x + p0|) with c·|p1| < 0
      const fs = flatten(expArg);
      let c = ONE;
      let inner = null;
      for (const f of fs) {
        const q = constantRational(f.node);
        if (q !== null) c = f.power > 0 ? c.multiply(q.pow(f.power)) : c.divide(q.pow(-f.power));
        else if (f.node.type === "call" && f.node.name === "abs" && f.power === 1 && !inner) inner = f.node.args[0];
        else return null;
      }
      const lin = inner && P.rationalFunction(inner, x);
      if (!lin || P.deg(lin.den) !== 0 || P.deg(lin.num) !== 1) return null;
      const p1 = lin.num[1].divide(lin.den[0]);
      const p0 = lin.num[0].divide(lin.den[0]);
      const a = c.multiply(p1.abs()).negate();
      if (a.numerator <= 0n) return null;
      // ∫ e^{−a|x|} e^{−iωx} dx = 2a/(a² + ω²)
      name = "two-sided exponential";
      base = shift({ re: div(num(a.multiply(TWO)), add(num(a.multiply(a)), pw(W, num(2)))), im: num(0) }, p0.divide(p1).negate(), w);
    }
  } else {
    // β/(x² + px + q) with no real root
    if (P.deg(top) !== 0 || P.deg(bottom) !== 2) return null;
    const p = bottom[1];
    const q = bottom[0];
    const s2 = q.subtract(p.multiply(p).divide(Q(4)));
    if (s2.numerator <= 0n) return null;
    // ∫ e^{−iωx}/(x² + s²) dx = (π/s)·e^{−s|ω|}
    name = "Lorentzian";
    const s = sqrtAst(s2);
    const decay = call("exp", simplify(neg(mul(s, call("abs", W)))));
    base = shift({ re: mul(div({ type: "const", name: "pi" }, s), decay), im: num(0) }, p.divide(TWO).negate(), w);
  }
  let res = applyPolynomial(poly, base, w);
  const numeric = constant.reduce((c, f) => {
    const q = constantRational(f.node);
    return c === null || q === null ? null : f.power > 0 ? c.multiply(q.pow(f.power)) : c.divide(q.pow(-f.power));
  }, ONE);
  const k = numeric !== null ? num(numeric) : product(constant);
  if (!isNum(k, 1)) res = { re: simplify(mul(k, res.re)), im: simplify(mul(k, res.im)) };
  return { name, ...res };
}
function polyAst(p, name) {
  let outAst = null;
  for (let k = p.length - 1; k >= 0; k--) {
    if (isZero(p[k])) continue;
    const mag = p[k].abs();
    const x = k === 0 ? null : k === 1 ? variable(name) : pw(variable(name), num(k));
    const t = x === null ? num(mag) : mag.equals(ONE) ? x : mul(num(mag), x);
    if (outAst === null) outAst = p[k].numerator < 0n ? neg(t) : t;
    else outAst = p[k].numerator < 0n ? sub(outAst, t) : add(outAst, t);
  }
  return outAst ?? num(0);
}

const CONVENTIONS = {
  // F(ω) = prefactor·∫ f(x)·e^{−i·k·ω·x} dx, and the inverse carries `back`
  angular: { k: null, prefactor: null, back: "1/(2*pi)", kernel: "e^(-i*w*x)" },
  unitary: { k: null, prefactor: "1/sqrt(2*pi)", back: "1/sqrt(2*pi)", kernel: "e^(-i*w*x)/sqrt(2*pi)" },
  frequency: { k: "2*pi", prefactor: null, back: "1", kernel: "e^(-2*pi*i*w*x)" },
};
const conventionOf = (name = "angular") => CONVENTIONS[name] ?? refuse("bad-convention", "convention is angular, unitary or frequency");

/** a complex number as a pair of enclosures */
const complex = (re, im) => ({ re, im, toString: () => `${re.low.toNumber()} + ${im.low.toNumber()}i` });

export class FourierTransform {
  constructor(f, opts = {}) {
    this.variable = opts.variable ?? "x";
    this.frequency = opts.frequency ?? "w";
    this.convention = opts.convention ?? "angular";
    this.digits = opts.digits ?? 15;
    this.support = opts.support ? [opts.support[0], opts.support[1]] : ["-inf", "inf"];
    this.f = A(f);
    this.text = F(this.f);
    const conv = conventionOf(this.convention);
    this._k = conv.k ? A(conv.k) : null;
    this._pre = conv.prefactor ? A(conv.prefactor) : null;
    this.kernel = conv.kernel.replaceAll("w", this.frequency).replaceAll("x", this.variable);
    this.formula = null;
    this.pairs = [];
    this._formula(opts);
  }

  _formula(opts) {
    if (opts.formula === false) return;
    const w = this.frequency;
    const whole = isInf(this.support[0]) && isInf(this.support[1]);
    let re = null;
    let im = null;
    const names = [];
    for (const term of terms(this.f)) {
      let p;
      try {
        p = pairOf(term, this.variable, w, whole ? null : this.support);
      } catch (e) {
        if (opts.debug) throw e;
        p = null;
      }
      if (!p) return;
      names.push(p.name);
      re = re ? add(re, p.re) : p.re;
      im = im ? add(im, p.im) : p.im;
    }
    re = simplify(re);
    im = simplify(im);
    if (this._k) {
      const arg = mul(this._k, variable(w));
      re = simplify(subst(re, w, arg));
      im = simplify(subst(im, w, arg));
    }
    const isZeroTree = (t) => {
      const q = constantRational(t);
      return q !== null && isZero(q);
    };
    if (this._pre) {
      re = isZeroTree(re) ? re : simplify(mul(this._pre, re));
      im = isZeroTree(im) ? im : simplify(mul(this._pre, im));
    }
    const neat = (t) => {
      // a purely rational formula reads better as one fraction
      if (!P.rationalFunction(t, w)) return t;
      try {
        const u = tidy(t);
        return F(u).length <= F(t).length ? u : t;
      } catch {
        return t;
      }
    };
    re = neat(re);
    im = neat(im);
    const candidate = { re, im };
    // a formula is only returned after it has agreed with the certified integrals
    for (const probe of [Q(3, 7), Q(-5, 4)]) {
      const exact = this.at(probe, { digits: 8 });
      const got = this._evaluate(candidate, probe, 12);
      if (!overlap(exact.re, got.re) || !overlap(exact.im, got.im)) return;
    }
    this._trees = candidate;
    this.formula = { re: F(re), im: F(im), text: isZeroTree(im) ? F(re) : isZeroTree(re) ? `i*(${F(im)})` : `${F(re)} + i*(${F(im)})`, trust: "checked" };
    this.pairs = names;
  }

  _evaluate(trees, w, digits) {
    const bits = bitsForDigits(digits) + 32;
    const env = { [this.frequency]: Iv.point(qOf(w)) };
    return complex(out(encloseAst(trees.re, env, bits)), out(encloseAst(trees.im, env, bits)));
  }

  /** F(ω) from the integrals themselves: { re, im }, each a certified enclosure. */
  at(w, opts = {}) {
    const digits = opts.digits ?? this.digits;
    const W = qOf(w);
    const X = variable(this.variable);
    let phase = isZero(W) ? null : mul(num(W), X);
    if (phase && this._k) phase = mul(this._k, phase);
    const [a, b] = this.support;
    let re = integral(phase ? mul(this.f, call("cos", phase)) : this.f, this.variable, a, b, digits);
    let im = phase ? integral(neg(mul(this.f, call("sin", phase))), this.variable, a, b, digits) : new RationalInterval(ZERO, ZERO);
    if (this._pre) {
      const c = encloseAst(this._pre, {}, bitsForDigits(digits) + 32);
      re = out(Iv.from(re).mul(c));
      im = out(Iv.from(im).mul(c));
    }
    return complex(re, im);
  }

  /** the formula evaluated at ω (needs a recognised pair) */
  formulaAt(w, opts = {}) {
    if (!this._trees) refuse("no-formula", `${this.text} is not one of the standard pairs; at(ω) still gives certified values`);
    return this._evaluate(this._trees, w, opts.digits ?? this.digits);
  }

  /** formula and integral side by side at ω */
  check(w, opts = {}) {
    const integralValue = this.at(w, opts);
    const formulaValue = this.formulaAt(w, opts);
    return { integral: integralValue, formula: formulaValue, agrees: overlap(integralValue.re, formulaValue.re) && overlap(integralValue.im, formulaValue.im) };
  }

  /**
   * The inversion theorem at x: the inverse transform of the formula beside
   * f(x) itself: { inverse, value, agrees }.
   */
  inversion(x, opts = {}) {
    if (!this._trees) refuse("no-formula", "inversion is checked from the formula, and there is none for this function");
    const inv = new InverseFourier(this._trees, { variable: this.frequency, to: this.variable, convention: this.convention, digits: opts.digits ?? this.digits }).at(x);
    const X = qOf(x);
    const [a, b] = this.support;
    const inside = (isInf(a) || qOf(a).compareTo(X) < 0) && (isInf(b) || X.compareTo(qOf(b)) < 0);
    const value = inside ? out(encloseAst(this.f, { [this.variable]: Iv.point(X) }, bitsForDigits(opts.digits ?? this.digits) + 32)) : new RationalInterval(ZERO, ZERO);
    return { inverse: inv, value, agrees: overlap(inv.re, value) && inv.im.low.compareTo(ZERO) <= 0 && inv.im.high.compareTo(ZERO) >= 0 };
  }

  /**
   * Parseval's identity (Plancherel): ∫|f|² dx beside the same from the
   * transform's formula: { time, frequency, agrees }.
   */
  parseval(opts = {}) {
    if (!this._trees) refuse("no-formula", "the frequency side is integrated from the formula, and there is none for this function");
    const digits = opts.digits ?? this.digits;
    const [a, b] = this.support;
    const time = integral(pw(this.f, num(2)), this.variable, a, b, digits);
    const power = simplify(add(pw(this._trees.re, num(2)), pw(this._trees.im, num(2))));
    const raw = integral(power, this.frequency, "-inf", "inf", digits);
    const back = this.convention === "angular" ? A("1/(2*pi)") : null;
    const frequency = back ? out(Iv.from(raw).mul(encloseAst(back, {}, bitsForDigits(digits) + 32))) : raw;
    return { time, frequency, agrees: overlap(time, frequency) };
  }
}

/**
 * The Fourier transform F(ω) = ∫ f(x)·e^{−iωx} dx of a function on the whole
 * line, or on `support: [a, b]` (zero outside it).
 *   fourierTransform("exp(-x^2)").at(2)          → { re, im } enclosures
 *   fourierTransform("exp(-x^2)").formula.text   → "sqrt(pi)*exp(-w^2/4)"
 * Conventions: "angular" (default), "unitary" (1/√(2π) on both sides) and
 * "frequency" (e^{−2πiξx}).
 */
export function fourierTransform(f, opts = {}) {
  return new FourierTransform(f, opts);
}

export class InverseFourier {
  constructor(Fw, opts = {}) {
    this.variable = opts.variable ?? "w";
    this.to = opts.to ?? "x";
    this.convention = opts.convention ?? "angular";
    this.digits = opts.digits ?? 15;
    const parts = Fw && typeof Fw === "object" && "re" in Fw ? Fw : { re: Fw, im: 0 };
    this.re = A(parts.re);
    this.im = A(parts.im ?? 0);
    const conv = conventionOf(this.convention);
    this._k = conv.k ? A(conv.k) : null;
    this._back = A(conv.back);
  }
  /** f(x) = back·∫ F(ω)·e^{+iωx} dω: { re, im } enclosures */
  at(x, opts = {}) {
    const digits = opts.digits ?? this.digits;
    const X = qOf(x);
    const W = variable(this.variable);
    let phase = isZero(X) ? null : mul(num(X), W);
    if (phase && this._k) phase = mul(this._k, phase);
    const zeroIm = (() => {
      const q = constantRational(this.im);
      return q !== null && isZero(q);
    })();
    let reAst = this.re;
    let imAst = this.im;
    if (phase) {
      const c = call("cos", phase);
      const s = call("sin", phase);
      reAst = zeroIm ? mul(this.re, c) : sub(mul(this.re, c), mul(this.im, s));
      imAst = zeroIm ? mul(this.re, s) : add(mul(this.re, s), mul(this.im, c));
    }
    const back = encloseAst(this._back, {}, bitsForDigits(digits) + 32);
    const side = (ast) => out(Iv.from(integral(ast, this.variable, "-inf", "inf", digits)).mul(back));
    return complex(side(reAst), side(imAst));
  }
}
/**
 * The inverse transform f(x) = (1/2π)·∫ F(ω)·e^{iωx} dω, from a formula for
 * F (a string for a real F, or { re, im }): inverseFourier(F).at(x).
 */
export function inverseFourier(Fw, opts = {}) {
  return new InverseFourier(Fw, opts);
}

/**
 * The convolution (f ∗ g)(x) = ∫ f(t)·g(x − t) dt: { at(x), theorem(x) }.
 * `at` is a certified enclosure; `theorem` computes the same number as the
 * inverse transform of F·G, which is the convolution theorem as a checked
 * statement (it needs both transforms as formulas).
 */
export function convolution(f, g, opts = {}) {
  const x = opts.variable ?? "x";
  const digits = opts.digits ?? 15;
  const fa = A(f);
  const ga = A(g);
  const t = "t_";
  const at = (X) => {
    const integrand = mul(subst(fa, x, variable(t)), subst(ga, x, sub(num(qOf(X)), variable(t))));
    return integral(integrand, t, "-inf", "inf", digits);
  };
  return {
    at,
    theorem(X) {
      const Ff = new FourierTransform(fa, { variable: x, digits });
      const Fg = new FourierTransform(ga, { variable: x, digits });
      if (!Ff._trees || !Fg._trees) refuse("no-formula", "the convolution theorem is checked from the two transforms as formulas, and one of these functions is not a standard pair");
      const product = {
        re: simplify(sub(mul(Ff._trees.re, Fg._trees.re), mul(Ff._trees.im, Fg._trees.im))),
        im: simplify(add(mul(Ff._trees.re, Fg._trees.im), mul(Ff._trees.im, Fg._trees.re))),
      };
      const viaTransforms = new InverseFourier(product, { digits }).at(X).re;
      const direct = at(X);
      return { convolution: direct, viaTransforms, transform: { re: F(product.re), im: F(product.im) }, agrees: overlap(direct, viaTransforms) };
    },
  };
}

/**
 * The heat equation u_t = k·u_xx on the whole line with u(x, 0) = f(x):
 * u(x, t) = ∫ f(y)·e^{−(x − y)²/(4kt)}/√(4πkt) dy.
 * { at(x, t), viaTransform(x, t), check(x, t), heat() }: `at` is the certified
 * value of that integral, `viaTransform` the same number as the inverse
 * transform of F(ω)·e^{−kω²t}, and heat() the total ∫ u dx, which the
 * equation conserves.
 */
export function heatLine(spec) {
  const k = qOf(spec.k ?? 1);
  if (k.numerator <= 0n) refuse("bad-problem", "k must be positive");
  const x = spec.x ?? "x";
  const digits = spec.digits ?? 12;
  const f = A(spec.initial);
  const support = spec.support ?? ["-inf", "inf"];
  const y = "y_";
  const at = (X, T) => {
    const xq = qOf(X);
    const tq = qOf(T);
    if (tq.numerator < 0n) refuse("bad-point", "the heat equation runs forward in time: t must not be negative");
    if (isZero(tq)) return out(encloseAst(f, { [x]: Iv.point(xq) }, bitsForDigits(digits) + 32));
    const four = k.multiply(tq).multiply(Q(4));
    const kernel = div(call("exp", neg(div(pw(sub(num(xq), variable(y)), num(2)), num(four)))), call("sqrt", mul(num(four), { type: "const", name: "pi" })));
    return integral(mul(subst(f, x, variable(y)), kernel), y, support[0], support[1], digits);
  };
  let transform = null;
  const viaTransform = (X, T) => {
    transform ??= new FourierTransform(f, { variable: x, digits, support });
    if (!transform._trees) refuse("no-formula", "this route needs the transform of the initial temperature as a formula");
    const damp = call("exp", neg(mul(num(k.multiply(qOf(T))), pw(variable("w"), num(2)))));
    return new InverseFourier({ re: mul(transform._trees.re, damp), im: mul(transform._trees.im, damp) }, { digits }).at(X).re;
  };
  return {
    equation: `u_t = ${k.equals(ONE) ? "" : `${k}*`}u_xx on the whole line, u(${x}, 0) = ${F(f)}`,
    at,
    viaTransform,
    check(X, T) {
      const direct = at(X, T);
      const other = viaTransform(X, T);
      return { kernel: direct, viaTransform: other, agrees: overlap(direct, other) };
    },
    heat: () => integral(f, x, support[0], support[1], digits),
  };
}

// ---------------------------------------------------------------- the discrete transform, exactly

const CYCLO = new Map();
/** the n-th cyclotomic polynomial, coefficients from the constant term up */
export function cyclotomic(n) {
  if (!Number.isInteger(n) || n < 1) refuse("bad-order", "n must be a positive whole number");
  if (CYCLO.has(n)) return CYCLO.get(n);
  let p = new Array(n + 1).fill(ZERO);
  p[0] = Q(-1);
  p[n] = ONE;
  for (let d = 1; d < n; d++) if (n % d === 0) p = P.divmod(p, cyclotomic(d)).quo;
  CYCLO.set(n, p);
  return p;
}

/**
 * An element of Q(ζ) with ζ = e^{2πi/n}: an exact complex number built from
 * n-th roots of unity. Kept as a polynomial in ζ of degree below φ(n), which
 * is unique, so two elements are equal exactly when their coefficients are.
 */
export class Cyclotomic {
  constructor(n, coefficients) {
    this.n = n;
    const phi = cyclotomic(n);
    let c = coefficients.map(qOf);
    if (c.length >= phi.length) {
      // fold with ζⁿ = 1, then reduce by the cyclotomic polynomial
      if (c.length > n) {
        const folded = new Array(n).fill(ZERO);
        c.forEach((q, i) => (folded[i % n] = folded[i % n].add(q)));
        c = folded;
      }
      if ((n & (n - 1)) === 0 && n > 1) {
        // Φ = x^{n/2} + 1: the top half folds onto the bottom with a sign
        const h = n / 2;
        c = Array.from({ length: h }, (_, i) => (c[i] ?? ZERO).subtract(c[i + h] ?? ZERO));
      } else c = P.divmod(P.trim(c), phi).rem;
    }
    c = c.slice();
    while (c.length < phi.length - 1) c.push(ZERO);
    this.coefficients = c.slice(0, phi.length - 1);
  }
  static root(n, k = 1) {
    const c = new Array(n).fill(ZERO);
    c[((k % n) + n) % n] = ONE;
    return new Cyclotomic(n, c);
  }
  static of(n, q) {
    return q instanceof Cyclotomic ? (q.n === n ? q : refuse("bad-order", `this number lives with the ${q.n}-th roots of unity, not the ${n}-th`)) : new Cyclotomic(n, [qOf(q)]);
  }
  /** the coefficients as a vector over all n powers of ζ (not reduced) */
  _wide() {
    const c = this.coefficients.slice();
    while (c.length < this.n) c.push(ZERO);
    return c;
  }
  add(o) {
    const b = Cyclotomic.of(this.n, o);
    return new Cyclotomic(this.n, this.coefficients.map((c, i) => c.add(b.coefficients[i])));
  }
  subtract(o) {
    const b = Cyclotomic.of(this.n, o);
    return new Cyclotomic(this.n, this.coefficients.map((c, i) => c.subtract(b.coefficients[i])));
  }
  scale(q) {
    const r = qOf(q);
    return new Cyclotomic(this.n, this.coefficients.map((c) => c.multiply(r)));
  }
  /** multiply by ζᵏ: a rotation of the coefficients */
  rotate(k) {
    const n = this.n;
    const s = ((k % n) + n) % n;
    const c = new Array(n).fill(ZERO);
    this.coefficients.forEach((q, i) => (c[(i + s) % n] = c[(i + s) % n].add(q)));
    return new Cyclotomic(n, c);
  }
  multiply(o) {
    if (!(o instanceof Cyclotomic)) return this.scale(o);
    Cyclotomic.of(this.n, o);
    return new Cyclotomic(this.n, P.mul(P.trim(this.coefficients.slice()), P.trim(o.coefficients.slice())));
  }
  /** complex conjugate: ζ ↦ ζ⁻¹ */
  conjugate() {
    const n = this.n;
    const c = new Array(n).fill(ZERO);
    this.coefficients.forEach((q, i) => (c[(n - i) % n] = c[(n - i) % n].add(q)));
    return new Cyclotomic(n, c);
  }
  /** |z|² = z·z̄, a real element */
  norm2() {
    return this.multiply(this.conjugate());
  }
  equals(o) {
    const b = Cyclotomic.of(this.n, o);
    return this.coefficients.every((c, i) => c.equals(b.coefficients[i]));
  }
  isRational() {
    return this.coefficients.slice(1).every(isZero);
  }
  /** the value as a rational when it is one, else null */
  rational() {
    return this.isRational() ? (this.coefficients[0] ?? ZERO) : null;
  }
  /** { re, im } as certified enclosures */
  enclose(digits = 20) {
    const bits = bitsForDigits(digits) + 32;
    let re = Iv.point(ZERO);
    let im = Iv.point(ZERO);
    this.coefficients.forEach((q, j) => {
      if (isZero(q)) return;
      const angle = { a_: Iv.point(new Rational(BigInt(2 * j), BigInt(this.n))) };
      re = re.add(encloseAst(toAst("cos(a_*pi)"), angle, bits).scale(q));
      im = im.add(encloseAst(toAst("sin(a_*pi)"), angle, bits).scale(q));
    });
    return complex(out(re), out(im));
  }
  toNumber() {
    let re = 0;
    let im = 0;
    this.coefficients.forEach((q, j) => {
      re += q.toNumber() * Math.cos((2 * Math.PI * j) / this.n);
      im += q.toNumber() * Math.sin((2 * Math.PI * j) / this.n);
    });
    return { re, im };
  }
  toString() {
    const parts = [];
    this.coefficients.forEach((q, j) => {
      if (isZero(q)) return;
      const mag = q.abs();
      const z = j === 0 ? "" : j === 1 ? "ζ" : `ζ^${j}`;
      const body = j === 0 ? mag.toString() : mag.equals(ONE) ? z : `${mag.denominator === 1n ? mag : `(${mag})`}${z}`;
      parts.push(parts.length ? `${q.numerator < 0n ? "-" : "+"} ${body}` : `${q.numerator < 0n ? "-" : ""}${body}`);
    });
    return parts.length ? parts.join(" ") : "0";
  }
}
/** ζᵏ with ζ = e^{2πi/n} */
export const rootOfUnity = (n, k = 1) => Cyclotomic.root(n, k);

const listOf = (values) => {
  const n = values.length;
  if (n < 1) refuse("bad-input", "give at least one value");
  return values.map((x) => Cyclotomic.of(n, x));
};
const spectrumOf = (values, extra) => ({
  n: values.length,
  values,
  text: values.map(String),
  /** every entry as { re, im } enclosures */
  enclose: (digits = 20) => values.map((z) => z.enclose(digits)),
  /** |X_k|², exact when it is rational and otherwise the exact field element */
  power: () => values.map((z) => z.norm2().rational() ?? z.norm2()),
  ...extra,
});

/**
 * The discrete Fourier transform by its definition, exactly:
 * X_k = Σ_j x_j·ζ^{−jk} with ζ = e^{2πi/n}. Inputs are rationals (or
 * Cyclotomic numbers of the same n). { values, text, enclose(), power(),
 * multiplications }. With { inverse: true }: x_j = (1/n)·Σ_k X_k·ζ^{jk}.
 */
export function dft(input, opts = {}) {
  const xs = listOf(input);
  const n = xs.length;
  const sign = opts.inverse ? 1 : -1;
  const wide = xs.map((z) => z._wide());
  const values = [];
  for (let k = 0; k < n; k++) {
    const acc = new Array(n).fill(ZERO);
    for (let j = 0; j < n; j++) {
      const s = (((sign * j * k) % n) + n) % n;
      const row = wide[j];
      for (let i = 0; i < n; i++) if (!isZero(row[i])) acc[(i + s) % n] = acc[(i + s) % n].add(row[i]);
    }
    let z = new Cyclotomic(n, acc);
    if (opts.inverse) z = z.scale(new Rational(1n, BigInt(n)));
    values.push(z);
  }
  return spectrumOf(values, { multiplications: n * n, inverse: !!opts.inverse });
}

/**
 * The fast Fourier transform (radix 2, n a power of two), exactly, with the
 * count of multiplications by a root of unity beside the n² of the
 * definition: { values, multiplications, definition, levels, agrees }.
 * `agrees` is the exact comparison with dft(); it is skipped (null) beyond
 * n = 256 unless { check: true }.
 */
export function fft(input, opts = {}) {
  const xs = listOf(input);
  const n = xs.length;
  if (n & (n - 1)) refuse("bad-length", "this fast algorithm halves the list at every level, so the length must be a power of two");
  const sign = opts.inverse ? 1 : -1;
  let multiplications = 0;
  const levels = [];
  const rec = (list, step, depth) => {
    const m = list.length;
    if (m === 1) return list;
    const even = rec(list.filter((_, i) => i % 2 === 0), step * 2, depth + 1);
    const odd = rec(list.filter((_, i) => i % 2 === 1), step * 2, depth + 1);
    const res = new Array(m);
    for (let k = 0; k < m / 2; k++) {
      const t = odd[k].rotate(sign * step * k);
      multiplications++;
      res[k] = even[k].add(t);
      res[k + m / 2] = even[k].subtract(t);
    }
    levels[depth] = (levels[depth] ?? 0) + m / 2;
    return res;
  };
  let values = rec(xs, 1, 0);
  if (opts.inverse) values = values.map((z) => z.scale(new Rational(1n, BigInt(n))));
  const check = opts.check ?? n <= 256;
  const agrees = check ? dft(input, opts).values.every((z, i) => z.equals(values[i])) : null;
  return spectrumOf(values, { multiplications, definition: n * n, levels: levels.length, perLevel: levels, agrees, inverse: !!opts.inverse });
}

// ---------------------------------------------------------------- sampling and aliasing

/**
 * A sinusoid of a given frequency sampled at a given rate looks, at the
 * samples, exactly like one of the alias frequency in [0, rate/2]:
 * { frequency, rate, nyquist, alias, sign, aliased }. For a sine the alias
 * comes with `sign` (−1 when the fold reverses it); a cosine is unchanged.
 */
export function alias(frequency, rate) {
  const f = qOf(frequency);
  const r = qOf(rate);
  if (r.numerator <= 0n) refuse("bad-rate", "the sampling rate must be positive");
  const half = r.divide(TWO);
  // nearest multiple of the rate, ties towards the lower one so the remainder lies in (−rate/2, rate/2]
  const ratio = f.divide(r);
  let m = (TWO.multiply(ratio).numerator * 1n + TWO.multiply(ratio).denominator) / (TWO.multiply(ratio).denominator * 2n);
  let rem = f.subtract(r.multiply(new Rational(m)));
  while (rem.compareTo(half) > 0) rem = rem.subtract(r);
  while (rem.compareTo(half.negate()) <= 0) rem = rem.add(r);
  return { frequency: f, rate: r, nyquist: half, alias: rem.abs(), sign: rem.numerator < 0n ? -1 : 1, aliased: f.abs().compareTo(half) > 0 };
}

/**
 * count samples of cos (or sin) of 2π·frequency·t at t = k/rate, exactly, as
 * numbers built from roots of unity. This needs frequency·count/rate to be
 * a whole number (the samples then cover whole periods), and for a sine a
 * count divisible by 4.
 */
export function sinusoidSamples(spec) {
  const f = qOf(spec.frequency);
  const r = qOf(spec.rate);
  const n = spec.count;
  const turns = f.multiply(Q(n)).divide(r);
  if (turns.denominator !== 1n) refuse("bad-sampling", "frequency*count/rate must be a whole number, so the samples cover whole periods exactly");
  const m = Number(turns.numerator);
  const kind = spec.kind ?? "cos";
  if (kind === "sin" && n % 4) refuse("bad-sampling", "an exact sine needs i among the roots of unity: use a count divisible by 4");
  const half = new Rational(1n, 2n);
  const samples = [];
  for (let k = 0; k < n; k++) {
    const up = Cyclotomic.root(n, m * k);
    const down = Cyclotomic.root(n, -m * k);
    samples.push(kind === "cos" ? up.add(down).scale(half) : up.subtract(down).scale(half).rotate(-n / 4));
  }
  return samples;
}

/**
 * f sampled at t = from + k/rate for k = 0 … count − 1: { times, values }
 * with exact times and each value a certified enclosure.
 */
export function sample(f, spec) {
  const name = spec.variable ?? "t";
  const r = qOf(spec.rate);
  const from = qOf(spec.from ?? 0);
  const ast = A(f);
  const bits = bitsForDigits(spec.digits ?? 15) + 32;
  const times = [];
  const values = [];
  for (let k = 0; k < spec.count; k++) {
    const t = from.add(Q(k).divide(r));
    times.push(t);
    values.push(out(encloseAst(ast, { [name]: Iv.point(t) }, bits)));
  }
  return { times, values };
}
