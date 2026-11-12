// A ready-made set of callable functions for evaluators (RatTree's function
// worker, RatCalc): each name works on Core numbers, Core intervals and
// Taylor models alike.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { TWO, toQ } from "./rat.js";
import { TaylorModel, Domain, DEFAULTS } from "./model.js";
import * as E from "./elementary.js";
import { enclose, constants } from "./enclose.js";
import { series } from "./series.js";
import { AnalyticError, refuse } from "./errors.js";

const NAMES = ["exp", "log", "log1p", "sqrt", "sin", "cos", "tan", "atan", "sinh", "cosh", "tanh"];

/** Bits needed for `digits` correct decimal digits, with guard bits. */
export function bitsForDigits(digits) {
  return Math.ceil(Number(digits) * 3.3219280948873626) + 8;
}

/**
 * createScope({ digits, bits, order }) → { exp, sin, ..., model, integral, range, pi, e, TM, Domain, series }
 *
 * exp(x) on a Rational/Integer/RationalInterval returns a certified
 * RationalInterval at the scope's precision; on a TaylorModel it returns a
 * TaylorModel. model(f, domain) builds the model of x ↦ f(x) on a domain.
 */
export function createScope(opts = {}) {
  const bits = opts.bits ?? (opts.digits !== undefined ? bitsForDigits(opts.digits) : DEFAULTS.bits);
  const order = opts.order ?? DEFAULTS.order;
  const scope = {};
  for (const name of NAMES) {
    scope[name] = (x) => (x instanceof TaylorModel ? E[name](x) : enclose[name](x, bits));
  }
  scope.pow = (x, a) => (x instanceof TaylorModel ? E.power(x, toQ(a)) : refuse("bad-operand", "pow(x, a) here is for Taylor models; use Core's pow for numbers"));

  /** Taylor model of f on the domain: f receives the identity model x. */
  scope.model = (f, domain, o = {}) => {
    const x = TaylorModel.x(Domain(domain), { order: o.order ?? order, bits: o.bits ?? bits });
    const m = f(x);
    return m instanceof TaylorModel ? m : TaylorModel.constant(x.domain, m, { order, bits });
  };

  /** Certified ∫_a^b f, splitting [a, b] into `pieces` models. */
  scope.integral = (f, a, b, o = {}) => {
    const lo = toQ(a);
    const hi = toQ(b);
    const n = o.pieces ?? 4;
    const step = hi.subtract(lo).divide(new Rational(BigInt(n)));
    let acc = Iv.point(new Rational(0n));
    for (let i = 0; i < n; i++) {
      const p = lo.add(step.multiply(new Rational(BigInt(i))));
      const q = i === n - 1 ? hi : p.add(step);
      acc = acc.add(Iv.from(scope.model(f, [p, q], o).integral()));
    }
    return acc.toRationalInterval();
  };

  /** Certified range of f over an interval, splitting it into `pieces` models. */
  scope.range = (f, interval, o = {}) => {
    const v = Iv.from(interval);
    const n = o.pieces ?? 4;
    const step = v.width.divide(new Rational(BigInt(n)));
    let acc = null;
    for (let i = 0; i < n; i++) {
      const p = v.lo.add(step.multiply(new Rational(BigInt(i))));
      const q = i === n - 1 ? v.hi : p.add(step);
      const r = Iv.from(scope.model(f, [p, q], o).range());
      acc = acc ? acc.hull(r) : r;
    }
    return acc.toRationalInterval();
  };

  scope.pi = constants.pi(bits);
  scope.e = constants.e(bits);
  scope.TM = TaylorModel;
  scope.Domain = Domain;
  scope.series = (domain, spec) => series(domain, { order, bits, ...spec });
  scope.AnalyticError = AnalyticError;
  scope.bits = bits;
  return scope;
}
