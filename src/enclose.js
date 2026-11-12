// Certified enclosures of elementary functions at Core numbers and intervals.
// Points use the series in points.js; intervals use monotonicity where it
// holds and Taylor-model ranges otherwise.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { ZERO, ONE, TWO, HALF, rat, le, lt, gt, isZero } from "./rat.js";
import { expPoint, logPoint, atanPoint, sqrtPoint, sinCosPoint, piIv } from "./points.js";
import { refuse } from "./errors.js";
import { TaylorModel, Domain } from "./model.js";
import * as E from "./elementary.js";

const out = (iv) => iv.toRationalInterval();

function monotone(pointFn, check) {
  return (x, bits = 96) => {
    const v = Iv.from(x);
    if (check) check(v);
    if (v.isPoint) return out(pointFn(v.lo, bits));
    return out(new Iv(pointFn(v.lo, bits).lo, pointFn(v.hi, bits).hi));
  };
}

export const enclose = {
  exp: monotone(expPoint),
  log: monotone(logPoint, (v) => {
    if (le(v.lo, ZERO)) refuse("domain", `log needs positive arguments, got ${v}`);
  }),
  sqrt: monotone(sqrtPoint, (v) => {
    if (lt(v.lo, ZERO)) refuse("domain", `sqrt needs non-negative arguments, got ${v}`);
  }),
  atan: monotone(atanPoint),
  sin(x, bits = 96) {
    const v = Iv.from(x);
    if (v.isPoint) return out(sinCosPoint(v.lo, bits).sin);
    if (gt(v.width, rat(6))) return out(new Iv(rat(-1), ONE));
    return pieces(v, bits, E.sin, new Iv(rat(-1), ONE));
  },
  cos(x, bits = 96) {
    const v = Iv.from(x);
    if (v.isPoint) return out(sinCosPoint(v.lo, bits).cos);
    if (gt(v.width, rat(6))) return out(new Iv(rat(-1), ONE));
    return pieces(v, bits, E.cos, new Iv(rat(-1), ONE));
  },
  tan(x, bits = 96) {
    const v = Iv.from(x);
    if (v.isPoint) {
      const { sin, cos } = sinCosPoint(v.lo, bits + 8);
      return out(sin.div(cos).roundOut(bits + 4));
    }
    return pieces(v, bits, E.tan);
  },
};
enclose.log1p = (x, bits = 96) => enclose.log(Iv.from(x).add(ONE), bits);
enclose.sinh = (x, bits = 96) => {
  const v = Iv.from(x);
  const f = (q) => {
    const e = expPoint(q, bits + 8);
    return e.sub(e.recip()).scale(HALF);
  };
  return out(v.isPoint ? f(v.lo).roundOut(bits + 4) : new Iv(f(v.lo).lo, f(v.hi).hi));
};
enclose.cosh = (x, bits = 96) => {
  const v = Iv.from(x);
  const f = (q) => {
    const e = expPoint(q, bits + 8);
    return e.add(e.recip()).scale(HALF);
  };
  if (v.isPoint) return out(f(v.lo).roundOut(bits + 4));
  const a = f(v.lo);
  const b = f(v.hi);
  const lo = v.containsZero() ? ONE : (lt(a.lo, b.lo) ? a.lo : b.lo);
  return out(new Iv(lo, gt(a.hi, b.hi) ? a.hi : b.hi));
};
enclose.tanh = (x, bits = 96) => {
  const v = Iv.from(x);
  const f = (q) => {
    const e = expPoint(q.multiply(TWO), bits + 8);
    return e.sub(ONE).div(e.add(ONE));
  };
  return out(v.isPoint ? f(v.lo).roundOut(bits + 4) : new Iv(f(v.lo).lo, f(v.hi).hi));
};

/** Range of a non-monotone function on an interval: split into pieces of width ≤ 1/2. */
function pieces(v, bits, fn, clamp) {
  const n = Math.max(1, Math.min(64, Math.ceil(v.width.multiply(TWO).toNumber())));
  const step = v.width.divide(new Rational(BigInt(n)));
  let acc = null;
  for (let i = 0; i < n; i++) {
    const a = v.lo.add(step.multiply(new Rational(BigInt(i))));
    const b = i === n - 1 ? v.hi : a.add(step);
    const m = fn(TaylorModel.x(Domain(new Iv(a, b)), { order: 10, bits }));
    const r = m.bound(6);
    acc = acc ? acc.hull(r) : r;
  }
  if (clamp) acc = acc.intersect(clamp) ?? acc;
  return out(acc.roundOut(bits + 4));
}

export const constants = {
  pi: (bits = 96) => out(piIv(bits)),
  e: (bits = 96) => out(expPoint(ONE, bits)),
};
