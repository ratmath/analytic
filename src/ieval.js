// Plain interval evaluation of an expression tree: cheaper than a Taylor
// model and enough for exclusion tests, Krawczyk steps and sign checks.
// Endpoints are exact Rationals, rounded outward to about `bits` bits after
// each operation so they stay small.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { ZERO, ONE, TWO, HALF, rat, lt, le, gt, ge, isZero, min, max } from "./rat.js";
import { expPoint, logPoint, atanPoint, sqrtPoint, sinCosPoint, piIv } from "./points.js";
import { refuse } from "./errors.js";
import { constantRational } from "./expr.js";

const R = (iv, bits) => iv.roundOut(bits);

function monotone(pointFn, v, bits, up = true) {
  if (v.isPoint) return pointFn(v.lo, bits);
  const a = pointFn(v.lo, bits);
  const b = pointFn(v.hi, bits);
  return up ? new Iv(a.lo, b.hi) : new Iv(b.lo, a.hi);
}

/**
 * sin (phase 0) or cos (phase 1) on an interval: endpoint values, widened to
 * ±1 when a maximum or minimum might lie inside. Extremes of sin are at
 * π/2 + kπ; of cos at kπ.
 */
function trig(v, bits, phase) {
  if (gt(v.width, rat(7))) return new Iv(rat(-1), ONE);
  const at = (q) => (phase === 0 ? sinCosPoint(q, bits).sin : sinCosPoint(q, bits).cos);
  const a = at(v.lo);
  if (v.isPoint) return a;
  const b = at(v.hi);
  let lo = min(a.lo, b.lo);
  let hi = max(a.hi, b.hi);
  const pi = piIv(bits);
  const off = phase === 0 ? pi.scale(HALF) : Iv.point(ZERO);
  // k with off + kπ possibly in [v.lo, v.hi]
  const k0 = Math.floor((v.lo.toNumber() - off.mid.toNumber()) / Math.PI) - 1;
  const k1 = Math.ceil((v.hi.toNumber() - off.mid.toNumber()) / Math.PI) + 1;
  for (let k = k0; k <= k1; k++) {
    const p = off.add(pi.scale(new Rational(BigInt(k))));
    if (lt(v.hi, p.lo) || gt(v.lo, p.hi)) continue;
    // sin(π/2 + kπ) = cos(kπ) = (−1)^k
    if (k % 2 === 0) hi = ONE;
    else lo = rat(-1);
  }
  return new Iv(max(lo, rat(-1)), min(hi, ONE));
}

const FNS = {
  exp: (v, b) => monotone(expPoint, v, b),
  log(v, b) {
    if (le(v.lo, ZERO)) refuse("domain", `log needs positive arguments, got ${v}`);
    return monotone(logPoint, v, b);
  },
  sqrt(v, b) {
    if (lt(v.lo, ZERO)) refuse("domain", `sqrt needs non-negative arguments, got ${v}`);
    return monotone(sqrtPoint, v, b);
  },
  atan: (v, b) => monotone(atanPoint, v, b),
  sin: (v, b) => trig(v, b, 0),
  cos: (v, b) => trig(v, b, 1),
  tan(v, b) {
    const c = trig(v, b + 8, 1);
    if (c.containsZero()) refuse("division-by-zero", `tan has a pole in ${v}`);
    return trig(v, b + 8, 0).div(c);
  },
  log1p: (v, b) => FNS.log(v.add(ONE), b),
  sinh(v, b) {
    const f = (q) => {
      const e = expPoint(q, b + 8);
      return e.sub(e.recip()).scale(HALF);
    };
    return monotone(f, v, b);
  },
  cosh(v, b) {
    const f = (q) => {
      const e = expPoint(q, b + 8);
      return e.add(e.recip()).scale(HALF);
    };
    const r = f(v.lo).hull(f(v.hi));
    return v.containsZero() ? new Iv(ONE, r.hi) : r;
  },
  tanh(v, b) {
    const f = (q) => {
      const e = expPoint(q.multiply(TWO), b + 8);
      return e.sub(ONE).div(e.add(ONE));
    };
    return monotone(f, v, b);
  },
  abs(v) {
    if (ge(v.lo, ZERO)) return v;
    if (le(v.hi, ZERO)) return v.neg();
    return new Iv(ZERO, v.mag);
  },
};

/** Enclosure of the tree over env (names → Iv) at about `bits` bits. */
export function encloseAst(ast, env, bits = 64) {
  const go = (n) => {
    switch (n.type) {
      case "num":
        return Iv.point(n.value);
      case "const":
        return n.name === "pi" ? piIv(bits) : expPoint(ONE, bits);
      case "var": {
        const val = env[n.name];
        if (val === undefined) refuse("unbound", `no value for ${n.name}`);
        return val;
      }
      case "op": {
        if (n.op === "^") return power(n);
        const [a, b] = n.args.map(go);
        switch (n.op) {
          case "+": return R(a.add(b), bits);
          case "-": return R(a.sub(b), bits);
          case "*": return R(a.mul(b), bits);
          case "/": return R(a.div(b), bits);
          case "neg": return a.neg();
        }
        break;
      }
      case "call": {
        const args = n.args.map(go);
        if (n.name === "min") return new Iv(min(args[0].lo, args[1].lo), min(args[0].hi, args[1].hi));
        if (n.name === "max") return new Iv(max(args[0].lo, args[1].lo), max(args[0].hi, args[1].hi));
        const f = FNS[n.name === "ln" ? "log" : n.name];
        if (f) return R(f(args[0], bits), bits);
        break;
      }
    }
    return refuse("bad-expression", `cannot enclose ${n.type} ${n.op ?? n.name ?? ""}`);
  };
  const power = (n) => {
    const a = go(n.args[0]);
    const q = constantRational(n.args[1]);
    if (q !== null && q.denominator === 1n) {
      const k = Number(q.numerator);
      if (k === 0) {
        if (a.containsZero()) refuse("zero-power", "0^0 is undefined");
        return Iv.point(ONE);
      }
      return R(k > 0 ? a.pow(k) : a.pow(-k).recip(), bits);
    }
    if (q !== null && q.denominator === 2n && q.numerator === 1n) return R(FNS.sqrt(a, bits), bits);
    return R(FNS.exp(go(n.args[1]).mul(FNS.log(a, bits)), bits), bits);
  };
  return go(ast);
}
