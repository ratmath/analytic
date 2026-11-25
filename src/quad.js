// One-variable integrals by Taylor expansion in fixed point: on a piece with
// centre c and half-width h, f(c + h·s) = Σ_{k<K} a_k·s^k + a_K(ξ)·s^K, so
// ∫ f = h·(Σ_{k even} 2·a_k/(k + 1) ± 2·|a_K|/(K + 1)) with a_K enclosed over
// the whole piece. Pieces wait in a heap and the widest is halved. Used for
// the finite parts of improper integrals and for Fourier coefficients, where
// many integrals of nested formulas are needed quickly.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, le, max } from "./rat.js";
import { compileFloat } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { taylorAlong, share, Heap } from "./multi.js";

/**
 * ∫_a^b ast d(name) as an interval, to an absolute width `tol` (a Rational)
 * where the budget allows. Returns { iv, pieces, met }.
 */
export function quad1(ast, name, env, a, b, { tol, bits = 96, maxPieces = 3000, order } = {}) {
  if (a.equals(b)) return { iv: Iv.point(ZERO), pieces: 0, met: true };
  const tree = share(ast);
  const K = order ?? 14;
  const float = compileFloat(tree);
  const fenv = {};
  for (const [k, val] of Object.entries(env)) fenv[k] = val.mid.toNumber();
  const evenWeights = [];
  for (let k = 0; k < K; k += 2) evenWeights.push(new Rational(2n, BigInt(k + 1)));
  const last = new Rational(2n, BigInt(K + 1));
  const piece = (lo, hi, depth) => {
    const c = lo.add(hi).divide(TWO);
    const h = hi.subtract(lo).divide(TWO);
    // tiny integrands need more absolute bits to keep their digits
    const size = Math.abs(float({ ...fenv, [name]: c.toNumber() }));
    const extra = Number.isFinite(size) && size > 0 && size < 1 ? Math.min(900, Math.ceil(-Math.log2(size))) : 0;
    const B = bits + extra;
    const box = new Iv(lo, hi);
    let plain = null;
    try {
      plain = encloseAst(tree, { ...env, [name]: box }, B).scale(hi.subtract(lo));
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
    }
    let iv = null;
    try {
      const over = taylorAlong(tree, { ...env, [name]: box }, name, B, K, h);
      const at = over && taylorAlong(tree, { ...env, [name]: Iv.point(c) }, name, B, K, h);
      if (over && at) {
        let sum = Iv.point(ZERO);
        for (let k = 0; k < K; k += 2) sum = sum.add(at[k].scale(evenWeights[k / 2]));
        const rest = over[K].mag.multiply(last);
        iv = sum.add(new Iv(rest.negate(), rest)).scale(h);
        if (plain) iv = iv.intersect(plain) ?? iv;
      }
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
    }
    iv ??= plain;
    if (!iv) {
      if (depth >= 60) refuse("not-integrable", `the integrand could not be bounded near ${name} = ${c.toNumber()}`);
      return null;
    }
    return { lo, hi, depth, iv: iv.roundOut(B, 6000), key: iv.width.toNumber() };
  };
  const heap = new Heap();
  let count = 0;
  let width = ZERO;
  const put = (lo, hi, depth) => {
    const p = piece(lo, hi, depth);
    count += 1;
    if (p) {
      width = width.add(p.iv.width);
      return heap.push(p);
    }
    const m = lo.add(hi).divide(TWO);
    put(lo, m, depth + 1);
    put(m, hi, depth + 1);
  };
  const [lo, hi, sign] = le(a, b) ? [a, b, 1] : [b, a, -1];
  put(lo, hi, 0);
  const total = () => heap.items().reduce((acc, p) => acc.add(p.iv), Iv.point(ZERO));
  let met = true;
  while (!le(width, tol)) {
    if (count >= maxPieces) { met = false; break; }
    const p = heap.pop();
    if (p.key === 0 || p.depth >= 200) { heap.push(p); met = false; break; }
    width = width.subtract(p.iv.width);
    const m = p.lo.add(p.hi).divide(TWO);
    put(p.lo, m, p.depth + 1);
    put(m, p.hi, p.depth + 1);
  }
  const sum = total();
  return { iv: sign < 0 ? sum.neg() : sum, pieces: heap.size, met };
}
