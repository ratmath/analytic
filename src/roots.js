// Certified zeros, poles, holes, extrema and inflection points of a function
// of one variable on [a, b], for graphics and the calculator.
//
// Two engines:
//
// * Rational functions with rational coefficients (no pi, e, sin, ...) are
//   read into N/D exactly. Common factors G = gcd(N, D) become holes; the
//   square-free (Yun) factors of N/G, G and D/G give multiplicities; one
//   Sturm sequence isolates every root, and brackets are narrowed by exact sign
//   tests at the simplest rational in the middle half (so rational roots come
//   out exactly). Every result is proven and unique in its bracket.
//
// * Everything else: interval bisection with a Krawczyk test
//       K = m − Y f(m) + (1 − Y F′(X)) (X − m),   Y ≈ 1/f′(m)
//   K ∩ X = ∅ proves no zero in X; K ⊂ int X proves exactly one, and
//   iterating X ← K ∩ X narrows it quadratically. Where f′ may vanish (a
//   multiple or clustered root), the bracket is reported as "possible" with
//   `atMost: m` when the m-th derivative is proven nonzero on it (Rolle: at
//   most m zeros counted with multiplicity), or as "sign-change" when the
//   end values have proven opposite signs.
//
// Result records (lo, hi are Rationals; `at` is set for exact points):
//   zeros:       { kind: "exact" | "sign-change" | "possible" | "undefined", at?, lo, hi,
//                  unique?, multiplicity?, atMost? }
//   poles:       { kind: "pole" | "hole" | "undefined", at?, lo, hi, order?, value? }
//   extrema:     { kind: "max" | "min" | "flat" | "possible", at?, lo, hi, value, unique? }
//   inflections: { kind: "inflection" | "possible", at?, lo, hi, value, unique? }
// `value` is a RationalInterval enclosing f there (a point when exact).
import { Rational, RationalInterval } from "@ratmath/core";
import { Refinement } from "./refine.js";
import { Iv } from "./interval.js";
import { AnalyticError } from "./errors.js";
import { ZERO, ONE, TWO, lt, le, gt, ge, isZero, sign, min, max, roundDyadic, bitLen, toQ } from "./rat.js";
import { fn, evalParams } from "./fn.js";
import { derivative as dAst, compileFloat, floatEnv, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import * as RP from "./rpoly.js";
import { hornerBound } from "./poly.js";

const q = (v) => (v instanceof Rational ? v : toRational(typeof v === "object" && v.toString ? v.toString() : v));
const FOUR = new Rational(4n);

/** The rational with the smallest denominator in [lo, hi] (Stern–Brocot descent). */
export function simplestBetween(lo, hi) {
  lo = toQ(lo);
  hi = toQ(hi);
  if (gt(lo, hi)) [lo, hi] = [hi, lo];
  if (lo.numerator <= 0n && hi.numerator >= 0n) return ZERO;
  if (hi.numerator < 0n) return simplestBetween(hi.negate(), lo.negate()).negate();
  const go = (p, qq, r, s) => {
    const a = p / qq;
    if (a * qq === p) return [a, 1n];
    if ((a + 1n) * s <= r) return [a + 1n, 1n];
    const [n, d] = go(s, r - a * s, qq, p - a * qq);
    return [a * n + d, n];
  };
  const [n, d] = go(lo.numerator, lo.denominator, hi.numerator, hi.denominator);
  return new Rational(n, d);
}

const middle = (lo, hi) => {
  const w = hi.subtract(lo).divide(FOUR);
  return simplestBetween(lo.add(w), hi.subtract(w));
};
const ri = (iv) => iv.toRationalInterval();
const record = (r) => Object.freeze(r);

function setup(f, interval, opts) {
  const F = fn(f, { variable: opts.variable, params: opts.params });
  const [a, b] = Array.isArray(interval) ? interval.map(q) : [Iv.from(interval).lo, Iv.from(interval).hi];
  const tol = q(opts.tolerance ?? "1/1000000");
  const params = evalParams(F.params);
  const exactParams = Object.values(params).every((v) => v instanceof Rational);
  const rf = exactParams ? RP.rationalFunction(F.ast, F.variable, params) : null;
  const bits = Math.max(64, bitLen(tol.denominator) - bitLen(tol.numerator) + 40);
  const env = {};
  for (const [k, v] of Object.entries(params)) env[k] = Iv.from(v);
  return { F, a, b, tol, rf, bits, env, opts };
}

// ---------------------------------------------------------------------------
// Rational-function engine

function rfDerivative({ num, den }) {
  return {
    num: RP.sub(RP.mul(RP.derivative(num), den), RP.mul(num, RP.derivative(den))),
    den: RP.mul(den, den),
  };
}

function reduce({ num, den }) {
  const G = RP.gcd(num, den);
  const Nr = RP.divmod(num, G).quo;
  const Dr = RP.divmod(den, G).quo;
  return { G, Nr, Dr };
}

const signAt = (p, x) => sign(RP.evaluate(p, x));
const rfSign = (rf, x) => signAt(rf.num, x) * signAt(rf.den, x);

/**
 * Isolate every real root in [a, b] of the tagged square-free factors.
 * Returns { at?, lo, hi, tags: Map(tag → multiplicity) } with every factor
 * nonzero at lo and hi (when lo < hi) and exactly one root in between.
 */
function isolate(tagged, a, b, tol, tick) {
  let P = [ONE];
  for (const t of tagged) P = RP.mul(P, t.factor);
  if (RP.deg(P) < 1) return [];
  const S = RP.divmod(P, RP.gcd(P, RP.derivative(P))).quo;
  const seq = RP.sturm(S);
  const val = (x) => RP.evaluate(S, x);
  const open = (lo, hi) => RP.sturmCount(seq, lo, hi) - (isZero(val(hi)) ? 1 : 0);
  const out = [];
  const exactAt = (r) => {
    // isolating neighbourhood of an exact root
    let w = ONE;
    let lo = r.subtract(w);
    while (isZero(val(lo)) || open(lo, r) > 0) lo = r.subtract((w = w.divide(TWO)));
    w = ONE;
    let hi = r.add(w);
    while (isZero(val(hi)) || open(r, hi) > 0) hi = r.add((w = w.divide(TWO)));
    out.push({ at: r, lo, hi });
  };
  const inward = (lo, hi, fromLow) => {
    // move a zero endpoint inward, keeping the single root inside
    let w = hi.subtract(lo).divide(TWO);
    for (;;) {
      const c = fromLow ? lo.add(w) : hi.subtract(w);
      if (!isZero(val(c)) && (fromLow ? open(c, hi) : open(lo, c)) === 1) return c;
      w = w.divide(TWO);
    }
  };
  const narrow = (lo, hi) => {
    if (isZero(val(lo))) lo = inward(lo, hi, true);
    if (isZero(val(hi))) hi = inward(lo, hi, false);
    while (gt(hi.subtract(lo), tol)) {
      const m = middle(lo, hi);
      const s = sign(val(m));
      if (s === 0) return exactAt(m);
      if (s === sign(val(lo))) lo = m;
      else hi = m;
    }
    out.push({ lo, hi });
  };
  const solve = (lo, hi) => {
    const c = open(lo, hi);
    if (c === 0) return;
    if (c === 1) return narrow(lo, hi);
    const m = middle(lo, hi);
    if (isZero(val(m))) exactAt(m);
    solve(lo, m);
    solve(m, hi);
    tick?.();
  };
  if (isZero(val(a))) exactAt(a);
  if (gt(b, a)) {
    solve(a, b);
    if (isZero(val(b))) exactAt(b);
  }
  out.sort((x, y) => x.lo.compareTo(y.lo));
  for (const r of out) {
    r.tags = new Map();
    for (const t of tagged) {
      const hit = r.at ? isZero(RP.evaluate(t.factor, r.at)) : signAt(t.factor, r.lo) !== signAt(t.factor, r.hi);
      if (hit) r.tags.set(t.tag, Math.max(r.tags.get(t.tag) ?? 0, t.multiplicity));
    }
  }
  return out;
}

function rationalFeatures(rf, a, b, tol, tick) {
  const { G, Nr, Dr } = reduce(rf);
  const tagged = [
    ...RP.squareFree(Nr).map((f) => ({ ...f, tag: "zero" })),
    ...RP.squareFree(G).map((f) => ({ ...f, tag: "hole" })),
    ...RP.squareFree(Dr).map((f) => ({ ...f, tag: "pole" })),
  ];
  return { roots: isolate(tagged, a, b, tol, tick), Nr, Dr };
}

/** Enclosure of Nr/Dr at a root record (exact at points). */
function rfValue(Nr, Dr, r) {
  if (r.at) return Iv.point(RP.evaluate(Nr, r.at).divide(RP.evaluate(Dr, r.at)));
  const X = new Iv(r.lo, r.hi);
  return hornerBound(Nr, X).div(hornerBound(Dr, X));
}

function placeOf(r) {
  return r.at ? { at: r.at, lo: r.at, hi: r.at } : { lo: r.lo, hi: r.hi };
}

function* rationalZeros(s) {
  const { roots } = rationalFeatures(s.rf, s.a, s.b, s.tol);
  yield { done: 1, of: 1, step: "isolated" };
  const out = [];
  for (const r of roots) {
    if (r.tags.has("pole") || r.tags.has("hole") || !r.tags.has("zero")) continue;
    out.push(record({ kind: r.at ? "exact" : "sign-change", ...placeOf(r), unique: true, multiplicity: r.tags.get("zero") }));
  }
  return { value: out, via: "exact Sturm isolation of square-free factors" };
}

function* rationalPoles(s) {
  const { roots, Nr, Dr } = rationalFeatures(s.rf, s.a, s.b, s.tol);
  yield { done: 1, of: 1, step: "isolated" };
  const out = [];
  for (const r of roots) {
    if (r.tags.has("pole")) out.push(record({ kind: "pole", ...placeOf(r), order: r.tags.get("pole"), unique: true }));
    else if (r.tags.has("hole")) out.push(record({ kind: "hole", ...placeOf(r), value: ri(rfValue(Nr, Dr, r)), unique: true }));
  }
  return { value: out, via: "exact Sturm isolation of square-free factors" };
}

/** Zeros of the k-th derivative, classified by its sign on either side. */
function* rationalCritical(s, kind) {
  let d = s.rf;
  const k = kind === "extrema" ? 1 : 2;
  for (let i = 0; i < k; i++) d = rfDerivative(d);
  const base = reduce(s.rf);
  const { roots } = rationalFeatures(d, s.a, s.b, s.tol);
  yield { done: 1, of: 1, step: "isolated" };
  const out = [];
  for (const r of roots) {
    if (!r.tags.has("zero") || r.tags.has("pole") || r.tags.has("hole")) continue;
    // f itself must be defined there (its poles and holes are poles/holes of d)
    const left = rfSign(d, r.lo);
    const right = rfSign(d, r.hi);
    const value = ri(rfValue(base.Nr, base.Dr, r));
    if (kind === "extrema") {
      const k2 = left > 0 && right < 0 ? "max" : left < 0 && right > 0 ? "min" : "flat";
      out.push(record({ kind: k2, ...placeOf(r), value, unique: true }));
    } else if (left !== right) {
      out.push(record({ kind: "inflection", ...placeOf(r), value, unique: true }));
    }
  }
  return { value: out, via: "exact Sturm isolation of the derivative's numerator" };
}

// ---------------------------------------------------------------------------
// General engine: interval bisection + Krawczyk

function makeEval(ast, s) {
  const bits = s.bits;
  return (X) => encloseAst(ast, { ...s.env, [s.F.variable]: X }, bits);
}

function safe(fnc, X) {
  try {
    return fnc(X);
  } catch (e) {
    if (e instanceof AnalyticError) return null;
    throw e;
  }
}

/**
 * Zeros of the tree `ast` (with derivative trees ds = [f′, f″, ...]) on [a, b].
 * Each result also carries sLo, sHi: proven signs of f at lo and hi (0 = unknown).
 */
function* generalZeros(ast, s, { pieces = 16, maxDepth = 48, maxMultiplicity = 4 } = {}) {
  const f = makeEval(ast, s);
  const ds = [];
  let cur = ast;
  for (let i = 0; i < maxMultiplicity; i++) {
    try {
      cur = dAst(cur, s.F.variable);
    } catch (e) {
      if (!(e instanceof AnalyticError)) throw e;
      break;
    }
    ds.push(makeEval(cur, s));
  }
  const df = ds[0];
  const out = [];
  const seen = new Set();
  const pointSign = (x) => {
    const y = safe(f, Iv.point(x));
    if (!y) return NaN;
    if (y.isPoint && isZero(y.lo)) return 0;
    return gt(y.lo, ZERO) ? 1 : lt(y.hi, ZERO) ? -1 : null; // null: unknown
  };
  const addExact = (x) => {
    const k = x.toString();
    if (seen.has(k)) return;
    seen.add(k);
    out.push({ kind: "exact", at: x, lo: x, hi: x, unique: true });
  };
  const atMost = (X) => {
    for (let m = 1; m <= ds.length; m++) {
      const y = safe(ds[m - 1], X);
      if (y && !y.containsZero()) return m;
    }
    return undefined;
  };
  const finish = (X, sLo, sHi) => {
    const change = sLo !== null && sHi !== null && !Number.isNaN(sLo) && !Number.isNaN(sHi) && sLo * sHi < 0;
    const m = atMost(X);
    const rec = { kind: change ? "sign-change" : "possible", lo: X.lo, hi: X.hi, sLo, sHi };
    if (m !== undefined) rec.atMost = m;
    if (change && m === 1) rec.unique = true;
    out.push(rec);
  };
  // Krawczyk iteration on X with f′ ≠ 0: returns "none", a narrowed unique Iv, or null (undecided)
  const krawczyk = (X) => {
    let unique = false;
    for (let it = 0; it < 60; it++) {
      const m = X.isPoint ? X.lo : middle(X.lo, X.hi);
      const fm = safe(f, Iv.point(m));
      const dX = df ? safe(df, X) : null;
      if (!fm || !dX || dX.containsZero()) return unique ? X : null;
      if (fm.isPoint && isZero(fm.lo)) return { exact: m };
      const Y = roundDyadic(ONE.divide(dX.mid), s.bits);
      const K = Iv.point(m).sub(fm.scale(Y)).add(Iv.point(ONE).sub(dX.scale(Y)).mul(X.sub(m))).roundOut(s.bits + 16);
      const N = K.intersect(X);
      if (!N) return unique ? X : "none";
      if (lt(X.lo, K.lo) && lt(K.hi, X.hi)) unique = true;
      if (unique && le(N.width, s.tol)) return N;
      if (!unique && ge(N.width.multiply(TWO), X.width)) return null; // not contracting yet: bisect
      X = N;
    }
    return unique ? X : null;
  };
  const work = (lo, hi, depth) => {
    const X = new Iv(lo, hi);
    const y = safe(f, X);
    const width = hi.subtract(lo);
    if (y === null) {
      // f fails somewhere on X. Keep splitting only where it can be evaluated
      // at some point; otherwise report the bracket as undefined (no claim).
      const anyPoint = [lo, middle(lo, hi), hi].some((x) => safe(f, Iv.point(x)) !== null);
      if (!anyPoint || le(width, s.tol) || depth >= maxDepth) out.push({ kind: "undefined", lo, hi });
      else split(lo, hi, depth);
      return;
    }
    if (!y.containsZero()) return;
    const k = krawczyk(X);
    if (k === "none") return;
    if (k && k.exact) {
      addExact(k.exact);
      work(lo, k.exact, depth + 1);
      work(k.exact, hi, depth + 1);
      return;
    }
    if (k) {
      const sl = pointSign(k.lo);
      const sh = pointSign(k.hi);
      if (sl === 0) addExact(k.lo);
      else if (sh === 0) addExact(k.hi);
      else out.push({ kind: "sign-change", lo: k.lo, hi: k.hi, unique: true, atMost: 1, sLo: sl, sHi: sh });
      return;
    }
    if (le(width, s.tol) || depth >= maxDepth) return finish(X, pointSign(lo), pointSign(hi));
    split(lo, hi, depth);
  };
  const split = (lo, hi, depth) => {
    const m = middle(lo, hi);
    if (pointSign(m) === 0) addExact(m);
    work(lo, m, depth + 1);
    work(m, hi, depth + 1);
  };
  const { a, b } = s;
  if (pointSign(a) === 0) addExact(a);
  if (pointSign(b) === 0) addExact(b);
  const step = b.subtract(a).divide(new Rational(BigInt(pieces)));
  for (let i = 0; i < pieces; i++) {
    const lo = a.add(step.multiply(new Rational(BigInt(i))));
    const hi = i === pieces - 1 ? b : lo.add(step);
    if (i < pieces - 1 && pointSign(hi) === 0) addExact(hi);
    if (gt(hi, lo)) work(lo, hi, 0);
    yield { done: i + 1, of: pieces, step: "piece", partial: out.map(clean) };
  }
  return absorbNearExact(mergeAdjacent(out, atMost), ds, atMost, s);
}

/**
 * At an exact zero r, f^(j)(r) = 0 exactly for j < k gives multiplicity ≥ k.
 * If some derivative of order m ≤ k is nonzero on a bracket touching r, Rolle
 * allows at most m zeros there with multiplicity, all used up by r: the
 * bracket holds no other zero and r's multiplicity is exactly k.
 */
function absorbNearExact(list, ds, atMost, s) {
  const exact = list.filter((r) => r.kind === "exact");
  const drop = new Set();
  for (const r of exact) {
    let k = 1;
    for (const d of ds) {
      const y = safe(d, Iv.point(r.at));
      if (y && y.isPoint && isZero(y.lo)) k++;
      else break;
    }
    const near = new Iv(r.at.subtract(s.tol), r.at.add(s.tol));
    const m = atMost(near);
    if (m !== undefined && m <= k) r.multiplicity = k;
    for (const o of list) {
      if (o.kind !== "possible") continue;
      if (o.lo.compareTo(r.at) !== 0 && o.hi.compareTo(r.at) !== 0) continue;
      const hull = new Iv(min(o.lo, r.at), max(o.hi, r.at));
      const mm = atMost(hull);
      if (mm !== undefined && mm <= k) {
        drop.add(o);
        r.multiplicity = k;
      }
    }
  }
  return list.filter((r) => !drop.has(r));
}

/** Sort, and merge touching "possible" or "undefined" brackets. */
function mergeAdjacent(list, atMost) {
  list.sort((x, y) => x.lo.compareTo(y.lo) || x.hi.compareTo(y.hi));
  const out = [];
  for (const r of list) {
    const last = out.at(-1);
    if (last && last.kind === r.kind && (r.kind === "possible" || r.kind === "undefined") && last.hi.compareTo(r.lo) === 0) {
      last.hi = r.hi;
      last.sHi = r.sHi;
      if (r.kind === "possible") {
        const m = atMost(new Iv(last.lo, last.hi));
        if (m === undefined) delete last.atMost;
        else last.atMost = m;
      }
      continue;
    }
    out.push({ ...r });
  }
  return out;
}

function clean(r) {
  const { sLo, sHi, ...rest } = r;
  return record(rest);
}

function* generalZerosStage(s) {
  const list = yield* generalZeros(s.F.ast, s, s.opts);
  return { value: list.map(clean), via: "interval bisection with Krawczyk uniqueness tests" };
}

function* generalCritical(s, kind) {
  const k = kind === "extrema" ? 1 : 2;
  let ast = s.F.ast;
  for (let i = 0; i < k; i++) ast = dAst(ast, s.F.variable);
  const next = makeEval(dAst(ast, s.F.variable), s); // f″ for extrema, f‴ for inflections
  const f0 = makeEval(s.F.ast, s);
  const list = yield* generalZeros(ast, s, s.opts);
  const out = [];
  for (const r of list) {
    if (r.kind === "undefined") continue;
    const X = new Iv(r.lo, r.hi);
    const v = safe(f0, X);
    if (!v) continue;
    const nx = safe(next, X);
    const proven = r.kind === "exact" || r.kind === "sign-change";
    let label = "possible";
    let unique = false;
    if (proven && nx && !nx.containsZero()) {
      label = kind === "extrema" ? (gt(nx.lo, ZERO) ? "min" : "max") : "inflection";
      unique = true;
    } else if (r.kind === "sign-change" && r.sLo && r.sHi) {
      label = kind === "extrema" ? (r.sLo > 0 ? "max" : "min") : "inflection";
      unique = !!r.unique;
    }
    out.push(record({ kind: label, ...(r.at ? { at: r.at } : {}), lo: r.lo, hi: r.hi, value: ri(v), unique }));
  }
  return { value: out, via: `zeros of f${kind === "extrema" ? "′" : "″"} by Krawczyk, classified by f${kind === "extrema" ? "″" : "‴"} or sign changes` };
}

/** Denominator subtrees (where f can blow up), paired with their numerators. */
function denominators(ast, out = []) {
  if (ast.type === "op" && ast.op === "/") out.push({ num: ast.args[0], den: ast.args[1] });
  if (ast.type === "op" && ast.op === "^") {
    const e = ast.args[1];
    if (e.type === "op" && e.op === "neg") out.push({ num: { type: "num", value: ONE }, den: ast.args[0] });
  }
  if (ast.type === "call" && ast.name === "tan") {
    out.push({ num: { type: "call", name: "sin", args: ast.args }, den: { type: "call", name: "cos", args: ast.args } });
  }
  for (const a of ast.args ?? []) denominators(a, out);
  return out;
}

function* generalPoles(s) {
  const out = [];
  const pairs = denominators(s.F.ast);
  let i = 0;
  for (const { num, den } of pairs) {
    const list = yield* generalZeros(den, s, { ...s.opts, maxMultiplicity: 2 });
    const numEval = makeEval(num, s);
    for (const r of list) {
      if (r.kind !== "exact" && r.kind !== "sign-change") continue;
      const nv = safe(numEval, new Iv(r.lo, r.hi));
      const where = r.at ? { at: r.at, lo: r.at, hi: r.at } : { lo: r.lo, hi: r.hi };
      if (nv && !nv.containsZero()) out.push(record({ kind: "pole", ...where, unique: !!r.unique }));
      else out.push(record({ kind: "undefined", ...where }));
    }
    yield { done: ++i, of: pairs.length, step: "denominator" };
  }
  out.sort((x, y) => x.lo.compareTo(y.lo));
  return { value: out, via: "zeros of denominators with numerators proven nonzero" };
}

// ---------------------------------------------------------------------------
// Public API: each returns a Refinement

function quickZeros(F, a, b, n = 512) {
  const g = compileFloat(F.ast);
  const env = floatEnv(F.params);
  const at = (x) => {
    env[F.variable] = x;
    return g(env);
  };
  const A = a.toNumber();
  const B = b.toNumber();
  const out = [];
  let x0 = A;
  let y0 = at(A);
  if (y0 === 0) out.push({ kind: "guess", at: A });
  for (let i = 1; i <= n; i++) {
    const x1 = A + ((B - A) * i) / n;
    const y1 = at(x1);
    if (y1 === 0) out.push({ kind: "guess", at: x1 });
    else if (Number.isFinite(y0) && Number.isFinite(y1) && y0 * y1 < 0) {
      let lo = x0;
      let hi = x1;
      let ylo = y0;
      for (let k = 0; k < 60; k++) {
        const m = (lo + hi) / 2;
        const ym = at(m);
        if (ym === 0 || m === lo || m === hi) {
          lo = hi = m;
          break;
        }
        if (Math.sign(ym) === Math.sign(ylo)) [lo, ylo] = [m, ym];
        else hi = m;
      }
      // a sign change with huge values is probably a pole
      const mid = (lo + hi) / 2;
      if (Math.abs(at(mid)) < 1e6) out.push({ kind: "guess", at: mid });
    }
    x0 = x1;
    y0 = y1;
  }
  return { value: out, trust: "rough" };
}

function quickCritical(F, a, b, k) {
  let d = F;
  for (let i = 0; i < k; i++) d = d.derivative();
  const z = quickZeros(d, a, b).value;
  return { value: z.map((g) => ({ kind: "guess", at: g.at, value: F.float(g.at) })), trust: "rough" };
}

/** zeros(f, [a, b], { variable, params, tolerance = 1e-6, pieces, maxDepth }) */
export function zeros(f, interval, opts = {}) {
  const s = setup(f, interval, opts);
  return new Refinement(() => quickZeros(s.F, s.a, s.b), () => (s.rf ? rationalZeros(s) : generalZerosStage(s)));
}

/** poles(f, [a, b], opts): poles, holes (removable points) and undefined points. */
export function poles(f, interval, opts = {}) {
  const s = setup(f, interval, opts);
  return new Refinement(
    () => ({ value: [], trust: "unsure" }),
    () => (s.rf ? rationalPoles(s) : generalPoles(s)),
  );
}

/** extrema(f, [a, b], opts): interior critical points of f, classified. */
export function extrema(f, interval, opts = {}) {
  const s = setup(f, interval, opts);
  return new Refinement(() => quickCritical(s.F, s.a, s.b, 1), () => (s.rf ? rationalCritical(s, "extrema") : generalCritical(s, "extrema")));
}

/** inflections(f, [a, b], opts): points where f″ changes sign. */
export function inflections(f, interval, opts = {}) {
  const s = setup(f, interval, opts);
  return new Refinement(() => quickCritical(s.F, s.a, s.b, 2), () => (s.rf ? rationalCritical(s, "inflections") : generalCritical(s, "inflections")));
}

export { RationalInterval };
