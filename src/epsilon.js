// A δ for a given ε, with its proof.
//
// For f continuous near x₀ and ε > 0, deltaFor finds a δ with
// |f(x) − f(x₀)| < ε whenever |x − x₀| < δ, and the largest such δ where it can
// be pinned down: by the intermediate value theorem that is the distance from
// x₀ to the nearest solution of f(x) = f(x₀) ± ε, and the certified root
// finder lists every solution in a window around x₀.
import { Rational, RationalInterval } from "@ratmath/core";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, lt, le, gt, ge, toQ } from "./rat.js";
import { toAst, format, derivative, simplify, constantRational, num, op, toRational } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { zeros } from "./roots.js";
import { AnalyticFunction } from "./fn.js";
import { verifySequenceCertificate } from "./sequences.js";

const q = (x) => (x instanceof Rational ? x : typeof x === "string" || (typeof x === "number" && !Number.isInteger(x)) ? toRational(String(x)) : toQ(x));
const BITS = 160;
const soft = (f, fallback = null) => {
  try {
    return f();
  } catch (e) {
    if (e instanceof AnalyticError) return fallback;
    throw e;
  }
};
const tidy = (iv) => (iv.isPoint ? iv.lo : iv.toRationalInterval());

function setup(f, x0, variable) {
  const ast = f instanceof AnalyticFunction ? f.ast : toAst(f);
  const x = f instanceof AnalyticFunction ? f.variable : variable;
  const a = q(x0);
  const at = (p) => {
    const exact = constantRational(ast, { [x]: p });
    return exact !== null ? Iv.point(exact) : encloseAst(ast, { [x]: Iv.point(p) }, BITS);
  };
  const fa = at(a);
  return { ast, x, a, at, fa, dAst: simplify(derivative(ast, x)) };
}

/**
 * sup of |f(x) − f(a)| for |x − a| ≤ δ, as an interval that holds it. Where
 * f′ keeps one sign on each side of a the sup is at an end and the interval
 * is as tight as the end values (a point for exact ones); otherwise it runs
 * from the larger end value to the mean value bound sup|f′|·δ.
 */
function supWithin(s, delta) {
  const { ast, x, a, at, fa, dAst } = s;
  const [l, r] = [a.subtract(delta), a.add(delta)];
  const ends = [at(l).sub(fa), at(r).sub(fa)];
  const endSup = new Iv(ends[0].mig.compareTo(ends[1].mig) > 0 ? ends[0].mig : ends[1].mig, ends[0].mag.compareTo(ends[1].mag) > 0 ? ends[0].mag : ends[1].mag);
  const oneSign = (lo, hi) => {
    const d = soft(() => encloseAst(dAst, { [x]: new Iv(lo, hi) }, BITS));
    return d !== null && (ge(d.lo, ZERO) || le(d.hi, ZERO));
  };
  if (oneSign(l, a) && oneSign(a, r)) return { sup: endSup, monotoneSides: true };
  // two upper bounds: the range of f over the interval, and the mean value bound sup|f′|·δ
  const range = encloseAst(ast, { [x]: new Iv(l, r) }, BITS).sub(fa).mag; // throws where f is not defined throughout
  const d = soft(() => encloseAst(dAst, { [x]: new Iv(l, r) }, BITS));
  const mean = d ? d.mag.multiply(delta) : null;
  return { sup: new Iv(endSup.lo, mean !== null && lt(mean, range) ? mean : range), monotoneSides: false };
}

/** The nearest solution of f(x) = f(a) + shift to a, within [a − W, a + W]: { distance, proven } or null when none. */
function nearest(s, shift, W) {
  const g = simplify(op("-", s.ast, num(shift)));
  const list = zeros(g, [s.a.subtract(W), s.a.add(W)], { variable: s.x }).exact();
  let best = null;
  for (const z of list) {
    if (z.kind === "everywhere") return { distance: Iv.point(ZERO), proven: true };
    let lo = z.at ?? z.lo;
    let hi = z.at ?? z.hi;
    const proven = z.kind === "exact" || z.kind === "sign-change" || z.unique === true;
    if (proven && !z.at && !lo.equals(hi)) {
      // one simple root in the bracket: narrow it by the sign of g at midpoints
      const sg = (p) => {
        const v = soft(() => encloseAst(g, { [s.x]: Iv.point(p) }, BITS));
        return v === null ? 0 : gt(v.lo, ZERO) ? 1 : lt(v.hi, ZERO) ? -1 : v.isPoint ? 2 : 0;
      };
      const sLo = sg(lo);
      if (sLo === 1 || sLo === -1) {
        for (let i = 0; i < 70; i++) {
          const m = lo.add(hi).divide(TWO);
          const sm = sg(m);
          if (sm === 2) {
            lo = hi = m;
            break;
          }
          if (sm === 0) break;
          if (sm === sLo) lo = m;
          else hi = m;
        }
      }
    }
    // distance from a to the bracket [lo, hi]
    const dLo = le(lo, s.a) && le(s.a, hi) ? ZERO : lt(hi, s.a) ? s.a.subtract(hi) : lo.subtract(s.a);
    const dHi = gt(s.a.subtract(lo).abs(), hi.subtract(s.a).abs()) ? s.a.subtract(lo).abs() : hi.subtract(s.a).abs();
    if (best === null || lt(dLo, best.distance.lo)) best = { distance: new Iv(dLo, dHi), proven };
  }
  return best;
}

/**
 * A δ for ε at x₀.
 *
 *   deltaFor("x^2", 2, "1/100")
 *   // { delta: 249/100000, largest: [0.0024984…, 0.0024984…], … }
 *   deltaFor("x^2", 2, "1/100", { delta: "0.002" })
 *   // { holds: true, worst: 2001/250000 }   the largest |f(x) − f(2)| for |x − 2| ≤ δ
 *
 * Without `delta`: → { delta, largest, attainedAt, reason, certificate }.
 * `delta` is a rational that works; `largest` is the supremum of the δ that
 * work (a Rational when the nearest solution of f(x) = f(x₀) ± ε is
 * rational, else a RationalInterval that encloses it; null when it was not
 * pinned down), and then `delta` is `largest` itself when that is rational,
 * else `largest` rounded down to three significant digits.
 *
 * With `delta`: → { holds, worst, reason } for that δ; `holds` is true or
 * false when proven, null when the enclosure of the worst case straddles ε.
 */
export function deltaFor(f, x0, eps, { variable = "x", delta } = {}) {
  const e = q(eps);
  if (e.numerator <= 0n) refuse("bad-argument", "ε must be positive");
  const s = setup(f, x0, variable);
  const text = `|${format(s.ast)} − f(${s.a})|`;
  if (delta !== undefined) {
    const d = q(delta);
    if (d.numerator <= 0n) refuse("bad-argument", "δ must be positive");
    const { sup, monotoneSides } = supWithin(s, d);
    // on monotone sides the sup over |x − a| ≤ δ is reached only at the ends, so equality with ε still works for |x − a| < δ
    const holds = lt(sup.hi, e) || (monotoneSides && le(sup.hi, e)) ? true : gt(sup.lo, e) ? false : null;
    return {
      delta: d,
      epsilon: e,
      holds,
      worst: tidy(sup),
      reason: monotoneSides
        ? `f is monotone on each side of ${s.a}, so ${text} is largest at an end of [${s.a.subtract(d)}, ${s.a.add(d)}]: ${sup.isPoint ? sup.lo : `about ${sup.hi.toNumber()}`}`
        : `${text} is bounded over the interval by interval arithmetic and the mean value theorem`,
      certificate: holds === true ? deltaCertificate(s, e, d) : null,
    };
  }
  // a δ that works: halve until the worst case is below ε
  let d = ONE;
  let found = null;
  for (let i = 0; i < 300 && !found; i++) {
    const r = soft(() => supWithin(s, d));
    if (r && lt(r.sup.hi, e)) found = r;
    else d = d.divide(TWO);
  }
  if (!found) refuse("undecided", `no δ was found: f may not be continuous at ${s.a}`);
  // the largest: the nearest solution of f = f(a) ± ε. f(a) must be exact to write the equation exactly.
  let largest = null;
  let attainedAt = null;
  if (s.fa.isPoint) {
    let W = d.multiply(TWO);
    for (let i = 0; i < 40 && largest === null; i++, W = W.multiply(TWO)) {
      const near = soft(() => [nearest(s, s.fa.lo.add(e), W), nearest(s, s.fa.lo.subtract(e), W)]);
      if (near === null) break; // the window left the domain of f
      const cands = near.filter(Boolean);
      if (!cands.length) continue;
      cands.sort((u, w) => u.distance.lo.compareTo(w.distance.lo));
      const first = cands[0];
      // the other equation's nearest solution must be provably no nearer
      if (first.proven && cands.every((c) => c === first || ge(c.distance.lo, first.distance.hi) || c.distance.lo.equals(first.distance.lo))) {
        largest = first.distance;
        attainedAt = first === near[0] ? "f(x) = f(x₀) + ε" : "f(x) = f(x₀) − ε";
      } else if (gt(first.distance.lo, d)) d = first.distance.lo; // still a δ that works
      break;
    }
  }
  let best = d;
  if (largest) {
    if (largest.isPoint) best = largest.lo;
    else {
      // three significant digits, rounded down
      const digits = BigInt(Math.max(0, 2 - Math.floor(Math.log10(largest.lo.toNumber()))));
      const scale = 10n ** digits;
      const down = new Rational(largest.lo.multiply(new Rational(scale)).floor(), scale);
      best = gt(down, d) ? down : d;
    }
  }
  const check = supWithin(s, best);
  return {
    delta: best,
    epsilon: e,
    largest: largest ? tidy(largest) : null,
    attainedAt,
    worst: tidy(check.sup),
    reason: largest
      ? `${text} first reaches ε where ${attainedAt}, at distance ${largest.isPoint ? largest.lo : `about ${largest.lo.toNumber()}`} from ${s.a}; any smaller δ works`
      : `for |x − ${s.a}| ≤ ${best}, ${text} is at most ${check.sup.hi.toNumber().toPrecision(4)} < ε`,
    certificate: deltaCertificate(s, e, best),
  };
}

function deltaCertificate(s, e, d) {
  return Object.freeze({ kind: "δ for ε", claim: `|f(x) − f(x₀)| < ε whenever |x − x₀| < δ`, f: format(s.ast), variable: s.x, x0: s.a, epsilon: e, delta: d });
}

/**
 * Recheck a "δ for ε" certificate by plain interval evaluation: the interval
 * |x − x₀| ≤ δ is cut into cells, and on each the enclosure of f(x) − f(x₀)
 * must lie inside (−ε, ε). A cell that fails is halved; one that still fails
 * when tiny is accepted only if it touches an end of the interval, f is
 * strictly monotone on it, and the end value is at most ε (so the open
 * interval stays strictly inside).
 */
function verifyDeltaCertificate(cert) {
  const s = setup(cert.f, cert.x0, cert.variable);
  const { a, x, ast, dAst, fa, at } = s;
  const [e, d] = [cert.epsilon, cert.delta];
  const checks = [];
  const floor = d.divide(new Rational(1n << 30n));
  let cells = Array.from({ length: 32 }, (_, i) => [a.subtract(d).add(d.multiply(new Rational(BigInt(i), 16n))), a.subtract(d).add(d.multiply(new Rational(BigInt(i + 1), 16n)))]);
  let ok = true;
  let work = 0;
  while (cells.length && ok) {
    const [l, r] = cells.pop();
    if (++work > 20000) {
      ok = false;
      break;
    }
    const v = soft(() => encloseAst(ast, { [x]: new Iv(l, r) }, BITS).sub(fa));
    if (v && lt(v.mag, e)) continue;
    if (gt(r.subtract(l), floor)) {
      const m = l.add(r).divide(TWO);
      cells.push([l, m], [m, r]);
      continue;
    }
    // a tiny cell at an end of the interval
    const atLeft = l.equals(a.subtract(d));
    const atRight = r.equals(a.add(d));
    const dv = soft(() => encloseAst(dAst, { [x]: new Iv(l, r) }, BITS));
    const strict = dv && (gt(dv.lo, ZERO) || lt(dv.hi, ZERO));
    const end = atLeft ? at(l).sub(fa) : atRight ? at(r).sub(fa) : null;
    const inner = atLeft ? at(r).sub(fa) : atRight ? at(l).sub(fa) : null;
    if (!(end && strict && le(end.mag, e) && lt(inner.mag, e))) ok = false;
  }
  checks.push({ check: `|f(x) − f(${a})| < ε on every cell of |x − ${a}| < ${d}`, ok });
  return { valid: ok, checks };
}

/**
 * Recheck a certificate from nFor or deltaFor with a method independent of
 * the search that produced it. → { valid, checks: [{ check, ok }] }.
 */
export function verifyCertificate(cert) {
  if (!cert || typeof cert !== "object") refuse("bad-argument", "verifyCertificate needs the certificate of a result");
  if (cert.kind === "N for ε") return verifySequenceCertificate(cert);
  if (cert.kind === "δ for ε") return verifyDeltaCertificate(cert);
  return refuse("bad-argument", `unknown certificate kind ${cert.kind}`);
}

AnalyticFunction.prototype.deltaFor = function (x0, eps, options) {
  return deltaFor(this, x0, eps, options);
};
