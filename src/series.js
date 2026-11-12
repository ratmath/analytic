// Models from user-supplied power series  f(x) = Σ a_k (x − c)^k  on a domain,
// with an explicit rule for the tail after degree p. The rule and whether it
// was proven or assumed are recorded on the model.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { ZERO, ONE, toQ, lt, le, gt, ge, isZero, sign, factorial } from "./rat.js";
import { refuse } from "./errors.js";
import { TaylorModel, Domain, settings } from "./model.js";

/**
 * series(domain, {
 *   coefficient: k => a_k (Rational or anything Core-like), or coefficients: [a_0, a_1, ...]
 *   order: p                       // degree kept (default: the model default)
 *   centre                         // optional, defaults to the domain's centre
 *   rule: "lagrange" | "ratio" | "alternating" | "explicit"
 *   M        (lagrange)            // bound on |f^(p+1)| over the domain — your claim
 *   q        (ratio)               // |a_{k+1}| r ≤ q |a_k| for k > p, with q < 1
 *   error    (explicit)            // interval or bound on the tail — your claim
 *   lookahead (ratio, alternating) // how many tail terms to check (default 32)
 * })
 *
 * "ratio" and "alternating" check their hypothesis on the next `lookahead`
 * terms; beyond that the hypothesis is the caller's claim, and the model is
 * marked assumed unless `proven: true` is passed by code that knows it.
 */
export function series(domain, spec = {}) {
  const D = Domain(domain, spec.centre !== undefined ? { centre: spec.centre } : undefined);
  const { order, bits } = settings(spec);
  const p = spec.degree ?? order;
  const coef = typeof spec.coefficient === "function"
    ? (k) => toQ(spec.coefficient(k))
    : Array.isArray(spec.coefficients)
      ? (k) => (k < spec.coefficients.length ? toQ(spec.coefficients[k]) : ZERO)
      : refuse("bad-series", "series needs coefficient: k => a_k or coefficients: [...]");
  const a = [];
  for (let k = 0; k <= p; k++) a.push(coef(k));
  const r = D.radius;
  const t = D.t;
  const rule = spec.rule ?? (Array.isArray(spec.coefficients) && spec.coefficients.length <= p + 1 ? "exact" : null);
  const look = spec.lookahead ?? 32;
  let rem;
  let assumed = false;
  let note;

  switch (rule) {
    case "exact": {
      rem = Iv.point(ZERO);
      note = "polynomial";
      break;
    }
    case "lagrange": {
      if (spec.M === undefined) refuse("bad-series", "Lagrange rule needs M ≥ max |f^(p+1)| on the domain");
      const M = toQ(spec.M).abs();
      rem = Iv.sym(M.multiply(r.pow(p + 1)).divide(new Rational(factorial(p + 1))));
      assumed = !spec.proven;
      note = `series (Lagrange, M = ${M})`;
      break;
    }
    case "ratio": {
      if (spec.q === undefined) refuse("bad-series", "ratio rule needs q < 1 with |a_{k+1}|·r ≤ q·|a_k| for k > p");
      const q = toQ(spec.q);
      if (!(ge(q, ZERO) && lt(q, ONE))) refuse("hypothesis", `ratio rule needs 0 ≤ q < 1, got ${q}`);
      let prev = coef(p + 1);
      for (let k = p + 2; k <= p + 1 + look; k++) {
        const next = coef(k);
        if (gt(next.abs().multiply(r), q.multiply(prev.abs()))) {
          refuse("hypothesis", `ratio rule fails at k = ${k - 1}: |a_${k}|·r > q·|a_${k - 1}| on this domain`, { k });
        }
        prev = next;
      }
      const first = coef(p + 1).abs().multiply(r.pow(p + 1));
      rem = Iv.sym(first.divide(ONE.subtract(q)));
      assumed = !spec.proven;
      note = `series (ratio tail, q = ${q}, checked ${look} terms)`;
      break;
    }
    case "alternating": {
      // Terms a_k t^k must alternate in sign and decrease in size for every t
      // in the domain: for t > 0 the a_k alternate; for t < 0 they share a sign.
      const tail = [];
      for (let k = p + 1; k <= p + 1 + look; k++) tail.push(coef(k));
      const signs = tail.map(sign);
      if (signs.some((s) => s === 0)) refuse("hypothesis", "alternating rule needs nonzero tail coefficients");
      if (gt(t.hi, ZERO) && !signs.every((s, i) => i === 0 || s === -signs[i - 1])) {
        refuse("hypothesis", "alternating rule fails for x > centre: tail coefficients do not alternate in sign");
      }
      if (lt(t.lo, ZERO) && !signs.every((s) => s === signs[0])) {
        refuse("hypothesis", "alternating rule fails for x < centre: tail terms a_k (x−c)^k do not alternate");
      }
      for (let i = 1; i < tail.length; i++) {
        if (gt(tail[i].abs().multiply(r), tail[i - 1].abs())) {
          refuse("hypothesis", `alternating rule fails: terms grow at k = ${p + 1 + i} on this domain`);
        }
      }
      // The tail lies between 0 and its first term a_{p+1} t^{p+1}.
      const first = Iv.point(tail[0]).mul(t.pow(p + 1));
      rem = first.hull(Iv.point(ZERO));
      assumed = !spec.proven;
      note = `series (alternating, checked ${look} terms)`;
      break;
    }
    case "explicit": {
      if (spec.error === undefined) refuse("bad-series", "explicit rule needs error: an interval or bound for the tail");
      const e = Iv.from(spec.error);
      rem = e.isPoint ? Iv.sym(e.lo) : e;
      assumed = true;
      note = "series (explicit error, assumed)";
      break;
    }
    default:
      refuse("bad-series", `unknown or missing rule "${rule}": use lagrange, ratio, alternating or explicit`);
  }
  return new TaylorModel({ domain: D, coeffs: a, rem, order, bits, notes: [note], assumed });
}
