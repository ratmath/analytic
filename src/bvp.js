// Two-point boundary value problems  y″ = F(x, y, y′)  by certified shooting.
//
// One datum at the left end is unknown (the slope, when y(a) is given). A
// Float64 shooting finds it approximately; then validated solves from just
// below and just above it give end values that miss the right-hand condition
// on opposite sides, and a validated solve from the whole bracket shows that
// every solution in between exists up to b. By the intermediate value
// theorem a solution of the boundary value problem starts in the bracket,
// and the tube from the bracket encloses it.
import { Rational } from "@ratmath/core";
import { Refinement } from "@ratmath/core/refine";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, lt, gt, toQ } from "./rat.js";
import { toAst, compileFloat, floatEnv, derivative, simplify, freeVariables, toRational, format } from "./expr.js";
import { solve } from "./ode.js";

const q = (x) => (typeof x === "string" ? toRational(x) : typeof x === "number" && !Number.isInteger(x) ? toRational(x) : toQ(x));

function condition(c, side, names) {
  const keys = Object.keys(c ?? {});
  if (keys.length !== 1 || (keys[0] !== "y" && keys[0] !== "dy" && !names.includes(keys[0]))) refuse("bad-bvp", `the ${side} condition is { y: value } or { dy: value }`);
  const index = keys[0] === "y" || keys[0] === names[0] ? 0 : 1;
  return { index, value: q(c[keys[0]]) };
}

export class BVPSolution {
  constructor(tube, unknown, start, info) {
    /** The validated tube: an ODESolution for [y, y′]. */
    this.tube = tube;
    /** Which left-end datum was solved for ("dy" or "y") and its enclosure. */
    this.unknown = unknown;
    this.start = start;
    this.linear = info.linear;
    /** True when the problem is linear, where the solution found is the only one. */
    this.unique = info.linear;
    this.interval = info.interval;
    Object.freeze(this);
  }
  /** Certified enclosure of y(x). */
  at(x) {
    return this.tube.at(x)[0];
  }
  /** Certified enclosure of y′(x). */
  slopeAt(x) {
    return this.tube.at(x)[1];
  }
}

/**
 * bvp({ f, interval: [a, b], left, right, vars, time, params, digits, guess })
 * → Refinement. `f` is the formula for y″ in x, y and dy (names from `time`
 * and `vars`, default "x" and ["y", "dy"]); `left` and `right` are
 * { y: value } or { dy: value }. The preview is a Float64 shooting
 * { t, y, dy, start }; the exact stage is a BVPSolution.
 */
export function bvp(spec) {
  const time = spec.time ?? "x";
  const names = spec.vars ?? ["y", "dy"];
  if (names.length !== 2) refuse("bad-bvp", "vars names y and its derivative, such as [\"y\", \"dy\"]");
  const ast = toAst(spec.f);
  const params = spec.params ?? {};
  for (const name of freeVariables(ast)) {
    if (name !== time && !names.includes(name) && !(name in params)) refuse("unbound", `${name} has no value: pass it in params`);
  }
  const a = q(spec.interval[0]);
  const b = q(spec.interval[1]);
  if (!lt(a, b)) refuse("bad-interval", "bvp needs an interval [a, b] with a < b");
  const left = condition(spec.left, "left", names);
  const right = condition(spec.right, "right", names);
  const free = 1 - left.index; // the left-end datum that is not given
  const digits = spec.digits ?? 8;
  // linear in y and y′: the second partials vanish identically
  const linear = names.every((n1) => names.every((n2) => format(simplify(derivative(simplify(derivative(ast, n1)), n2))) === "0"));

  const F = compileFloat(ast);
  const fenv = floatEnv(params);
  const steps = spec.previewSteps ?? 400;
  const shoot = (s, keep) => {
    const af = a.toNumber();
    const h = (b.toNumber() - af) / steps;
    let y = left.index === 0 ? [left.value.toNumber(), s] : [s, left.value.toNumber()];
    const rhs = (t, u) => [u[1], F({ ...fenv, [time]: t, [names[0]]: u[0], [names[1]]: u[1] })];
    const ax = (u, k, c) => [u[0] + c * k[0], u[1] + c * k[1]];
    const out = keep ? { t: new Float64Array(steps + 1), y: new Float64Array(steps + 1), dy: new Float64Array(steps + 1) } : null;
    for (let k = 0; ; k++) {
      const t = af + k * h;
      if (out) { out.t[k] = t; out.y[k] = y[0]; out.dy[k] = y[1]; }
      if (k === steps) break;
      const k1 = rhs(t, y);
      const k2 = rhs(t + h / 2, ax(y, k1, h / 2));
      const k3 = rhs(t + h / 2, ax(y, k2, h / 2));
      const k4 = rhs(t + h, ax(y, k3, h));
      y = [y[0] + (h / 6) * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]), y[1] + (h / 6) * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1])];
    }
    return keep ? out : y[right.index] - right.value.toNumber();
  };
  const floatStart = () => {
    let s0 = spec.guess ?? 0;
    let g0 = shoot(s0);
    let s1 = s0 + 1;
    let g1 = shoot(s1);
    for (let it = 0; it < 60 && Number.isFinite(g1); it++) {
      if (Math.abs(g1) < 1e-13 * Math.max(1, Math.abs(right.value.toNumber())) || g1 === g0) break;
      const s2 = s1 - (g1 * (s1 - s0)) / (g1 - g0);
      [s0, g0, s1] = [s1, g1, s2];
      g1 = shoot(s1);
    }
    return Number.isFinite(g1) ? s1 : NaN;
  };

  const exactSolve = (start) => {
    const y0 = left.index === 0 ? [left.value, start] : [start, left.value];
    return solve({ f: [names[1], ast], y0, vars: names, time, t0: a, until: b, params, order: spec.order }).exact();
  };
  const miss = (sol) => Iv.from(sol.final[right.index]).sub(Iv.point(right.value));

  return new Refinement(
    () => {
      const s = floatStart();
      if (!Number.isFinite(s)) return { value: null, trust: "unsure" };
      return { value: { ...shoot(s, true), start: s }, trust: "good" };
    },
    function* () {
      const s = floatStart();
      if (!Number.isFinite(s)) refuse("no-solution-found", "the Float64 shooting did not converge; pass a guess for the unknown left-end value");
      const centre = toRational(s.toPrecision(15));
      const scale = Math.max(1, Math.abs(s));
      let attempt = 0;
      let last = "";
      for (let e = digits; e >= 1; e -= 2) {
        attempt += 1;
        const delta = toRational((scale * 10 ** -e).toPrecision(3));
        const lo = centre.subtract(delta);
        const hi = centre.add(delta);
        yield { done: attempt, of: attempt + 1, step: `bracket ±${delta.toNumber().toExponential(0)}` };
        let below;
        let above;
        try {
          below = exactSolve(lo);
          above = exactSolve(hi);
        } catch (err) {
          if (!(err instanceof AnalyticError)) throw err;
          last = err.message;
          continue;
        }
        if (!below.complete || !above.complete) { last = "a validated solve stopped before the right end"; continue; }
        const gl = miss(below);
        const gh = miss(above);
        const opposite = (lt(gl.hi, ZERO) && gt(gh.lo, ZERO)) || (gt(gl.lo, ZERO) && lt(gh.hi, ZERO));
        if (!opposite) { last = "the end values at the two ends of the bracket do not straddle the condition"; continue; }
        yield { done: attempt, of: attempt + 1, step: "tube" };
        let tube;
        try {
          tube = exactSolve(new Iv(lo, hi));
        } catch (err) {
          if (!(err instanceof AnalyticError)) throw err;
          last = err.message;
          continue;
        }
        if (!tube.complete) { last = "the validated solve from the whole bracket stopped early"; continue; }
        return {
          value: new BVPSolution(tube, free === 1 ? "dy" : "y", new Iv(lo, hi).toRationalInterval(), { linear, interval: [a, b] }),
          via: `shooting: validated solves from both ends of a bracket of width ${delta.multiply(new Rational(2n)).toNumber().toExponential(0)} straddle the right-hand condition${linear ? "; the problem is linear, so this is the only solution" : ""}`,
        };
      }
      return refuse("no-enclosure", `no bracket could be proven (${last})`);
    },
  );
}
