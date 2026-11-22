// Piecewise functions: pairs of (region, rule), first match wins.
//
// Regions use a betweenness chain on the tested variable:
//
//   2:x:8      2 ≤ x ≤ 8          :x:8     x ≤ 8         2:x:     x ≥ 2
//   2:!x:8     2 < x ≤ 8          2:x:!8   2 ≤ x < 8     (a "!" right after a colon makes it strict)
//   2n:x:!2n+1 2n ≤ x < 2n+1 for some integer n (any other free name is an integer)
//   :x:!-1 | 1:!x:   unions with "|";   "all", "else", "otherwise": everything
//
// Bounds are rational expressions of the parameters and at most one integer
// variable, affine in it. A region can also be a plain function x => boolean;
// such regions answer point questions, but interval questions (ranges,
// integrals, zeros) need the breakpoints that only chains provide.
//
// Rules may use the integer variable too: "x - n if n:x:!n+1" is the
// sawtooth, "(-1)^n if n:x:!n+1" a square wave.
import { Rational, RationalInterval } from "@ratmath/core";
import { Refinement } from "./refine.js";
import { Iv } from "./interval.js";
import { refuse, AnalyticError } from "./errors.js";
import { ZERO, ONE, lt, le, gt, ge, isZero, min, max, toQ } from "./rat.js";
import { parse, toAst, format, freeVariables, toRational, derivative as dAst } from "./expr.js";
import { AnalyticFunction, evalParams, gaussLegendre } from "./fn.js";
import * as roots from "./roots.js";

const q = (v) => (v instanceof Rational ? v : typeof v === "number" || typeof v === "string" ? toRational(v) : toQ(v));
const MAX_PIECES = 100000;

// ---- exact evaluation of bound expressions -------------------------------------

function evalQ(ast, env) {
  switch (ast.type) {
    case "num":
      return ast.value;
    case "var": {
      const v = env[ast.name];
      if (!(v instanceof Rational)) refuse("bad-region", `bound uses ${ast.name}, which has no exact rational value`);
      return v;
    }
    case "op": {
      const [a, b] = ast.args.map((x) => evalQ(x, env));
      switch (ast.op) {
        case "+": return a.add(b);
        case "-": return a.subtract(b);
        case "*": return a.multiply(b);
        case "/":
          if (isZero(b)) refuse("bad-region", "a bound divides by 0");
          return a.divide(b);
        case "neg": return a.negate();
        case "^": {
          if (b.denominator !== 1n) refuse("bad-region", "bounds take integer powers only");
          return a.pow(Number(b.numerator));
        }
      }
    }
  }
  return refuse("bad-region", `bounds must be rational expressions (got ${ast.type} ${ast.name ?? ast.op ?? ""}); pi, e and functions are not supported in bounds yet`);
}

/** Bound as an affine function of the integer variable: { c0, c1 } with value c0 + c1·n. */
function affine(ast, params, iname) {
  if (!iname || !freeVariables(ast).has(iname)) return { c0: evalQ(ast, params), c1: ZERO };
  const at = (k) => evalQ(ast, { ...params, [iname]: new Rational(BigInt(k)) });
  const c0 = at(0);
  const c1 = at(1).subtract(c0);
  for (const k of [2, -1, 3]) {
    if (at(k).compareTo(c0.add(c1.multiply(new Rational(BigInt(k))))) !== 0) {
      refuse("bad-region", `bound ${format(ast)} is not affine in ${iname}`);
    }
  }
  return { c0, c1 };
}

// ---- regions -------------------------------------------------------------------

const EVERYTHING = new Set(["all", "else", "otherwise", "always", ""]);

function parseChain(text, variable) {
  const parts = text.split(":");
  if (parts.length !== 3) refuse("bad-region", `"${text}" should look like a:${variable}:b (either side may be empty)`);
  const strict = [parts[1].trimStart().startsWith("!"), parts[2].trimStart().startsWith("!")];
  const clean = (s) => s.trim().replace(/^!/, "").trim();
  const [lo, mid, hi] = [clean(parts[0]), clean(parts[1]), clean(parts[2])];
  if (mid !== variable) refuse("bad-region", `the middle of "${text}" should be the variable ${variable}`);
  return {
    lo: lo === "" ? null : parse(lo),
    hi: hi === "" ? null : parse(hi),
    loStrict: strict[0],
    hiStrict: strict[1],
  };
}

export class Region {
  /**
   * Region.from("2:!x:8" | "2n:x:!2n+1 | ..." | x => boolean | Region, { variable, params })
   */
  static from(spec, opts = {}) {
    if (spec instanceof Region) return spec;
    return new Region(spec, opts);
  }

  constructor(spec, { variable = "x", params = {} } = {}) {
    this.variable = variable;
    this.params = evalParams(params);
    if (typeof spec === "function") {
      this.fn = spec;
      this.text = spec.toString();
      this.alternatives = null;
      this.integer = null;
      Object.freeze(this);
      return;
    }
    this.text = String(spec).trim();
    const alts = this.text.split("|").map((s) => s.trim());
    const names = new Set();
    const chains = alts.map((a) => {
      if (EVERYTHING.has(a.toLowerCase())) return { all: true };
      const c = parseChain(a, variable);
      for (const t of [c.lo, c.hi]) if (t) for (const n of freeVariables(t)) if (!(n in this.params)) names.add(n);
      return c;
    });
    if (names.size > 1) refuse("bad-region", `at most one integer variable per region, found ${[...names].join(", ")}`);
    this.integer = names.size ? [...names][0] : null;
    this.alternatives = chains.map((c) =>
      c.all ? c : { ...c, L: c.lo && affine(c.lo, this.params, this.integer), U: c.hi && affine(c.hi, this.params, this.integer) },
    );
    Object.freeze(this);
  }

  /**
   * The match at x: { n } (n is the smallest fitting integer, or null without
   * an integer variable), or null when x is outside.
   */
  match(x) {
    if (this.fn) {
      const r = this.fn(q(x)); // function regions always receive a Core Rational
      return r ? { n: null } : null;
    }
    x = q(x);
    for (const c of this.alternatives) {
      if (c.all) return { n: null };
      const m = matchChain(c, x);
      if (m) return m;
    }
    return null;
  }

  test(x) {
    return this.match(x) !== null;
  }

  /** Concrete intervals of the region that meet [a, b]: { lo, hi, loStrict, hiStrict, n }; null for function regions. */
  intervals(a, b) {
    if (this.fn) return null;
    a = q(a);
    b = q(b);
    const out = [];
    for (const c of this.alternatives) {
      if (c.all) {
        out.push({ lo: null, hi: null, loStrict: false, hiStrict: false, n: null });
        continue;
      }
      const ns = this.integer ? integerRange(c, a, b) : [null];
      for (const n of ns) {
        const N = n === null ? ZERO : new Rational(BigInt(n));
        const lo = c.L ? c.L.c0.add(c.L.c1.multiply(N)) : null;
        const hi = c.U ? c.U.c0.add(c.U.c1.multiply(N)) : null;
        if (lo && hi && gt(lo, hi)) continue;
        if (lo && gt(lo, b)) continue;
        if (hi && lt(hi, a)) continue;
        out.push({ lo, hi, loStrict: c.loStrict, hiStrict: c.hiStrict, n });
      }
    }
    return out;
  }

  /** Every finite endpoint of the region inside [a, b]. */
  breakpoints(a, b) {
    const iv = this.intervals(a, b);
    if (!iv) return null;
    const pts = [];
    for (const r of iv) for (const p of [r.lo, r.hi]) if (p && ge(p, q(a)) && le(p, q(b))) pts.push(p);
    return pts;
  }

  toString() {
    return this.text;
  }
}

function matchChain(c, x) {
  const okConst = (A, strict, isLower) => {
    const v = A.c0;
    return isLower ? (strict ? lt(v, x) : le(v, x)) : strict ? lt(x, v) : le(x, v);
  };
  if (!c.L?.c1 || isZero(c.L.c1)) {
    if (c.L && !okConst(c.L, c.loStrict, true)) return null;
  }
  if (!c.U?.c1 || isZero(c.U.c1)) {
    if (c.U && !okConst(c.U, c.hiStrict, false)) return null;
  }
  const varying = (c.L && !isZero(c.L.c1)) || (c.U && !isZero(c.U.c1));
  if (!varying) return { n: null };
  // n-range from each varying bound:  c0 + c1 n ≤ x  (lower)   x ≤ c0 + c1 n  (upper)
  let nlo = null; // { v, strict }
  let nhi = null;
  const tighten = (v, strict, upper) => {
    if (upper) {
      if (!nhi || lt(v, nhi.v) || (v.compareTo(nhi.v) === 0 && strict)) nhi = { v, strict };
    } else if (!nlo || gt(v, nlo.v) || (v.compareTo(nlo.v) === 0 && strict)) nlo = { v, strict };
  };
  if (c.L && !isZero(c.L.c1)) {
    const v = x.subtract(c.L.c0).divide(c.L.c1); // c1 n ≤ x − c0
    tighten(v, c.loStrict, gt(c.L.c1, ZERO));
  }
  if (c.U && !isZero(c.U.c1)) {
    const v = x.subtract(c.U.c0).divide(c.U.c1); // x − c0 ≤ c1 n
    tighten(v, c.hiStrict, lt(c.U.c1, ZERO));
  }
  // smallest integer n in the range
  let n;
  if (nlo) {
    const f = floorQ(nlo.v);
    const onIt = new Rational(f).compareTo(nlo.v) === 0;
    n = onIt && !nlo.strict ? f : f + 1n;
  } else {
    if (!nhi) return { n: null };
    // unbounded below: report the largest fitting n
    const f = floorQ(nhi.v);
    n = nhi.strict && new Rational(f).compareTo(nhi.v) === 0 ? f - 1n : f;
    return { n: Number(n) };
  }
  if (nhi) {
    const N = new Rational(n);
    if (nhi.strict ? !lt(N, nhi.v) : !le(N, nhi.v)) return null;
  }
  return { n: Number(n) };
}

function floorQ(v) {
  const a = v.numerator;
  const b = v.denominator;
  const f = a / b;
  return a < 0n && f * b !== a ? f - 1n : f;
}

/** Integers n whose concrete piece can meet [a, b]. */
function integerRange(c, a, b) {
  let lo = -Infinity;
  let hi = Infinity;
  const cut = (A, bound, isLowerBound) => {
    // isLowerBound: piece's lower end L(n) ≤ b ; else piece's upper end U(n) ≥ a
    if (!A || isZero(A.c1)) return;
    const v = (isLowerBound ? b : a).subtract(A.c0).divide(A.c1);
    const f = Number(floorQ(v));
    const cl = Number(-floorQ(v.negate()));
    const pos = gt(A.c1, ZERO);
    if (isLowerBound === pos) hi = Math.min(hi, f); // c1 n ≤ … with c1 > 0  →  n ≤ v
    else lo = Math.max(lo, cl);
    void bound;
  };
  cut(c.L, null, true);
  cut(c.U, null, false);
  if (!Number.isFinite(lo) || !Number.isFinite(hi)) {
    refuse("bad-region", "this region has infinitely many pieces in the interval; give both bounds in terms of n");
  }
  if (hi - lo + 1 > MAX_PIECES) refuse("budget", `more than ${MAX_PIECES} pieces in the interval`);
  const out = [];
  for (let n = lo; n <= hi; n++) out.push(n);
  return out;
}

/** where`2:!x:8` — a Region from a template (values may be interpolated). */
export function where(strings, ...values) {
  let text = strings[0];
  values.forEach((v, i) => (text += String(v) + strings[i + 1]));
  return new Region(text);
}

// ---- piecewise functions -------------------------------------------------------

/** "x^2 if :x:0; 1 - x if 0:!x:; 0 otherwise" → [[region text, rule text], ...] or null */
export function parsePiecewiseText(text) {
  if (!/\bif\b|\botherwise\b/.test(text)) return null;
  const parts = text.split(/;|\n/).map((s) => s.trim()).filter(Boolean);
  return parts.map((p) => {
    const m = /^(.*?)\s+if\s+(.*)$/.exec(p);
    if (m) return [m[2], m[1]];
    const o = /^(.*?)\s+(otherwise|else)$/.exec(p);
    if (o) return ["all", o[1]];
    return refuse("bad-piecewise", `"${p}" should read "rule if region" or "rule otherwise"`);
  });
}

export class PiecewiseFunction {
  #cache = new Map();
  /**
   * piecewise([[region, rule], ...], { variable, params }). Regions: chain
   * text, Region, or x => boolean. Rules: expression text, AST, number.
   */
  constructor(pieces, { variable = "x", params = {} } = {}) {
    if (typeof pieces === "string") pieces = parsePiecewiseText(pieces) ?? refuse("bad-piecewise", "no pieces found");
    this.variable = variable;
    this.params = Object.freeze({ ...params });
    this.pieces = Object.freeze(
      pieces.map(([region, rule]) => {
        const R = Region.from(region, { variable, params });
        const ast = typeof rule === "number" || typeof rule === "bigint" ? { type: "num", value: q(rule) } : rule instanceof AnalyticFunction ? rule.ast : toAst(rule);
        return Object.freeze({ region: R, ast });
      }),
    );
    // check that every rule's names are bound
    for (const p of this.pieces) {
      for (const name of freeVariables(p.ast)) {
        if (name !== variable && !(name in params) && name !== p.region.integer) {
          refuse("unbound", `${name} has no value in the rule ${format(p.ast)}`);
        }
      }
    }
    Object.freeze(this);
  }

  toString() {
    return this.pieces.map((p) => `${format(p.ast)} if ${p.region}`).join("; ");
  }

  with(p) {
    return new PiecewiseFunction(this.pieces.map((x) => [x.region.fn ?? x.region.text, x.ast]), { variable: this.variable, params: { ...this.params, ...p } });
  }

  /** The AnalyticFunction of piece i with integer n substituted. */
  rule(i, n = null) {
    const key = `${i}|${n}`;
    let f = this.#cache.get(key);
    if (!f) {
      const p = this.pieces[i];
      const params = { ...this.params };
      if (p.region.integer) params[p.region.integer] = new Rational(BigInt(n ?? 0));
      f = new AnalyticFunction(p.ast, { variable: this.variable, params });
      this.#cache.set(key, f);
    }
    return f;
  }

  /** { index, n, f } for the first piece containing x, or null. */
  locate(x) {
    for (let i = 0; i < this.pieces.length; i++) {
      const m = this.pieces[i].region.match(x);
      if (m) return { index: i, n: m.n, f: this.rule(i, m.n) };
    }
    return null;
  }

  float(x) {
    let X;
    try {
      X = toRational(x);
    } catch {
      return NaN;
    }
    const at = this.locate(X);
    return at ? at.f.float(x) : NaN;
  }

  /**
   * Split [a, b] into open segments and points with the active piece of each:
   * { lo, hi, at?, index, n, f } (f null where no piece applies).
   */
  segments(a, b) {
    a = q(a);
    b = q(b);
    const pts = [a, b];
    for (const p of this.pieces) {
      const bp = p.region.breakpoints(a, b);
      if (bp === null) refuse("no-breakpoints", "a region given as a function has no known breakpoints; interval questions need chain regions");
      pts.push(...bp);
    }
    pts.sort((x, y) => x.compareTo(y));
    const uniq = pts.filter((p, i) => i === 0 || p.compareTo(pts[i - 1]) !== 0);
    const out = [];
    const put = (lo, hi, at) => {
      const probe = at ?? lo.add(hi).divide(new Rational(2n));
      const m = this.locate(probe);
      out.push({ lo, hi, at, index: m?.index ?? null, n: m?.n ?? null, f: m?.f ?? null });
    };
    for (let i = 0; i < uniq.length; i++) {
      put(uniq[i], uniq[i], uniq[i]);
      if (i + 1 < uniq.length) put(uniq[i], uniq[i + 1], undefined);
    }
    return out;
  }

  /** Symbolic derivative of each rule (one-sided at breakpoints). */
  derivative() {
    return new PiecewiseFunction(
      this.pieces.map((p) => [p.region, dAst(p.ast, this.variable)]),
      { variable: this.variable, params: this.params },
    );
  }

  value(x, opts = {}) {
    const X = q(x);
    const at = this.locate(X);
    if (!at) {
      return new Refinement(
        () => ({ value: NaN, trust: "good" }),
        function* () {
          return refuse("undefined", `no piece is defined at ${X}`);
        },
      );
    }
    return at.f.value(X, opts);
  }

  range(interval, opts = {}) {
    const I = Iv.from(interval);
    const self = this;
    return new Refinement(
      () => {
        const n = 512;
        let lo = Infinity;
        let hi = -Infinity;
        const a = I.lo.toNumber();
        const b = I.hi.toNumber();
        for (let i = 0; i <= n; i++) {
          const y = self.float(a + ((b - a) * i) / n);
          if (Number.isFinite(y)) {
            lo = Math.min(lo, y);
            hi = Math.max(hi, y);
          }
        }
        return { value: [lo, hi], trust: "rough" };
      },
      function* () {
        let acc = null;
        const segs = self.segments(I.lo, I.hi);
        let k = 0;
        for (const s of segs) {
          k++;
          if (!s.f) continue;
          let iv;
          if (s.at) iv = Iv.from(s.f.value(s.at, { digits: opts.digits ?? 6 }).exact());
          else {
            // closed hull of the open segment: a valid outer bound
            const r = s.f.range(new Iv(s.lo, s.hi), opts);
            for (const st of r.stages()) if (st.stage === "progress") yield { done: k, of: segs.length, step: "piece", partial: acc?.toRationalInterval() };
            iv = Iv.from(r.exact());
          }
          acc = acc ? acc.hull(iv) : iv;
        }
        if (!acc) refuse("undefined", "no piece is defined on this interval");
        return { value: acc.toRationalInterval(), via: `certified range on ${segs.filter((s) => s.f && !s.at).length} pieces (closures of the pieces)` };
      },
    );
  }

  integral(a, b, opts = {}) {
    const A = q(a);
    const B = q(b);
    const self = this;
    return new Refinement(
      () => {
        const value = gaussLegendre((t) => self.float(t), A.toNumber(), B.toNumber(), 64);
        return { value, trust: Number.isFinite(value) ? "rough" : "unsure" };
      },
      function* () {
        const [lo, hi, sgn] = lt(A, B) ? [A, B, ONE] : [B, A, ONE.negate()];
        let acc = Iv.point(ZERO);
        const segs = self.segments(lo, hi).filter((s) => !s.at && lt(s.lo, s.hi));
        let k = 0;
        for (const s of segs) {
          if (!s.f) refuse("undefined", `no piece is defined on (${s.lo}, ${s.hi})`);
          acc = acc.add(Iv.from(s.f.integral(s.lo, s.hi, opts).exact()));
          yield { done: ++k, of: segs.length, step: "piece", partial: acc.scale(sgn).toRationalInterval() };
        }
        return { value: acc.scale(sgn).toRationalInterval(), via: `sum of certified integrals over ${segs.length} pieces` };
      },
    );
  }

  /**
   * Breakpoints in [a, b]: { at, value, left, right, kind } where value is
   * f at the point (null if undefined), left/right are the one-sided limits
   * of the neighbouring rules (null where no piece applies or the rule is
   * undefined there). kind: "continuous" (all equal, proven), "jump" (left
   * and right proven different), "removable" (limits equal, value missing or
   * different), "edge" (a piece only on one side), "unproven".
   */
  breaks(interval, opts = {}) {
    const I = Iv.from(interval);
    const self = this;
    const digits = opts.digits ?? 12;
    const valueOf = (f, x) => {
      if (!f) return null;
      try {
        return f.value(x, { digits }).exact();
      } catch (e) {
        if (e instanceof AnalyticError) return null;
        throw e;
      }
    };
    return new Refinement(
      () => ({ value: [], trust: "unsure" }),
      function* () {
        const segs = self.segments(I.lo, I.hi);
        const regionPoints = new Set(self.pieces.flatMap((p) => p.region.breakpoints(I.lo, I.hi).map(String)));
        const out = [];
        for (let i = 0; i < segs.length; i++) {
          const s = segs[i];
          if (!s.at) continue;
          const left = valueOf(segs[i - 1]?.f, s.at);
          const right = valueOf(segs[i + 1]?.f, s.at);
          const value = valueOf(s.f, s.at);
          const leftPiece = segs[i - 1]?.index ?? null;
          const rightPiece = segs[i + 1]?.index ?? null;
          const interior = i > 0 && i < segs.length - 1;
          if (!interior && !regionPoints.has(s.at.toString())) continue; // an end of the interval, not a break
          if (interior && leftPiece === rightPiece && leftPiece === s.index && segs[i - 1].n === segs[i + 1].n) continue; // not a real break
          const same = (u, v) => u && v && u.low.compareTo(v.low) === 0 && u.high.compareTo(v.high) === 0 && u.low.compareTo(u.high) === 0;
          const apart = (u, v) => u && v && (lt(u.high, v.low) || lt(v.high, u.low));
          let kind = "unproven";
          if (!left || !right) kind = "edge";
          else if (apart(left, right)) kind = "jump";
          else if (same(left, right)) kind = value && same(left, value) ? "continuous" : "removable";
          out.push(Object.freeze({ at: s.at, value, left, right, kind, defined: !!value }));
          yield { done: i + 1, of: segs.length, step: "break" };
        }
        return { value: out, via: "one-sided limits from each piece's rule" };
      },
    );
  }
}

// zeros / extrema / inflections / poles piece by piece
for (const name of ["zeros", "extrema", "inflections", "poles"]) {
  PiecewiseFunction.prototype[name] = function (interval, opts = {}) {
    const I = Iv.from(Array.isArray(interval) ? new Iv(q(interval[0]), q(interval[1])) : interval);
    const self = this;
    return new Refinement(
      () => {
        const out = [];
        for (const s of self.segments(I.lo, I.hi)) {
          if (!s.f || s.at) continue;
          out.push(...roots[name](s.f, [s.lo, s.hi], opts).quick.value);
        }
        return { value: out, trust: "rough" };
      },
      function* () {
        const out = [];
        const segs = self.segments(I.lo, I.hi);
        let k = 0;
        for (const s of segs) {
          k++;
          if (!s.f) continue;
          if (s.at) {
            if (name === "zeros") {
              try {
                const v = s.f.value(s.at).exact();
                if (isZero(v.low) && isZero(v.high)) out.push(Object.freeze({ kind: "exact", at: s.at, lo: s.at, hi: s.at, unique: true }));
              } catch (e) {
                if (!(e instanceof AnalyticError)) throw e;
              }
            }
            continue;
          }
          const list = roots[name](s.f, [s.lo, s.hi], opts).exact();
          for (const r of list) {
            // the segment is open: drop results sitting exactly on its ends
            if (r.at && (r.at.compareTo(s.lo) === 0 || r.at.compareTo(s.hi) === 0)) continue;
            out.push(Object.freeze({ ...r, piece: s.index, ...(s.n !== null ? { n: s.n } : {}) }));
          }
          yield { done: k, of: segs.length, step: "piece", partial: out.slice() };
        }
        out.sort((x, y) => x.lo.compareTo(y.lo));
        return { value: out, via: `${name} piece by piece on ${segs.filter((s) => s.f && !s.at).length} pieces` };
      },
    );
  };
}

/** piecewise([[region, rule], ...] | "rule if region; ...", { variable, params }) */
export function piecewise(pieces, opts) {
  return new PiecewiseFunction(pieces, opts);
}

export { RationalInterval };
