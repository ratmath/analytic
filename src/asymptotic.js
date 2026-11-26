// Behaviour at infinity, with proof.
//
// On a ray [X, ∞) every subexpression is written as
//
//     g(x) = e^(k·x) · x^p · (log x)^m · (ℓ + ρ(x))
//
// with exact rational exponents (k, p, m), a constant ℓ enclosed by an
// interval L, and a remainder |ρ(x)| ≤ C·e^(b·x)·x^a·(log x)^c that decays.
// Where no constant leads (sin x), the node only carries a range: ℓ(x) lies
// in L for every x ≥ X ("osc"). Sums, products, quotients, powers and the
// elementary functions keep this form, so limits at infinity, the tail of an
// improper integral and its convergence or divergence are read off it.
// Bounds that only hold from some point on throw "larger-x"; callers retry
// with a larger X.
import { Rational } from "@ratmath/core";
import { Iv } from "./interval.js";
import { AnalyticError, refuse } from "./errors.js";
import { ZERO, ONE, TWO, lt, le, gt, ge } from "./rat.js";
import { derivative, constantRational, num, v as variable, op, call, format } from "./expr.js";
import { encloseAst } from "./ieval.js";
import { rationalFunction, deg, isZeroPoly } from "./rpoly.js";

const E0 = Object.freeze({ k: ZERO, p: ZERO, m: ZERO });
const cmpE = (a, b) => a.k.compareTo(b.k) || a.p.compareTo(b.p) || a.m.compareTo(b.m);
const signE = (e) => Math.sign(cmpE(e, E0));
const addE = (a, b) => ({ k: a.k.add(b.k), p: a.p.add(b.p), m: a.m.add(b.m) });
const subE = (a, b) => ({ k: a.k.subtract(b.k), p: a.p.subtract(b.p), m: a.m.subtract(b.m) });
const scaleE = (a, c) => ({ k: a.k.multiply(c), p: a.p.multiply(c), m: a.m.multiply(c) });
const negE = (a) => scaleE(a, ONE.negate());
const isZeroQ = (x) => x.numerator === 0n;

const larger = (why) => { throw new AnalyticError("larger-x", why); };
const pos = (x) => (x.numerator > 0n ? x : ZERO);
const PI = { type: "const", name: "pi" };

/** e^(k·X)·X^p·(log X)^m as an interval. */
function termAt(e, ctx) {
  let r = Iv.point(ONE);
  if (!isZeroQ(e.k)) r = r.mul(encloseAst(call("exp", num(e.k.multiply(ctx.X))), {}, ctx.bits));
  if (!isZeroQ(e.p)) r = r.mul(encloseAst(op("^", num(ctx.X), num(e.p)), {}, ctx.bits));
  if (!isZeroQ(e.m)) r = r.mul(encloseAst(op("^", num(ctx.logX.lo), num(e.m)), {}, ctx.bits).hull(encloseAst(op("^", num(ctx.logX.hi), num(e.m)), {}, ctx.bits)));
  return r.roundOut(ctx.bits, 6000);
}

/**
 * Whether e^(k·x)·x^p·(log x)^m never increases on [X, ∞): its logarithmic
 * derivative k + p/x + m/(x·log x) is at most 0 there.
 */
function decreasing(e, ctx) {
  const s = signE(e);
  if (s === 0) return true;
  if (s > 0) return false;
  const logLo = ctx.logX.lo;
  if (e.k.numerator < 0n) return le(pos(e.p).divide(ctx.X).add(pos(e.m).divide(ctx.X.multiply(logLo))).add(e.k), ZERO);
  if (e.p.numerator < 0n) return le(e.p.add(pos(e.m).divide(logLo)), ZERO);
  return true;
}

/** An upper bound of the term on [X, ∞): its value at X once it decreases. */
function supTerm(e, ctx) {
  if (signE(e) === 0) return ONE;
  if (!decreasing(e, ctx)) larger("a bound does not hold this early");
  return termAt(e, ctx).hi;
}
const up = (x, ctx) => Iv.point(x).roundOut(ctx.bits, 6000).hi;
const envAt = (env, ctx) => env.C.multiply(supTerm(env.e, ctx));

/** One envelope that bounds a sum of envelopes: the slowest to decay absorbs the others. */
function envSum(envs, ctx) {
  const list = envs.filter((x) => x && !isZeroQ(x.C));
  if (!list.length) return null;
  let d = list[0];
  for (const x of list) if (cmpE(x.e, d.e) > 0) d = x;
  let C = ZERO;
  for (const x of list) C = C.add(x === d ? x.C : x.C.multiply(supTerm(subE(x.e, d.e), ctx)));
  return { C: up(C, ctx), e: d.e };
}

const constNode = (iv) => ({ e: E0, L: iv, osc: false, r: null });
const R = (iv, ctx) => iv.roundOut(ctx.bits, 6000);

/** An interval that holds ℓ + ρ(x) for every x ≥ X. */
function spread(n, ctx) {
  if (!n.r) return n.L;
  const s = envAt(n.r, ctx);
  return new Iv(n.L.lo.subtract(s), n.L.hi.add(s));
}
/** |g(x)| ≤ C·term(x) on the ray. */
function upperEnv(n, ctx) {
  if (!n.osc && n.r && isZeroQ(n.L.mag)) return { C: n.r.C, e: addE(n.e, n.r.e) };
  return { C: spread(n, ctx).mag, e: n.e };
}

function mul(A, B, ctx) {
  const e = addE(A.e, B.e);
  if (A.osc || B.osc) return { e, L: R(spread(A, ctx).mul(spread(B, ctx)), ctx), osc: true, r: null };
  const envs = [];
  if (B.r) envs.push({ C: A.L.mag.multiply(B.r.C), e: B.r.e });
  if (A.r) envs.push({ C: B.L.mag.multiply(A.r.C), e: A.r.e });
  if (A.r && B.r) envs.push({ C: A.r.C.multiply(B.r.C), e: addE(A.r.e, B.r.e) });
  return { e, L: R(A.L.mul(B.L), ctx), osc: false, r: envSum(envs, ctx) };
}

function nonzeroSpread(A, ctx, what) {
  const S = spread(A, ctx);
  if (S.containsZero()) {
    if (!A.osc && !A.L.containsZero()) larger(`${what} is not yet bounded away from 0`);
    refuse("undecided", `${what} could not be bounded away from 0 near infinity`);
  }
  return S;
}

function recip(A, ctx) {
  const S = nonzeroSpread(A, ctx, "a denominator");
  if (A.osc) return { e: negE(A.e), L: R(S.recip(), ctx), osc: true, r: null };
  // 1/(ℓ + ρ) = 1/ℓ − ρ/(ℓ·(ℓ + ρ))
  const r = A.r ? { C: up(A.r.C.divide(A.L.mig.multiply(S.mig)), ctx), e: A.r.e } : null;
  return { e: negE(A.e), L: R(A.L.recip(), ctx), osc: false, r };
}

function add(A, B, ctx) {
  let c = cmpE(A.e, B.e);
  if (c < 0) { [A, B] = [B, A]; c = -c; }
  if (c === 0) {
    if (A.osc || B.osc) return { e: A.e, L: R(spread(A, ctx).add(spread(B, ctx)), ctx), osc: true, r: null };
    return { e: A.e, L: R(A.L.add(B.L), ctx), osc: false, r: envSum([A.r, B.r], ctx) };
  }
  // B is of smaller order: it joins the remainder
  const ub = upperEnv(B, ctx);
  const shifted = { C: ub.C, e: subE(ub.e, A.e) };
  if (signE(shifted.e) >= 0) {
    // B was a pure remainder whose bound is not below A's order: compare as ranges
    const SA = upperEnv(A, ctx);
    const env = envSum([SA, ub], ctx);
    return { e: env.e, L: new Iv(env.C.negate(), env.C), osc: true, r: null };
  }
  if (A.osc) {
    const s = envAt(shifted, ctx);
    const S = spread(A, ctx);
    return { e: A.e, L: new Iv(S.lo.subtract(s), S.hi.add(s)), osc: true, r: null };
  }
  return { e: A.e, L: A.L, osc: false, r: envSum([A.r, shifted], ctx) };
}

const neg = (A) => ({ ...A, L: A.L.neg() });

function powNode(A, c, ctx) {
  if (isZeroQ(c)) return constNode(Iv.point(ONE));
  if (c.denominator === 1n) {
    if (c.numerator < 0n) return recip(powNode(A, c.negate(), ctx), ctx);
    if (c.numerator > 512n) refuse("undecided", "the power is too large to follow at infinity");
    let out = null;
    let base = A;
    for (let n = c.numerator; n > 0n; n >>= 1n) {
      if (n & 1n) out = out ? mul(out, base, ctx) : base;
      if (n > 1n) base = mul(base, base, ctx);
    }
    return out;
  }
  const S = nonzeroSpread(A, ctx, "the base of a fractional power");
  const at = (iv, expo) => encloseAst(op("^", variable("u"), num(expo)), { u: iv }, ctx.bits);
  const e = scaleE(A.e, c);
  if (A.osc) return { e, L: R(at(S, c), ctx), osc: true, r: null };
  // (ℓ + ρ)^c = ℓ^c + c·ξ^(c−1)·ρ with ξ between
  const r = A.r ? { C: up(c.abs().multiply(at(S, c.subtract(ONE)).mag).multiply(A.r.C), ctx), e: A.r.e } : null;
  return { e, L: R(at(A.L, c), ctx), osc: false, r };
}

/** A node that tends to 0 or to a constant, rewritten as (constant + remainder). */
function finite(A, ctx) {
  const s = signE(A.e);
  if (s === 0) return A;
  if (s > 0) return null;
  return { e: E0, L: Iv.point(ZERO), osc: false, r: upperEnv(A, ctx) };
}

const derivativeTrees = new Map();
/** F applied to a node with a finite limit: F(ℓ + ρ) = F(ℓ) + F′(ξ)·ρ. */
function applyF(name, A, ctx) {
  const S = spread(A, ctx);
  const F = call(name, variable("u"));
  try {
    if (A.osc) return { e: E0, L: R(encloseAst(F, { u: S }, ctx.bits), ctx), osc: true, r: null };
    const L = R(encloseAst(F, { u: A.L }, ctx.bits), ctx);
    if (!A.r) return { e: E0, L, osc: false, r: null };
    let d = derivativeTrees.get(name);
    if (!d) derivativeTrees.set(name, (d = derivative(F, "u")));
    return { e: E0, L, osc: false, r: { C: up(encloseAst(d, { u: S }, ctx.bits).mag.multiply(A.r.C), ctx), e: A.r.e } };
  } catch (err) {
    if (err instanceof AnalyticError && err.code !== "larger-x" && A.r) larger(err.message);
    throw err;
  }
}

/**
 * F(g) for g → 0 where F(0) = 0 and F′(0) = factor: F(g) = factor·g·(1 + θ)
 * with |θ| ≤ |g| once |g| ≤ 1/2 (true of sin, tan, atan, tanh, asin, sinh,
 * log1p and of erf with its factor 2/√π).
 */
function small(name, A, ctx, factor = Iv.point(ONE)) {
  if (A.osc || A.L.containsZero()) return applyF(name, finite(A, ctx), ctx);
  const ub = upperEnv(A, ctx);
  if (gt(envAt(ub, ctx), new Rational(1n, 2n))) larger("an argument is not yet small");
  const S = spread(A, ctx);
  const r = envSum([A.r, { C: S.mag.multiply(ub.C), e: ub.e }], ctx);
  const f = factor.mag;
  return { e: A.e, L: R(A.L.mul(factor), ctx), osc: false, r: r && { C: up(r.C.multiply(f), ctx), e: r.e } };
}

/** g = a·x + b with rational a, b, or null. */
function linearIn(ast, name) {
  switch (ast.type) {
    case "num": return { a: ZERO, b: ast.value };
    case "var": return ast.name === name ? { a: ONE, b: ZERO } : null;
    case "op": {
      const [x, y] = ast.args.map((n) => linearIn(n, name));
      if (!x || (ast.args.length > 1 && !y)) return null;
      if (ast.op === "neg") return { a: x.a.negate(), b: x.b.negate() };
      if (ast.op === "+") return { a: x.a.add(y.a), b: x.b.add(y.b) };
      if (ast.op === "-") return { a: x.a.subtract(y.a), b: x.b.subtract(y.b) };
      if (ast.op === "*" && isZeroQ(x.a)) return { a: y.a.multiply(x.b), b: y.b.multiply(x.b) };
      if (ast.op === "*" && isZeroQ(y.a)) return { a: x.a.multiply(y.b), b: x.b.multiply(y.b) };
      if (ast.op === "/" && isZeroQ(y.a) && !isZeroQ(y.b)) return { a: x.a.divide(y.b), b: x.b.divide(y.b) };
      return null;
    }
  }
  return null;
}

function expNode(A, ctx, linear) {
  if (linear && !isZeroQ(linear.a)) {
    return { e: { k: linear.a, p: ZERO, m: ZERO }, L: R(encloseAst(call("exp", num(linear.b)), {}, ctx.bits), ctx), osc: false, r: null };
  }
  if (signE(A.e) <= 0) return applyF("exp", finite(A, ctx), ctx);
  const S = spread(A, ctx);
  if (lt(S.hi, ZERO)) {
    // g ≤ −κ·x once term(x)/x is nondecreasing: e^g ≤ e^(−κ·x)
    const e1 = subE(A.e, { k: ZERO, p: ONE, m: ZERO });
    if (signE(e1) >= 0) {
      if (!decreasing(negE(e1), ctx)) larger("a growth bound does not hold this early");
      const kappa = termAt(e1, ctx).lo.multiply(S.hi.negate());
      return { e: { k: Iv.point(kappa).roundOut(24).lo.negate(), p: ZERO, m: ZERO }, L: new Iv(ZERO, ONE), osc: true, r: null };
    }
    // slower than x but faster than log x (−√x): e^g ≤ x^(−q)
    const e2 = subE(A.e, { k: ZERO, p: ZERO, m: ONE });
    if (signE(e2) >= 0) {
      if (!decreasing(negE(e2), ctx)) larger("a growth bound does not hold this early");
      const qq = termAt(e2, ctx).lo.multiply(S.hi.negate());
      return { e: { k: ZERO, p: Iv.point(qq).roundOut(24).lo.negate(), m: ZERO }, L: new Iv(ZERO, ONE), osc: true, r: null };
    }
    refuse("undecided", "an exponential of a slowly growing argument could not be bounded");
  }
  if (gt(S.lo, ZERO)) refuse("growth", "an exponential of a growing argument has no simple bound here");
  if (!A.osc && !A.L.containsZero()) larger("the sign of an exponent is not yet settled");
  return refuse("undecided", "an exponent may oscillate with growing size");
}

function logNode(A, ctx) {
  const S = spread(A, ctx);
  if (le(S.lo, ZERO)) {
    if (!A.osc && gt(A.L.lo, ZERO)) larger("the argument of a logarithm is not yet positive");
    refuse("undecided", "the argument of a logarithm could not be shown positive near infinity");
  }
  if (!isZeroQ(A.e.m)) refuse("undecided", "a logarithm of a logarithm is beyond the growth scale used here");
  let out = applyF("log", { e: E0, L: A.L, osc: A.osc, r: A.r }, ctx);
  if (!isZeroQ(A.e.p)) out = add({ e: { k: ZERO, p: ZERO, m: ONE }, L: Iv.point(A.e.p), osc: false, r: null }, out, ctx);
  if (!isZeroQ(A.e.k)) out = add({ e: { k: ZERO, p: ONE, m: ZERO }, L: Iv.point(A.e.k), osc: false, r: null }, out, ctx);
  return out;
}

/** A bounded odd function with limits ±lim at ±∞ and |F(y) − F(±∞)| ≤ 1/|y| (atan, tanh, erf). */
function saturating(name, A, ctx, lim, factor) {
  const s = signE(A.e);
  if (s < 0) return small(name, A, ctx, factor);
  if (s === 0) return applyF(name, A, ctx);
  const S = spread(A, ctx);
  if (S.containsZero()) {
    if (!A.osc && !A.L.containsZero()) larger("the sign of an argument is not yet settled");
    return { e: E0, L: new Iv(lim.hi.negate(), lim.hi), osc: true, r: null };
  }
  const L = gt(S.lo, ZERO) ? lim : lim.neg();
  return { e: E0, L, osc: false, r: { C: up(S.mig.reciprocal(), ctx), e: negE(A.e) } };
}

/** A polynomial as a node: its leading term, the lower terms as the remainder. */
function polyNode(p, ctx) {
  if (isZeroPoly(p)) return constNode(Iv.point(ZERO));
  const d = deg(p);
  const envs = [];
  for (let i = 0; i < d; i++) if (!isZeroQ(p[i])) envs.push({ C: p[i].abs(), e: { k: ZERO, p: new Rational(BigInt(i - d)), m: ZERO } });
  return { e: { k: ZERO, p: new Rational(BigInt(d)), m: ZERO }, L: Iv.point(p[d]), osc: false, r: envSum(envs, ctx) };
}

function evalNode(ast, ctx) {
  const go = (n) => evalNode(n, ctx);
  if (ast.type === "op") {
    // a rational function is expanded exactly first, so that leading terms that cancel (1 − (1 − 1/x)²) do
    const rf = rationalFunction(ast, ctx.name, {}, 64);
    if (rf) return mul(polyNode(rf.num, ctx), recip(polyNode(rf.den, ctx), ctx), ctx);
  }
  switch (ast.type) {
    case "num":
      return constNode(Iv.point(ast.value));
    case "const":
      return constNode(R(encloseAst(ast, {}, ctx.bits), ctx));
    case "var": {
      if (ast.name === ctx.name) return { e: { k: ZERO, p: ONE, m: ZERO }, L: Iv.point(ONE), osc: false, r: null };
      const val = ctx.env[ast.name];
      if (val === undefined) refuse("unbound", `no value for ${ast.name}`);
      return constNode(val);
    }
    case "op": {
      const [a, b] = ast.args;
      switch (ast.op) {
        case "neg": return neg(go(a));
        case "+": return add(go(a), go(b), ctx);
        case "-": return add(go(a), neg(go(b)), ctx);
        case "*": return mul(go(a), go(b), ctx);
        case "/": return mul(go(a), recipAst(b, ctx), ctx);
        case "^": {
          const c = constantRational(b);
          if (c !== null) {
            if (c.numerator < 0n) return recipAst(c.equals(ONE.negate()) ? a : op("^", a, num(c.negate())), ctx);
            if (a.type === "call" && a.name === "exp") return go(call("exp", op("*", num(c), a.args[0])));
            return powNode(go(a), c, ctx);
          }
          return go(call("exp", op("*", b, call("log", a))));
        }
      }
      break;
    }
    case "call": {
      const name = ast.name === "ln" ? "log" : ast.name;
      const arg = ast.args[0];
      if (name === "exp") return expNode(go(arg), ctx, linearIn(arg, ctx.name));
      if (name === "log") {
        // log(1 + h) with h → 0 keeps h as its leading term
        if (arg.type === "op" && arg.op === "+") {
          const one = (n) => n.type === "num" && n.value.equals(ONE);
          const h = one(arg.args[0]) ? arg.args[1] : one(arg.args[1]) ? arg.args[0] : null;
          if (h) {
            const H = go(h);
            if (signE(H.e) < 0) return small("log1p", H, ctx);
          }
        }
        return logNode(go(arg), ctx);
      }
      const A = go(arg);
      const s = signE(A.e);
      switch (name) {
        case "sqrt": return powNode(A, new Rational(1n, 2n), ctx);
        case "cbrt": return powNode(A, new Rational(1n, 3n), ctx);
        case "abs": {
          const S = spread(A, ctx);
          if (!A.osc && !S.containsZero()) return gt(S.lo, ZERO) ? A : neg(A);
          return { e: A.osc || !A.r || !isZeroQ(A.L.mag) ? A.e : addE(A.e, A.r.e), L: new Iv(ZERO, upperEnv(A, ctx).C), osc: true, r: null };
        }
        case "sin":
          if (s > 0) return { e: E0, L: new Iv(ONE.negate(), ONE), osc: true, r: null };
          return s < 0 ? small("sin", A, ctx) : applyF("sin", A, ctx);
        case "cos":
          if (s > 0) return { e: E0, L: new Iv(ONE.negate(), ONE), osc: true, r: null };
          return applyF("cos", finite(A, ctx), ctx);
        case "tan":
          if (s > 0) refuse("undecided", "tan of a growing argument has poles all the way out");
          return s < 0 ? small("tan", A, ctx) : applyF("tan", A, ctx);
        case "asin":
          if (s > 0) refuse("domain", "asin of a growing argument is not defined");
          return s < 0 ? small("asin", A, ctx) : applyF("asin", A, ctx);
        case "acos":
          if (s > 0) refuse("domain", "acos of a growing argument is not defined");
          return applyF("acos", finite(A, ctx), ctx);
        case "atan":
          return saturating("atan", A, ctx, R(encloseAst(op("/", PI, num(2)), {}, ctx.bits), ctx));
        case "tanh":
          return saturating("tanh", A, ctx, Iv.point(ONE));
        case "erf":
          return saturating("erf", A, ctx, Iv.point(ONE), R(encloseAst(op("/", num(2), call("sqrt", PI)), {}, ctx.bits), ctx));
        case "log1p":
          return s < 0 ? small("log1p", A, ctx) : logNode(add(constNode(Iv.point(ONE)), A, ctx), ctx);
        case "sinh":
        case "cosh": {
          if (s < 0 && name === "sinh") return small("sinh", A, ctx);
          if (s <= 0) return applyF(name, finite(A, ctx), ctx);
          const half = constNode(Iv.point(new Rational(1n, 2n)));
          const plus = go(call("exp", arg));
          const minus = go(call("exp", op("neg", arg)));
          return mul(half, add(plus, name === "sinh" ? neg(minus) : minus, ctx), ctx);
        }
      }
      break;
    }
  }
  return refuse("undecided", `${ast.op ?? ast.name ?? ast.type} is not followed out to infinity`);
}

/** 1/ast as a node: exponentials are negated in place so that 1/e^(x²) is not a division by something unbounded. */
function recipAst(ast, ctx) {
  if (ast.type === "call" && ast.name === "exp") return evalNode(call("exp", op("neg", ast.args[0])), ctx);
  if (ast.type === "op" && ast.op === "*") return mul(recipAst(ast.args[0], ctx), recipAst(ast.args[1], ctx), ctx);
  if (ast.type === "op" && ast.op === "/") return mul(recipAst(ast.args[0], ctx), evalNode(ast.args[1], ctx), ctx);
  if (ast.type === "op" && ast.op === "^") {
    const c = constantRational(ast.args[1]);
    if (c !== null && ast.args[0].type === "call" && ast.args[0].name === "exp") return evalNode(call("exp", op("*", num(c.negate()), ast.args[0].args[0])), ctx);
    if (c !== null && c.numerator > 0n && c.denominator !== 1n) return powNode(evalNode(ast.args[0], ctx), c.negate(), ctx);
  }
  return recip(evalNode(ast, ctx), ctx);
}

/** The context for the ray [X, ∞). */
export function rayContext(name, env, X, bits) {
  return { name, env, X, bits, logX: encloseAst(call("log", num(X)), {}, bits) };
}
/** The node of `ast` on [X, ∞). Throws AnalyticError "larger-x" when X is too small for a bound. */
export function nodeAt(ast, ctx) {
  return evalNode(ast, ctx);
}

/** The values of X tried in turn, starting past `from`. */
export function* rays(from = ZERO) {
  let base = 4n;
  while (le(new Rational(base), from)) base *= 2n;
  for (let i = 0; i < 9; i++) yield new Rational(base << BigInt(i));
  for (const s of [16n, 32n, 64n, 128n, 256n]) yield new Rational(base << s);
}

/** Runs `use(node, ctx)` on the first ray where every bound holds. */
export function onRay(ast, name, env, bits, use, from = ZERO) {
  let last = null;
  for (const X of rays(from)) {
    const ctx = rayContext(name, env, X, bits);
    try {
      const out = use(evalNode(ast, ctx), ctx);
      if (out !== undefined) return out;
    } catch (e) {
      if (!(e instanceof AnalyticError) || (e.code !== "larger-x" && e.code !== "overflow")) throw e;
      last = e;
    }
  }
  return refuse("undecided", `the behaviour of ${format(ast)} at infinity could not be bounded${last ? ` (${last.message})` : ""}`);
}

// ---- limits -----------------------------------------------------------------------------------

/**
 * lim_{x→∞} ast. Returns { kind: "finite", iv } with the limit inside iv,
 * or { kind: "infinite", sign }. Refuses with "no-limit" where the function
 * keeps oscillating, "undecided" where no bound was found.
 */
export function limitAtInfinity(ast, name, env, bits) {
  return onRay(ast, name, env, bits, (found, ctx) => {
    // leading terms that cancelled leave only a bound
    const node = !found.osc && found.r && isZeroQ(found.L.mag)
      ? { e: addE(found.e, found.r.e), L: new Iv(found.r.C.negate(), found.r.C), osc: true, r: null }
      : found;
    const s = signE(node.e);
    if (s < 0) {
      upperEnv(node, ctx); // the bound must hold on this ray
      return { kind: "finite", iv: Iv.point(ZERO), node };
    }
    if (s === 0) {
      if (node.osc) {
        if (node.L.isPoint) return { kind: "finite", iv: node.L, node };
        refuse("no-limit", `no limit could be proven: ${format(ast)} may keep oscillating, or its leading terms cancel`);
      }
      spread(node, ctx);
      return { kind: "finite", iv: node.L, node };
    }
    const S = spread(node, ctx);
    if (S.containsZero()) {
      if (!node.osc && !node.L.containsZero()) larger("the sign is not yet settled");
      refuse("no-limit", `no limit could be proven: ${format(ast)} grows without settling on a sign`);
    }
    return { kind: "infinite", sign: gt(S.lo, ZERO) ? 1 : -1, node };
  });
}

/** A readable form of the leading behaviour: { exp, power, log, coefficient, oscillates, text }. */
export function describeNode(node, name = "x") {
  const parts = [];
  const q = (x) => (x.denominator === 1n ? `${x.numerator}` : `(${x})`);
  if (!isZeroQ(node.e.k)) parts.push(`exp(${node.e.k.equals(ONE) ? "" : node.e.k.equals(ONE.negate()) ? "-" : `${q(node.e.k)}*`}${name})`);
  if (!isZeroQ(node.e.p)) parts.push(node.e.p.equals(ONE) ? name : `${name}^${q(node.e.p)}`);
  if (!isZeroQ(node.e.m)) parts.push(node.e.m.equals(ONE) ? `log(${name})` : `log(${name})^${q(node.e.m)}`);
  return {
    exp: node.e.k,
    power: node.e.p,
    log: node.e.m,
    coefficient: node.L.toRationalInterval(),
    oscillates: node.osc,
    term: parts.join("*") || "1",
  };
}

// ---- tails of integrals ---------------------------------------------------------------------------

/** Whether ∫^∞ of the term converges. */
function integrable(e) {
  if (!isZeroQ(e.k)) return e.k.numerator < 0n;
  const c = e.p.compareTo(ONE.negate());
  if (c !== 0) return c < 0;
  return lt(e.m, ONE.negate());
}

/** ∫_X^∞ of the term in closed form, where there is one. */
function termTail(e, ctx) {
  const zk = isZeroQ(e.k);
  const zp = isZeroQ(e.p);
  const zm = isZeroQ(e.m);
  if (zk && zm) return termAt({ k: ZERO, p: e.p.add(ONE), m: ZERO }, ctx).scale(e.p.add(ONE).negate().reciprocal());
  if (zp && zm) return termAt(e, ctx).scale(e.k.negate().reciprocal());
  if (zk && e.p.equals(ONE.negate())) return termAt({ k: ZERO, p: ZERO, m: e.m.add(ONE) }, ctx).scale(e.m.add(ONE).negate().reciprocal());
  const whole = (x) => x.denominator === 1n && x.numerator > 0n && x.numerator <= 16n;
  if (zk && whole(e.m)) {
    // by parts: ∫ x^p·log^m = X^(p+1)·log^m X/(−p−1) + m/(−p−1)·∫ x^p·log^(m−1)
    const c = e.p.add(ONE).negate().reciprocal();
    const lower = termTail({ k: ZERO, p: e.p, m: e.m.subtract(ONE) }, ctx);
    return termAt({ k: ZERO, p: e.p.add(ONE), m: e.m }, ctx).scale(c).add(lower.scale(e.m.multiply(c)));
  }
  if (zm && whole(e.p)) {
    // by parts: ∫ x^p·e^(k·x) = X^p·e^(k·X)/(−k) + p/(−k)·∫ x^(p−1)·e^(k·x)
    const c = e.k.negate().reciprocal();
    const lower = termTail({ k: e.k, p: e.p.subtract(ONE), m: ZERO }, ctx);
    return termAt(e, ctx).scale(c).add(lower.scale(e.p.multiply(c)));
  }
  return null;
}

/** An upper bound of ∫_X^∞ C·term. */
function tailUpper(env, ctx) {
  const { e, C } = env;
  const exact = termTail(e, ctx);
  if (exact) return exact.hi.multiply(C);
  if (e.k.numerator < 0n) {
    // term = [e^(k·x/2)·x^p·log^m]·e^(k·x/2), the bracket decreasing
    const half = { k: e.k.divide(TWO), p: e.p, m: e.m };
    if (!decreasing(half, ctx)) larger("a tail bound does not hold this early");
    return C.multiply(termAt(e, ctx).hi).multiply(TWO).divide(e.k.negate());
  }
  // k = 0, p < −1, m ≠ 0: split off x^p′ with p′ = (p − 1)/2 < −1
  const p2 = e.p.subtract(ONE).divide(TWO);
  if (!decreasing({ k: ZERO, p: e.p.subtract(p2), m: e.m }, ctx)) larger("a tail bound does not hold this early");
  return C.multiply(termAt({ k: ZERO, p: e.p.add(ONE), m: e.m }, ctx).hi).divide(p2.add(ONE).negate());
}

/**
 * The tail ∫_X^∞ of a node: { kind: "converges", iv } or
 * { kind: "diverges", sign }. Refuses with "undecided" where the bound found
 * is not integrable and the sign is not constant (sin(x)/x).
 */
export function tailOf(node, ctx, text = "the integrand") {
  const ub = upperEnv(node, ctx);
  if (integrable(ub.e)) {
    if (!node.osc && !isZeroQ(node.L.mag)) {
      const I = termTail(node.e, ctx);
      if (I) {
        const rest = node.r ? tailUpper({ C: node.r.C, e: addE(node.e, node.r.e) }, ctx) : ZERO;
        return { kind: "converges", iv: R(node.L.mul(I).add(new Iv(rest.negate(), rest)), ctx) };
      }
    }
    const U = up(tailUpper(ub, ctx), ctx);
    const S = spread(node, ctx);
    // `loose`: only a bound, which narrows slowly as X grows
    return { kind: "converges", loose: true, oscillates: node.osc, iv: ge(S.lo, ZERO) ? new Iv(ZERO, U) : le(S.hi, ZERO) ? new Iv(U.negate(), ZERO) : new Iv(U.negate(), U) };
  }
  const S = spread(node, ctx);
  if (!S.containsZero()) return { kind: "diverges", sign: gt(S.lo, ZERO) ? 1 : -1 };
  if (!node.osc && !node.L.containsZero()) larger("the sign is not yet settled");
  return refuse("undecided", `could not decide whether the integral converges: ${text} may change sign for ever while its size is not integrable`);
}

// the pieces series and sequences are built from (src/sequences.js)
export { signE, spread, upperEnv, envAt, decreasing, tailUpper, termAt, integrable };
