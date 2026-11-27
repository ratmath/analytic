// Expressions: the same plain AST and calculator grammar as @ratmath/graphics
// (src/expr.js there), so one parse tree can be plotted, modelled and
// differentiated. The parser below follows graphics' grammar; keep the two in
// sync until it moves to a shared package. Analytic adds atan, log1p, sinh,
// cosh and tanh to the function names.
//
//   { type: "num", value: Rational }
//   { type: "var", name }
//   { type: "const", name: "pi" | "e" }
//   { type: "op", op: "+" | "-" | "*" | "/" | "neg" | "^", args }
//   { type: "call", name, args }
//
// Three things are built from a tree here:
//   compileFloat(ast)      (env) => number          fast previews
//   modelOf(ast, env, base)  Taylor model             certified
//   derivative(ast, name)  a new tree                symbolic d/d(name)

import { Rational } from "@ratmath/core";
import { refuse } from "./errors.js";
import { TaylorModel } from "./model.js";
import * as E from "./elementary.js";
import { constants } from "./enclose.js";
import { Iv } from "./interval.js";
import { ZERO, ONE, le, ge, isZero } from "./rat.js";
import { gammaFloat, lgammaFloat, digammaFloat, trigammaFloat, besselJFloat, siFloat, fresnelSFloat, fresnelCFloat } from "./special.js";

// ---- AST builders ------------------------------------------------------------

export const num = (value) => ({ type: "num", value: toRational(value) });
export const v = (name) => ({ type: "var", name });
export const op = (o, ...args) => ({ type: "op", op: o, args });
export const call = (name, ...args) => ({ type: "call", name, args });

export function toRational(value) {
  if (value instanceof Rational) return value;
  if (typeof value === "bigint") return new Rational(value);
  if (typeof value === "number") {
    if (!Number.isFinite(value)) throw new RangeError(`not a finite number: ${value}`);
    return parseDecimalString(String(value)); // shortest spelling: 0.1 is 1/10
  }
  if (typeof value === "string") return parseDecimalString(value.trim());
  if (value && typeof value.numerator === "bigint") return new Rational(value.numerator, value.denominator);
  throw new TypeError(`cannot read ${value} as a rational`);
}

function parseDecimalString(s) {
  const frac = /^([+-]?\d+)\s*\/\s*(\d+)$/.exec(s);
  if (frac) return new Rational(BigInt(frac[1]), BigInt(frac[2]));
  const m = /^([+-]?)(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/.exec(s);
  if (!m || (m[2] === "" && (m[3] ?? "") === "")) throw new SyntaxError(`not a number: ${s}`);
  const digits = (m[2] || "0") + (m[3] ?? "");
  let n = BigInt(digits) * (m[1] === "-" ? -1n : 1n);
  let d = 10n ** BigInt((m[3] ?? "").length);
  const e = m[4] ? Number(m[4]) : 0;
  if (e > 0) n *= 10n ** BigInt(e);
  else if (e < 0) d *= 10n ** BigInt(-e);
  return new Rational(n, d);
}

// ---- parser (graphics' grammar) -------------------------------------------------

export const FUNCTIONS = new Set([
  "sin", "cos", "tan", "exp", "ln", "log", "sqrt", "abs", "min", "max",
  "atan", "log1p", "sinh", "cosh", "tanh", "asin", "acos", "cbrt", "erf",
  "gamma", "lgamma", "digamma", "trigamma", "beta", "besselJ", "Si", "fresnelS", "fresnelC", "erfc",
  // switches for the Laplace transform tools: a unit step and a unit impulse at 0
  "heaviside", "dirac",
]);
/** Functions of two arguments. */
const BINARY = new Set(["min", "max", "beta", "besselJ"]);
/** Calls that are written out in terms of others as they are read. */
function specialCall(name, args, text) {
  if (BINARY.has(name) !== (args.length === 2)) throw new SyntaxError(`${name} takes ${BINARY.has(name) ? "two arguments" : "one argument"} in ${text}`);
  if (name === "erfc") return op("-", num(1), call("erf", args[0]));
  if (name === "beta") return op("/", op("*", call("gamma", args[0]), call("gamma", args[1])), call("gamma", op("+", args[0], args[1])));
  if (name === "besselJ") {
    const n = constantRational(args[0]);
    if (n === null || n.denominator !== 1n) throw new SyntaxError(`besselJ(n, x) needs a whole number n in ${text}`);
    return call("besselJ", num(n), args[1]);
  }
  return call(name, ...args);
}
const ALIASES = { arcsin: "asin", arccos: "acos", arctan: "atan", arcsinh: "asinh", arccosh: "acosh", arctanh: "atanh" };
const ONE_ = () => num(1);
/** Functions read as they are written out in terms of the built-in ones. */
const REWRITES = {
  sec: (u) => op("/", ONE_(), call("cos", u)),
  csc: (u) => op("/", ONE_(), call("sin", u)),
  cot: (u) => op("/", call("cos", u), call("sin", u)),
  sech: (u) => op("/", ONE_(), call("cosh", u)),
  csch: (u) => op("/", ONE_(), call("sinh", u)),
  coth: (u) => op("/", call("cosh", u), call("sinh", u)),
  asinh: (u) => call("log", op("+", u, call("sqrt", op("+", op("^", u, num(2)), ONE_())))),
  acosh: (u) => call("log", op("+", u, call("sqrt", op("-", op("^", u, num(2)), ONE_())))),
  atanh: (u) => op("/", call("log", op("/", op("+", ONE_(), u), op("-", ONE_(), u))), num(2)),
};
export const CONSTANTS = new Set(["pi", "e"]);

/**
 * Parse calculator notation: + - * / ^ (or **), parentheses, unary minus,
 * implicit multiplication after a number or factor (`2x`, `3(x+1)`,
 * `2sin(x)`), decimals as exact rationals. `^` is right-associative and binds
 * tighter than unary minus: `-x^2` is `-(x^2)`. `log` is the natural log.
 */
export function parse(text) {
  const toks = tokenize(text);
  let i = 0;
  const peek = () => toks[i];
  const next = () => toks[i++];
  const expect = (t) => {
    const k = next();
    if (!k || k.t !== t) throw new SyntaxError(`expected ${t} at ${k ? k.pos : text.length} in ${text}`);
    return k;
  };
  function expr() {
    let left = term();
    while (peek() && (peek().t === "+" || peek().t === "-")) {
      const o = next().t;
      left = op(o, left, term());
    }
    return left;
  }
  const startsFactor = (k) => k && (k.t === "num" || k.t === "name" || k.t === "(");
  function term() {
    let left = unary();
    for (;;) {
      const k = peek();
      if (k && (k.t === "*" || k.t === "/")) {
        next();
        left = op(k.t, left, unary());
      } else if (startsFactor(k)) {
        left = op("*", left, power());
      } else return left;
    }
  }
  function unary() {
    if (peek() && peek().t === "-") {
      next();
      return op("neg", unary());
    }
    if (peek() && peek().t === "+") {
      next();
      return unary();
    }
    return power();
  }
  function power() {
    const base = primary();
    if (peek() && peek().t === "^") {
      next();
      return op("^", base, unary());
    }
    return base;
  }
  function primary() {
    const k = next();
    if (!k) throw new SyntaxError(`unexpected end of ${text}`);
    if (k.t === "num") return { type: "num", value: parseDecimalString(k.v) };
    if (k.t === "(") {
      const e = expr();
      expect(")");
      return e;
    }
    if (k.t === "name") {
      if (ALIASES[k.v]) k.v = ALIASES[k.v];
      // "sinx", "lnx": a function name run together with x
      if (!FUNCTIONS.has(k.v) && k.v.endsWith("x") && FUNCTIONS.has(k.v.slice(0, -1)) && !(peek() && peek().t === "(")) {
        return call(k.v.slice(0, -1), v("x"));
      }
      if (FUNCTIONS.has(k.v)) {
        if (peek() && peek().t === "(") {
          next();
          const args = [expr()];
          while (peek() && peek().t === ",") {
            next();
            args.push(expr());
          }
          expect(")");
          return specialCall(k.v, args, text);
        }
        return specialCall(k.v, [power()], text);
      }
      if (REWRITES[k.v]) {
        if (peek() && peek().t === "(") {
          next();
          const arg = expr();
          if (peek() && peek().t === ",") throw new SyntaxError(`${k.v} takes one argument in ${text}`);
          expect(")");
          return REWRITES[k.v](arg);
        }
        return REWRITES[k.v](power());
      }
      if (CONSTANTS.has(k.v)) return { type: "const", name: k.v };
      // a name of three or more letters written against "(" is a function call, not a product:
      // refuse one that is not known rather than read sec(x) as sec·x
      if (k.v.length >= 3 && peek() && peek().t === "(" && peek().pos === k.pos + k.v.length) {
        throw new SyntaxError(`unknown function ${k.v} at ${k.pos} in ${text} (write a product with *)`);
      }
      return v(k.v);
    }
    throw new SyntaxError(`unexpected ${k.t} at ${k.pos} in ${text}`);
  }
  const result = expr();
  if (i < toks.length) throw new SyntaxError(`unexpected ${toks[i].t} at ${toks[i].pos} in ${text}`);
  return result;
}

function tokenize(text) {
  const out = [];
  const re = /\s*(?:(\d+\.?\d*(?:[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?)|([A-Za-z][A-Za-z0-9_]*)|(\*\*|[-+*/^(),]))/y;
  let pos = 0;
  while (pos < text.length) {
    if (/^\s*$/.test(text.slice(pos))) break;
    re.lastIndex = pos;
    const m = re.exec(text);
    if (!m) throw new SyntaxError(`cannot read ${JSON.stringify(text.slice(pos))}`);
    const at = m.index + (m[0].length - (m[1] ?? m[2] ?? m[3]).length);
    if (m[1] && /^[.\d]/.test(text.slice(re.lastIndex)) && /\./.test(m[1])) {
      throw new SyntaxError(`a number with two decimal points at ${at} in ${text}`);
    }
    if (m[1]) out.push({ t: "num", v: m[1], pos: at });
    else if (m[2]) out.push({ t: "name", v: m[2], pos: at });
    else out.push({ t: m[3] === "**" ? "^" : m[3], pos: at });
    pos = re.lastIndex;
  }
  return out;
}

/** A tree from a string or a tree (checked lightly). */
export function toAst(x) {
  if (typeof x === "string") return parse(x);
  if (x && typeof x === "object" && typeof x.type === "string") return x;
  throw new TypeError("expected an expression string or AST");
}

/** Names used as variables (excluding functions and constants). */
export function freeVariables(ast, out = new Set()) {
  if (ast.type === "var") out.add(ast.name);
  else if (ast.args) for (const a of ast.args) freeVariables(a, out);
  return out;
}

/** The value of a tree with no variables and no pi/e or functions, else null. */
export function constantRational(ast) {
  switch (ast.type) {
    case "num":
      return ast.value;
    case "op": {
      const a = ast.args.map(constantRational);
      if (a.some((q) => q === null)) return null;
      switch (ast.op) {
        case "+": return a[0].add(a[1]);
        case "-": return a[0].subtract(a[1]);
        case "*": return a[0].multiply(a[1]);
        case "/": return isZero(a[1]) ? null : a[0].divide(a[1]);
        case "neg": return a[0].negate();
        case "^": {
          if (a[1].denominator !== 1n) return null;
          const k = Number(a[1].numerator);
          if (Math.abs(k) > 4096 || (k <= 0 && isZero(a[0]))) return null;
          return a[0].pow(k);
        }
      }
    }
  }
  return null;
}

// ---- printing ------------------------------------------------------------------

const PREC = { "+": 1, "-": 1, "*": 2, "/": 2, neg: 3, "^": 4 };

/** Calculator notation that parses back to the same tree. */
export function format(ast) {
  const go = (n, outer = 0, rightSide = false) => {
    let s;
    let p;
    switch (n.type) {
      case "num": {
        const q = n.value;
        s = q.denominator === 1n ? q.numerator.toString() : `${q.numerator}/${q.denominator}`;
        // a negative number prints like a negation; a fraction like a quotient
        p = q.denominator !== 1n ? 2 : q.numerator < 0n ? 3 : 5;
        break;
      }
      case "var":
      case "const":
        s = n.name;
        p = 5;
        break;
      case "call":
        s = `${n.name}(${n.args.map((a) => go(a)).join(", ")})`;
        p = 5;
        break;
      case "op": {
        p = PREC[n.op];
        if (n.op === "neg") s = `-${go(n.args[0], 3)}`;
        else if (n.op === "^") s = `${go(n.args[0], 5)}^${go(n.args[1], 3)}`;
        else {
          const sym = n.op === "*" ? "*" : ` ${n.op} `;
          const l = go(n.args[0], p);
          const r = go(n.args[1], p, true);
          s = n.op === "*" || n.op === "/" ? `${l}${n.op === "*" ? "*" : "/"}${r}` : `${l}${sym}${r}`;
        }
        break;
      }
    }
    const needs = p < outer || (rightSide && p === outer && (outer === 1 || outer === 2));
    return needs ? `(${s})` : s;
  };
  return go(ast);
}

// ---- float compiler ------------------------------------------------------------

/** erf on doubles: the power series below 3, the continued fraction for erfc beyond. */
export function erfFloat(x) {
  const a = Math.abs(x);
  let r;
  if (a < 3) {
    let term = a;
    let sum = a;
    for (let k = 1; k < 120; k++) {
      term *= (-a * a) / k;
      sum += term / (2 * k + 1);
    }
    r = (2 / Math.sqrt(Math.PI)) * sum;
  } else {
    let f = 0;
    for (let k = 60; k >= 1; k--) f = k / 2 / (a + f);
    r = 1 - Math.exp(-a * a) / Math.sqrt(Math.PI) / (a + f);
  }
  return x < 0 ? -r : r;
}

const FLOAT_FNS = {
  sin: Math.sin, cos: Math.cos, tan: Math.tan, exp: Math.exp, ln: Math.log, log: Math.log,
  sqrt: Math.sqrt, abs: Math.abs, atan: Math.atan, log1p: Math.log1p,
  sinh: Math.sinh, cosh: Math.cosh, tanh: Math.tanh,
  asin: Math.asin, acos: Math.acos, cbrt: Math.cbrt, erf: erfFloat,
  gamma: gammaFloat, lgamma: lgammaFloat, digamma: digammaFloat, trigamma: trigammaFloat,
  Si: siFloat, fresnelS: fresnelSFloat, fresnelC: fresnelCFloat,
};

/** Compile to a closure over doubles: (env) => number, env maps names to numbers. */
export function compileFloat(ast) {
  const go = (n) => {
    switch (n.type) {
      case "num": {
        const c = n.value.toNumber();
        return () => c;
      }
      case "const": {
        const c = n.name === "pi" ? Math.PI : Math.E;
        return () => c;
      }
      case "var": {
        const name = n.name;
        return (env) => {
          const x = env[name];
          if (x === undefined) throw new ReferenceError(`no value for ${name}`);
          return x;
        };
      }
      case "op": {
        const [a, b] = n.args.map(go);
        switch (n.op) {
          case "+": return (e) => a(e) + b(e);
          case "-": return (e) => a(e) - b(e);
          case "*": return (e) => a(e) * b(e);
          case "/": return (e) => a(e) / b(e);
          case "neg": return (e) => -a(e);
          case "^": {
            // an odd root of a negative base is real: (−8)^(1/3) = −2, where Math.pow gives NaN
            const q = constantRational(n.args[1]);
            if (q !== null && q.denominator !== 1n && q.denominator % 2n === 1n) {
              const ex = q.toNumber();
              const sgn = q.numerator % 2n === 0n ? 1 : -1;
              return (e) => {
                const x = a(e);
                return x < 0 ? sgn * Math.pow(-x, ex) : Math.pow(x, ex);
              };
            }
            return (e) => Math.pow(a(e), b(e));
          }
        }
        break;
      }
      case "call": {
        const [a, b] = n.args.map(go);
        const f = FLOAT_FNS[n.name];
        if (f) return (e) => f(a(e));
        if (n.name === "besselJ") {
          const order = Number(n.args[0].value.numerator);
          return (e) => besselJFloat(order, b(e));
        }
        if (n.name === "min") return (e) => Math.min(a(e), b(e));
        if (n.name === "max") return (e) => Math.max(a(e), b(e));
        break;
      }
    }
    throw new Error(`cannot compile ${n.type} ${n.op ?? n.name ?? ""}`);
  };
  return go(ast);
}

/** Plain-number copy of a parameter map (Rationals, strings, intervals → midpoints). */
export function floatEnv(params = {}) {
  const out = {};
  for (const [k, val] of Object.entries(params)) {
    if (typeof val === "number") out[k] = val;
    else {
      const iv = Iv.from(typeof val === "string" ? toRational(val) : val);
      out[k] = iv.mid.toNumber();
    }
  }
  return out;
}

// ---- Taylor-model compiler -----------------------------------------------------

/**
 * Taylor model of the tree. env maps names to Taylor models, Rationals or
 * intervals; `base` is any model on the target domain (its domain, order and
 * bits are used for constants).
 */
export function modelOf(ast, env, base) {
  const settings = { order: base.order, bits: base.bits };
  const lift = (val) => (val instanceof TaylorModel ? val : TaylorModel.constant(base.domain, val, settings));
  const go = (n) => {
    switch (n.type) {
      case "num":
        return lift(n.value);
      case "const":
        return lift(n.name === "pi" ? constants.pi(base.bits + 8) : constants.e(base.bits + 8));
      case "var": {
        const val = env[n.name];
        if (val === undefined) refuse("unbound", `no value for ${n.name}`);
        return lift(typeof val === "string" ? toRational(val) : val);
      }
      case "op": {
        if (n.op === "^") return powerOf(n);
        const [a, b] = n.args.map(go);
        switch (n.op) {
          case "+": return a.add(b);
          case "-": return a.subtract(b);
          case "*": return a.multiply(b);
          case "/": return a.divide(b);
          case "neg": return a.negate();
        }
        break;
      }
      case "call": {
        const args = n.args.map(go);
        const [a, b] = args;
        switch (n.name) {
          case "ln":
          case "log": return E.log(a);
          case "abs": {
            const r = a.bound(4);
            if (ge(r.lo, ZERO)) return a;
            if (le(r.hi, ZERO)) return a.negate();
            return refuse("not-smooth", `abs is not smooth here: its argument's range ${r} contains 0; split the domain at the zero`);
          }
          case "min":
          case "max": {
            const r = a.subtract(b).bound(4);
            const aBig = ge(r.lo, ZERO);
            const bBig = le(r.hi, ZERO);
            if (!aBig && !bBig) return refuse("not-smooth", `${n.name} is not smooth here: its arguments cross; split the domain where they meet`);
            return (n.name === "max") === aBig ? a : b;
          }
          default:
            if (E[n.name]) return E[n.name](a);
        }
        break;
      }
    }
    return refuse("bad-expression", `cannot model ${n.type} ${n.op ?? n.name ?? ""}`);
  };
  const powerOf = (n) => {
    const q = constantRational(n.args[1]);
    const a = go(n.args[0]);
    if (q !== null) {
      if (isZero(q)) {
        const r = a.bound(4);
        if (r.containsZero()) refuse("zero-power", "0^0 is undefined: the base of ^0 can be 0 on this domain");
        return lift(ONE);
      }
      return E.power(a, q);
    }
    return E.exp(go(n.args[1]).multiply(E.log(a)));
  };
  return go(ast);
}

// ---- symbolic derivative -------------------------------------------------------

const ZN = () => num(0n);
const ON = () => num(1n);
const isNum = (n, q) => n.type === "num" && (q === undefined || n.value.compareTo(toRational(q)) === 0);

// Builders that fold constants and drop identities, so derivatives stay readable.
export const S = {
  add(a, b) {
    if (isNum(a, 0)) return b;
    if (isNum(b, 0)) return a;
    if (a.type === "num" && b.type === "num") return num(a.value.add(b.value));
    if (b.type === "op" && b.op === "neg") return S.sub(a, b.args[0]);
    if (b.type === "num" && b.value.numerator < 0n) return S.sub(a, num(b.value.negate()));
    return op("+", a, b);
  },
  sub(a, b) {
    if (isNum(b, 0)) return a;
    if (isNum(a, 0)) return S.neg(b);
    if (a.type === "num" && b.type === "num") return num(a.value.subtract(b.value));
    if (b.type === "op" && b.op === "neg") return S.add(a, b.args[0]);
    if (b.type === "num" && b.value.numerator < 0n) return S.add(a, num(b.value.negate()));
    return op("-", a, b);
  },
  neg(a) {
    if (a.type === "num") return num(a.value.negate());
    if (a.type === "op" && a.op === "neg") return a.args[0];
    return op("neg", a);
  },
  mul(a, b) {
    if (isNum(a, 0) || isNum(b, 0)) return ZN();
    if (isNum(a, 1)) return b;
    if (isNum(b, 1)) return a;
    if (isNum(a, -1)) return S.neg(b);
    if (isNum(b, -1)) return S.neg(a);
    if (a.type === "num" && b.type === "num") return num(a.value.multiply(b.value));
    if (b.type === "num") return S.mul(b, a);
    if (a.type === "op" && a.op === "neg") return S.neg(S.mul(a.args[0], b));
    if (b.type === "op" && b.op === "neg") return S.neg(S.mul(a, b.args[0]));
    return op("*", a, b);
  },
  div(a, b) {
    if (isNum(a, 0)) return ZN();
    if (isNum(b, 1)) return a;
    if (a.type === "num" && b.type === "num" && !isZero(b.value)) return num(a.value.divide(b.value));
    if (a.type === "op" && a.op === "neg") return S.neg(S.div(a.args[0], b));
    if (a.type === "num" && a.value.numerator < 0n) return S.neg(S.div(num(a.value.negate()), b));
    return op("/", a, b);
  },
  pow(a, b) {
    if (isNum(b, 1)) return a;
    // (a^m)^n = a^(mn) for integers m, n
    if (a.type === "op" && a.op === "^" && a.args[1].type === "num" && b.type === "num" &&
        a.args[1].value.denominator === 1n && b.value.denominator === 1n) {
      return S.pow(a.args[0], num(a.args[1].value.multiply(b.value)));
    }
    return op("^", a, b);
  },
};

const depends = (n, name) => freeVariables(n).has(name);

const TOTAL_CALLS = new Set(["sin", "cos", "exp", "atan", "sinh", "cosh", "tanh", "abs", "min", "max", "cbrt", "erf", "besselJ", "Si", "fresnelS", "fresnelC"]);

/** True when the tree is defined for every real value of its variables (no division, log, root or tan). */
export function isTotal(n) {
  if (n.type === "num" || n.type === "var" || n.type === "const") return true;
  if (n.type === "call") return TOTAL_CALLS.has(n.name) && n.args.every(isTotal);
  if (n.op === "/") return false;
  if (n.op === "^") {
    const e = n.args[1];
    return e.type === "num" && e.value.denominator === 1n && e.value.numerator > 0n && isTotal(n.args[0]);
  }
  return n.args.every(isTotal);
}

const sameTree = (a, b) => format(a) === format(b);

/**
 * Algebraic clean-up that never changes where a formula is defined: constants
 * folded, 0 and 1 dropped, products flattened with like factors merged
 * (3·(2x)·x = 6x^2), sums flattened with like terms merged (2u + 3u = 5u,
 * u − u = 0 only when u is defined everywhere). Quotients keep their
 * denominators: u/u stays, since it is undefined where u = 0.
 */
export function simplify(ast) {
  const isPosInt = (e) => e.type === "num" && e.value.denominator === 1n && e.value.numerator > 0n;
  /** [coefficient, core tree or null] of a simplified term. */
  const split = (t) => {
    if (t.type === "num") return [t.value, null];
    if (t.type === "op" && t.op === "neg") {
      const [c, core] = split(t.args[0]);
      return [c.negate(), core];
    }
    if (t.type === "op" && t.op === "*") {
      // products are built left to right with the number first: ((2·a)·x)
      const fs = [];
      const flat = (u) => (u.type === "op" && u.op === "*" ? u.args.forEach(flat) : fs.push(u));
      flat(t);
      if (fs[0].type === "num" && fs.length > 1) return [fs[0].value, fs.slice(1).reduce((acc, f) => op("*", acc, f))];
    }
    return [ONE, t];
  };
  /** c·rest as a left-to-right product with the number first, so it prints as 2*a*x. */
  const withCoef = (c, rest) => {
    if (isZero(c.subtract(ONE))) return rest;
    if (isZero(c.add(ONE))) return op("neg", rest);
    const fs = [];
    const flat = (u) => (u.type === "op" && u.op === "*" ? u.args.forEach(flat) : fs.push(u));
    flat(rest);
    return fs.reduce((acc, f) => op("*", acc, f), num(c));
  };
  const product = (n) => {
    let c = ONE;
    const fs = []; // { base, k }
    let keepZero = false;
    const push = (base, k) => {
      const hit = fs.find((f) => sameTree(f.base, base));
      if (hit) hit.k += k;
      else fs.push({ base, k });
    };
    const walk = (t) => {
      if (t.type === "op" && t.op === "*") return t.args.forEach(walk);
      if (t.type === "op" && t.op === "neg") {
        c = c.negate();
        return walk(t.args[0]);
      }
      const g = go(t);
      if (g.type === "num") c = c.multiply(g.value);
      else if (g.type === "op" && (g.op === "*" || g.op === "neg")) walk(g);
      else if (g.type === "op" && g.op === "^" && isPosInt(g.args[1]) && g.args[1].value.numerator < 1000n) push(g.args[0], Number(g.args[1].value.numerator));
      else push(g, 1);
    };
    n.args.forEach(walk);
    let rest = null;
    for (const f of fs) {
      const t = f.k === 1 ? f.base : op("^", f.base, num(BigInt(f.k)));
      rest = rest ? op("*", rest, t) : t;
      if (!isTotal(f.base)) keepZero = true;
    }
    if (!rest) return num(c);
    if (isZero(c)) return keepZero ? op("*", ZN(), rest) : ZN();
    return withCoef(c, rest);
  };
  const sum = (n) => {
    const terms = []; // { c, core }
    let constant = ZERO;
    const walk = (t, sgn) => {
      if (t.type === "op" && t.op === "+") {
        walk(t.args[0], sgn);
        return walk(t.args[1], sgn);
      }
      if (t.type === "op" && t.op === "-") {
        walk(t.args[0], sgn);
        return walk(t.args[1], -sgn);
      }
      if (t.type === "op" && t.op === "neg") return walk(t.args[0], -sgn);
      const g = go(t);
      if (g.type === "op" && (g.op === "+" || g.op === "-")) return walk(g, sgn);
      let [c, core] = split(g);
      if (sgn < 0) c = c.negate();
      if (core === null) {
        if (!terms.some((x) => x.core === null)) terms.push({ c: ZERO, core: null }); // the constant keeps its place
        constant = constant.add(c);
      } else {
        const hit = terms.find((x) => x.core !== null && sameTree(x.core, core));
        if (hit) hit.c = hit.c.add(c);
        else terms.push({ c, core });
      }
    };
    walk(n, 1);
    let out = null;
    for (const term of terms) {
      const core = term.core;
      const c = core === null ? constant : term.c;
      if (core === null) {
        if (isZero(c)) continue;
        const mag = num(c.abs());
        if (!out) out = num(c);
        else out = c.numerator < 0n ? op("-", out, mag) : op("+", out, mag);
        continue;
      }
      if (isZero(c)) {
        if (isTotal(core)) continue;
        const z = op("*", ZN(), core);
        out = out ? op("+", out, z) : z;
        continue;
      }
      const mag = withCoef(c.abs(), core);
      if (!out) out = withCoef(c, core);
      else out = c.numerator < 0n ? op("-", out, mag) : op("+", out, mag);
    }
    return out ?? ZN();
  };
  const go = (n) => {
    if (n.type !== "op" && n.type !== "call") return n;
    if (n.type === "call") return call(n.name, ...n.args.map(go));
    switch (n.op) {
      case "+":
      case "-": return sum(n);
      case "*": return product(n);
      case "neg": return product(op("*", num(-1n), n.args[0]));
      case "/": {
        const a = go(n.args[0]);
        const b = go(n.args[1]);
        if (isNum(a, 0) && !isTotal(b)) return op("/", a, b);
        // numeric factors move out front: (6u)/(3v) = 2·(u/v)
        const [ca, ua] = split(a);
        const [cb, ub] = split(b);
        if (isZero(cb)) return op("/", a, b);
        const c = ca.divide(cb);
        const q = ub === null ? (ua === null ? null : ua) : op("/", ua ?? ON(), ub);
        if (q === null) return num(c);
        if (ua === null && ub !== null) return S.div(num(c), ub);
        return S.mul(num(c), q);
      }
      case "^": {
        const a = go(n.args[0]);
        const b = go(n.args[1]);
        if (isNum(b, 0)) return op("^", a, b); // 0^0 is refused elsewhere
        if (a.type === "num" && isPosInt(b) && b.value.numerator <= 64n) return num(a.value.pow(Number(b.value.numerator)));
        return S.pow(a, b);
      }
      default: return op(n.op, ...n.args.map(go));
    }
  };
  return go(toAst(ast));
}

/** d/d(name) of the tree, as a new tree. */
export function derivative(ast, name = "x") {
  const d = (n) => {
    if (!depends(n, name)) return ZN();
    switch (n.type) {
      case "var":
        return ON();
      case "op": {
        const [a, b] = n.args;
        switch (n.op) {
          case "+": return S.add(d(a), d(b));
          case "-": return S.sub(d(a), d(b));
          case "neg": return S.neg(d(a));
          case "*": return S.add(S.mul(d(a), b), S.mul(a, d(b)));
          case "/":
            if (!depends(b, name)) return S.div(d(a), b);
            return S.div(S.sub(S.mul(d(a), b), S.mul(a, d(b))), S.pow(b, num(2n)));
          case "^": {
            if (!depends(b, name)) {
              const q = constantRational(b);
              const bm1 = q !== null ? num(q.subtract(ONE)) : S.sub(b, ON());
              if (q !== null && isZero(q.subtract(ONE))) return d(a);
              return S.mul(S.mul(b, S.pow(a, bm1)), d(a));
            }
            if (!depends(a, name)) return S.mul(S.mul(n, call("log", a)), d(b));
            // a^b · (b' log a + b a'/a)
            return S.mul(n, S.add(S.mul(d(b), call("log", a)), S.div(S.mul(b, d(a)), a)));
          }
        }
        break;
      }
      case "call": {
        if (n.name === "besselJ") {
          // J₀′ = −J₁ and J_n′ = (J_(n−1) − J_(n+1))/2
          const k = n.args[0].value;
          const x = n.args[1];
          const J = (m) => call("besselJ", num(m), x);
          const slope = isZero(k) ? S.neg(J(ONE)) : S.div(S.sub(J(k.subtract(ONE)), J(k.add(ONE))), num(2n));
          return S.mul(slope, d(x));
        }
        const [a] = n.args;
        const da = d(a);
        const two = () => num(2n);
        const halfPi = (u) => S.div(S.mul({ type: "const", name: "pi" }, S.pow(u, two())), two());
        switch (n.name) {
          case "gamma": return S.mul(S.mul(n, call("digamma", a)), da);
          case "lgamma": return S.mul(call("digamma", a), da);
          case "digamma": return S.mul(call("trigamma", a), da);
          case "trigamma": return refuse("unsupported", "the derivative of trigamma is not available");
          case "Si": return S.mul(S.div(call("sin", a), a), da);
          case "fresnelS": return S.mul(call("sin", halfPi(a)), da);
          case "fresnelC": return S.mul(call("cos", halfPi(a)), da);
          case "sin": return S.mul(call("cos", a), da);
          case "cos": return S.neg(S.mul(call("sin", a), da));
          case "tan": return S.div(da, S.pow(call("cos", a), two()));
          case "exp": return S.mul(n, da);
          case "ln":
          case "log": return S.div(da, a);
          case "log1p": return S.div(da, S.add(ON(), a));
          case "sqrt": return S.div(da, S.mul(two(), n));
          case "atan": return S.div(da, S.add(ON(), S.pow(a, two())));
          case "asin": return S.div(da, call("sqrt", S.sub(ON(), S.pow(a, two()))));
          case "acos": return S.neg(S.div(da, call("sqrt", S.sub(ON(), S.pow(a, two())))));
          case "cbrt": return S.div(da, S.mul(num(3n), S.pow(n, two())));
          case "erf": return S.mul(S.div(S.mul(two(), call("exp", S.neg(S.pow(a, two())))), call("sqrt", { type: "const", name: "pi" })), da);
          case "sinh": return S.mul(call("cosh", a), da);
          case "cosh": return S.mul(call("sinh", a), da);
          case "tanh": return S.div(da, S.pow(call("cosh", a), two()));
          case "abs": return S.mul(S.div(a, n), da); // valid where a ≠ 0
          case "min":
          case "max":
            return refuse("not-smooth", `${n.name} has no derivative formula; split the domain where its arguments meet`);
        }
        break;
      }
    }
    return refuse("bad-expression", `cannot differentiate ${n.type} ${n.op ?? n.name ?? ""}`);
  };
  return d(ast);
}
