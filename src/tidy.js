// A normal form for formulas that are rational functions of their variables
// and of their function calls.
//
// Each call (sin(v), exp(x*y), sqrt(1 + u^2)) stands as one more letter, the
// tree becomes a quotient of two polynomials in those letters, and then
//
//   sin² is traded for 1 − cos² (or the other way, whichever is shorter),
//   sqrt(P)² becomes P,
//   the common factor of numerator and denominator is divided out.
//
// This is what makes the formulas of differential geometry readable: the first
// fundamental form of a sphere comes out as sin(v)^2, not as a page of
// products. A tree that does not fit (a variable in an exponent) is returned
// as simplify leaves it.
import { Rational } from "@ratmath/core";
import { ZERO, ONE } from "./rat.js";
import { format, simplify, constantRational, num, v as variable, op, call } from "./expr.js";

const keyOf = (e) => e.join(",");
const expOf = (key) => key.split(",").map(Number);
const LIMIT = 400; // terms beyond which the common factor is not looked for

function addP(p, r, s = ONE) {
  const out = new Map(p);
  for (const [key, c] of r) {
    const t = (out.get(key) ?? ZERO).add(c.multiply(s));
    if (t.numerator === 0n) out.delete(key);
    else out.set(key, t);
  }
  return out;
}
function mulP(p, r) {
  const out = new Map();
  for (const [k1, c1] of p) {
    const e1 = expOf(k1);
    for (const [k2, c2] of r) {
      const e2 = expOf(k2);
      const key = keyOf(e1.map((x, i) => x + e2[i]));
      const t = (out.get(key) ?? ZERO).add(c1.multiply(c2));
      if (t.numerator === 0n) out.delete(key);
      else out.set(key, t);
    }
  }
  return out;
}
const scaleP = (p, s) => new Map([...p].map(([k, c]) => [k, c.multiply(s)]));
const constP = (n, c) => (c.numerator === 0n ? new Map() : new Map([[keyOf(new Array(n).fill(0)), c]]));
const letterP = (n, i, d = 1) => new Map([[keyOf(Array.from({ length: n }, (_, j) => (j === i ? d : 0))), ONE]]);
const lexCmp = (a, b) => {
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return a[i] - b[i];
  return 0;
};
function leading(p) {
  let best = null;
  let bc = null;
  for (const [key, c] of p) {
    const e = expOf(key);
    if (best === null || lexCmp(e, best) > 0) {
      best = e;
      bc = c;
    }
  }
  return { e: best, c: bc };
}
/** a / b when b divides a exactly, else null */
function divExact(a, b) {
  if (b.size === 0) return null;
  const lb = leading(b);
  let r = a;
  let q = new Map();
  for (let guard = 0; r.size > 0; guard++) {
    if (guard > 4000) return null;
    const lr = leading(r);
    const e = lr.e.map((x, i) => x - lb.e[i]);
    if (e.some((x) => x < 0)) return null;
    const term = new Map([[keyOf(e), lr.c.divide(lb.c)]]);
    q = addP(q, term);
    r = addP(r, mulP(term, b), ONE.negate());
  }
  return q;
}
const degIn = (p, j) => {
  let d = 0;
  for (const key of p.keys()) d = Math.max(d, expOf(key)[j]);
  return d;
};
/** coefficients of p as a polynomial in letter j: Map degree → polynomial without j */
function coeffsIn(p, j) {
  const out = new Map();
  for (const [key, c] of p) {
    const e = expOf(key);
    const d = e[j];
    e[j] = 0;
    if (!out.has(d)) out.set(d, new Map());
    out.get(d).set(keyOf(e), c);
  }
  return out;
}
const monic = (p) => (p.size ? scaleP(p, leading(p).c.reciprocal()) : p);
/** greatest common divisor of two polynomials (leading coefficient 1), by primitive remainder sequences */
function gcdP(a, b, n, from = 0) {
  if (a.size === 0) return monic(b);
  if (b.size === 0) return monic(a);
  let j = from;
  while (j < n && degIn(a, j) === 0 && degIn(b, j) === 0) j++;
  if (j >= n) return constP(n, ONE);
  const content = (p) => {
    let g = new Map();
    for (const c of coeffsIn(p, j).values()) {
      g = gcdP(g, c, n, j + 1);
      if (g.size === 1 && leading(g).e.every((x) => x === 0)) break;
    }
    return g;
  };
  const ca = content(a);
  const cb = content(b);
  let pa = divExact(a, ca);
  let pb = divExact(b, cb);
  const gc = gcdP(ca, cb, n, j + 1);
  if (degIn(pa, j) < degIn(pb, j)) [pa, pb] = [pb, pa];
  for (let guard = 0; pb.size > 0; guard++) {
    if (guard > 200) return gc;
    const db = degIn(pb, j);
    if (db === 0) return gc; // a non-zero remainder free of the letter: nothing in common
    const lcb = coeffsIn(pb, j).get(db);
    let r = pa;
    while (r.size > 0 && degIn(r, j) >= db) {
      const dr = degIn(r, j);
      const lcr = coeffsIn(r, j).get(dr);
      r = addP(mulP(lcb, r), mulP(mulP(lcr, letterP(n, j, dr - db)), pb), ONE.negate());
      if (r.size > 4 * LIMIT) return gc;
    }
    pa = pb;
    pb = r.size ? divExact(r, content(r)) : r;
  }
  return mulP(gc, monic(pa));
}

function polyAst(p, names) {
  const terms = [...p]
    .map(([key, c]) => [expOf(key), c])
    .sort((s, t) => -lexCmp(s[0], t[0]))
    .map(([e, c]) => {
      let m = null;
      e.forEach((d, i) => {
        if (!d) return;
        const f = d === 1 ? names[i] : op("^", names[i], num(d));
        m = m ? op("*", m, f) : f;
      });
      const neg = c.numerator < 0n;
      const a = neg ? c.negate() : c;
      const body = m === null ? num(a) : a.equals(ONE) ? m : op("*", num(a), m);
      return { neg, body };
    });
  if (!terms.length) return num(0);
  let out = terms[0].neg ? op("neg", terms[0].body) : terms[0].body;
  for (const t of terms.slice(1)) out = op(t.neg ? "-" : "+", out, t.body);
  return out;
}

/** the square root of a rational when it is one, else null */
function ratSqrt(c) {
  if (c.numerator < 0n) return null;
  const root = (x) => {
    if (x < 2n) return x;
    let r = BigInt(Math.floor(Math.sqrt(Number(x))));
    while (r * r > x) r--;
    while ((r + 1n) * (r + 1n) <= x) r++;
    return r * r === x ? r : null;
  };
  const a = root(c.numerator);
  const b = root(c.denominator);
  return a === null || b === null ? null : new Rational(a, b);
}

class Context {
  constructor() {
    this.letters = []; // trees, in order
    this.index = new Map(); // format(tree) → position
    this.pending = [];
  }
  letter(tree) {
    const key = format(tree);
    if (!this.index.has(key)) {
      this.index.set(key, this.letters.length);
      this.letters.push(tree);
    }
    return { letter: this.index.get(key) };
  }
}

/** First pass: the tree with every letter found, as a nested { n, d } recipe run once the letters are known. */
function build(ast, ctx) {
  const t = ast;
  if (t.type === "num") return (n) => ({ n: constP(n, t.value), d: constP(n, ONE) });
  if (t.type === "var") {
    const { letter } = ctx.letter(t);
    return (n) => ({ n: letterP(n, letter), d: constP(n, ONE) });
  }
  if (t.type === "call") {
    if (t.name === "sqrt" && t.args.length === 1) return root(t.args[0], ctx);
    const args = t.args.map((a) => tidy(a));
    const { letter } = ctx.letter(call(t.name, ...args));
    return (n) => ({ n: letterP(n, letter), d: constP(n, ONE) });
  }
  if (t.type !== "op") return null;
  if (t.op === "^") {
    const c = constantRational(t.args[1]);
    if (c === null) {
      const { letter } = ctx.letter(op("^", tidy(t.args[0]), tidy(t.args[1])));
      return (n) => ({ n: letterP(n, letter), d: constP(n, ONE) });
    }
    if (c.denominator === 2n) {
      // X^(k + 1/2) = X^k · sqrt(X)
      const k = (c.numerator - 1n) / 2n;
      const whole = build(op("^", t.args[0], num(new Rational(k))), ctx);
      const r = root(t.args[0], ctx);
      if (!whole || !r) return null;
      return (n) => {
        const a = whole(n);
        const b = r(n);
        return { n: mulP(a.n, b.n), d: mulP(a.d, b.d) };
      };
    }
    if (c.denominator !== 1n) {
      const { letter } = ctx.letter(op("^", tidy(t.args[0]), num(c)));
      return (n) => ({ n: letterP(n, letter), d: constP(n, ONE) });
    }
    const base = build(t.args[0], ctx);
    if (!base) return null;
    const k = Number(c.numerator < 0n ? -c.numerator : c.numerator);
    if (k > 24) return null;
    return (n) => {
      const b = base(n);
      let pn = constP(n, ONE);
      let pd = constP(n, ONE);
      for (let i = 0; i < k; i++) {
        pn = mulP(pn, b.n);
        pd = mulP(pd, b.d);
        if (pn.size > 4 * LIMIT || pd.size > 4 * LIMIT) throw new RangeError("too large");
      }
      return c.numerator < 0n ? { n: pd, d: pn } : { n: pn, d: pd };
    };
  }
  const parts = t.args.map((a) => build(a, ctx));
  if (parts.some((p) => p === null)) return null;
  return (n) => {
    const a = parts.map((p) => p(n));
    const big = (r) => {
      if (r.n.size > 4 * LIMIT || r.d.size > 4 * LIMIT) throw new RangeError("too large");
      return r;
    };
    switch (t.op) {
      case "+":
      case "-": {
        const s = t.op === "+" ? ONE : ONE.negate();
        if (a[1].d.size === 1 && a[0].d.size === 1 && [...a[0].d.keys()][0] === [...a[1].d.keys()][0]) {
          const scale = [...a[0].d.values()][0].divide([...a[1].d.values()][0]);
          return big({ n: addP(a[0].n, a[1].n, s.multiply(scale)), d: a[0].d });
        }
        return big({ n: addP(mulP(a[0].n, a[1].d), mulP(a[1].n, a[0].d), s), d: mulP(a[0].d, a[1].d) });
      }
      case "neg": return { n: scaleP(a[0].n, ONE.negate()), d: a[0].d };
      case "*": return big({ n: mulP(a[0].n, a[1].n), d: mulP(a[0].d, a[1].d) });
      case "/":
        if (a[1].n.size === 0) throw new RangeError("division by zero");
        return big({ n: mulP(a[0].n, a[1].d), d: mulP(a[0].d, a[1].n) });
    }
    throw new RangeError("unknown operation");
  };
}

/** sqrt(X): a rational, a product of absolute values, or a letter whose square is known */
function root(arg, ctx) {
  const inner = tidy(arg);
  const c = constantRational(inner);
  if (c !== null) {
    const r = ratSqrt(c);
    if (r !== null) return (n) => ({ n: constP(n, r), d: constP(n, ONE) });
  }
  // c · x^(2k) · …: |x|^k times the root of c
  const factors = [];
  const flat = (t, sign) => {
    if (t.type === "op" && t.op === "*") return flat(t.args[0], sign) && flat(t.args[1], sign);
    if (t.type === "op" && t.op === "/") return flat(t.args[0], sign) && flat(t.args[1], -sign);
    const k = constantRational(t);
    if (k !== null) return k.numerator > 0n && factors.push({ c: sign > 0 ? k : k.reciprocal() });
    if (t.type === "op" && t.op === "^") {
      const e = constantRational(t.args[1]);
      if (e !== null && e.denominator === 1n && e.numerator % 2n === 0n) return factors.push({ base: t.args[0], k: (e.numerator / 2n) * BigInt(sign) });
    }
    return false;
  };
  if (c === null && flat(inner, 1) && factors.some((f) => f.base)) {
    let cTotal = ONE;
    let tree = null;
    for (const f of factors) {
      if (f.c) {
        cTotal = cTotal.multiply(f.c);
        continue;
      }
      const positive = f.base.type === "call" && ["sqrt", "exp", "abs", "cosh"].includes(f.base.name);
      const piece = op("^", positive ? f.base : call("abs", f.base), num(new Rational(f.k)));
      tree = tree ? op("*", tree, piece) : piece;
    }
    const r = ratSqrt(cTotal);
    return build(op("*", r !== null ? num(r) : call("sqrt", num(cTotal)), tree), ctx);
  }
  const tree = call("sqrt", inner);
  const { letter } = ctx.letter(tree);
  const sq = build(inner, ctx);
  if (sq) ctx.pending.push({ letter, square: sq });
  return (n) => ({ n: letterP(n, letter), d: constP(n, ONE) });
}

/** replace letter i squared by the polynomial `by` wherever it appears */
function reduceSquare(p, i, by, n) {
  for (let guard = 0; guard < 400; guard++) {
    let hit = null;
    for (const key of p.keys()) {
      if (expOf(key)[i] >= 2) {
        hit = key;
        break;
      }
    }
    if (hit === null) return p;
    const c = p.get(hit);
    const e = expOf(hit);
    e[i] -= 2;
    p = new Map(p);
    p.delete(hit);
    p = addP(p, mulP(new Map([[keyOf(e), c]]), by));
    if (p.size > 4 * LIMIT) throw new RangeError("too large");
  }
  void n;
  return p;
}

/**
 * The tidied tree. Equal to the input wherever both are defined; the only
 * change of meaning is that a cancelled factor no longer makes a hole.
 */
export function tidy(ast) {
  const start = simplify(ast);
  if (start.type === "num" || start.type === "var") return start;
  const ctx = new Context();
  let recipe;
  try {
    recipe = build(start, ctx);
  } catch {
    return start;
  }
  if (!recipe) return start;
  const n = ctx.letters.length;
  let r;
  try {
    r = recipe(n);
    // squares of square roots
    for (const { letter, square } of ctx.pending) {
      const sq = square(n);
      if (sq.d.size !== 1 || !leading(sq.d).e.every((x) => x === 0)) continue;
      const by = scaleP(sq.n, leading(sq.d).c.reciprocal());
      r = { n: reduceSquare(r.n, letter, by, n), d: reduceSquare(r.d, letter, by, n) };
    }
    // sin² + cos² = 1, in whichever direction leaves less
    ctx.letters.forEach((tree, i) => {
      if (tree.type !== "call" || tree.name !== "sin") return;
      const j = ctx.index.get(format(call("cos", tree.args[0])));
      const oneMinus = (k) => addP(constP(n, ONE), letterP(n, k, 2), ONE.negate());
      const viaCos = j === undefined ? null : { n: reduceSquare(r.n, i, oneMinus(j), n), d: reduceSquare(r.d, i, oneMinus(j), n) };
      const viaSin = j === undefined ? null : { n: reduceSquare(r.n, j, oneMinus(i), n), d: reduceSquare(r.d, j, oneMinus(i), n) };
      if (!viaCos) return;
      const size = (x) => x.n.size + x.d.size;
      r = size(viaSin) < size(viaCos) ? viaSin : viaCos;
    });
    // cosh² − sinh² = 1
    ctx.letters.forEach((tree, i) => {
      if (tree.type !== "call" || tree.name !== "cosh") return;
      const j = ctx.index.get(format(call("sinh", tree.args[0])));
      if (j === undefined) return;
      const by = addP(constP(n, ONE), letterP(n, j, 2));
      r = { n: reduceSquare(r.n, i, by, n), d: reduceSquare(r.d, i, by, n) };
    });
    if (r.n.size === 0) return num(0);
    if (r.d.size === 0) return start;
    if (r.n.size <= LIMIT && r.d.size <= LIMIT && !(r.d.size === 1 && leading(r.d).e.every((x) => x === 0))) {
      const g = gcdP(r.n, r.d, n);
      if (!(g.size === 1 && leading(g).e.every((x) => x === 0))) {
        const qn = divExact(r.n, g);
        const qd = divExact(r.d, g);
        if (qn && qd) r = { n: qn, d: qd };
      }
    }
  } catch {
    return start;
  }
  // one rational in front: the denominator gets whole coprime coefficients, leading one positive
  const dl = leading(r.d);
  let scale = dl.c.numerator < 0n ? ONE.negate() : ONE;
  const g2 = (a, b) => {
    while (b) [a, b] = [b, a % b];
    return a < 0n ? -a : a;
  };
  let lcm = 1n;
  let gcd = 0n;
  for (const c of r.d.values()) {
    lcm = (lcm * c.denominator) / g2(lcm, c.denominator);
  }
  for (const c of r.d.values()) gcd = g2(gcd, (c.numerator * lcm) / c.denominator);
  scale = scale.multiply(new Rational(lcm, gcd || 1n));
  const dn = scaleP(r.d, scale);
  const nn = scaleP(r.n, scale);
  const top = polyAst(nn, ctx.letters);
  const constantDen = dn.size === 1 && leading(dn).e.every((x) => x === 0);
  return simplify(constantDen ? polyAst(scaleP(nn, leading(dn).c.reciprocal()), ctx.letters) : op("/", top, polyAst(dn, ctx.letters)));
}

/** Whether the tree is identically zero, as far as the normal form shows. */
export function vanishesIdentically(ast) {
  const t = tidy(ast);
  const c = constantRational(t);
  return c !== null && c.numerator === 0n;
}
