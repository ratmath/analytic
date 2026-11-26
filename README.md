# @ratmath/analytic

Documentation and interactive explorer: https://ratmath.com/analytic/

Taylor models with exact rational coefficients and certified remainders, built
on [`@ratmath/core`](https://github.com/ratmath/core). A model on a domain `D = [a, b]` with centre `c`
is a pair `(P, I)` with

    f(x) − P(x − c) ∈ I    for every x in D,

where `P` has exact `Rational` coefficients and `I` is a rational interval.
Every operation keeps that statement true, so ranges, values and integrals that
come out are proofs, not estimates. When a hypothesis fails (a log argument that
reaches 0, a divisor whose range contains 0, a point outside the domain) the
library throws an `AnalyticError` with a reason instead of returning a bound it
cannot prove.

**Docs site:** GitHub Pages from the `docs` folder, one HTML file per page:
an overview (`index.html`), a full reference (`reference.html`), a free-form
explorer (`explore.html`), and topic pages with the mathematics, worked
examples and live demos (values, formulas, Taylor models, ranges and
integrals, zeros, piecewise, ODEs, series, fast-then-certified). The page
bodies live in `docs-src/pages/` and share `docs-src/layout.html`;
`bun run docs:build` bundles the library to `docs/assets/analytic.js` and
writes the pages (`scripts/build-pages.js`). Edit `docs-src`, not the
generated `docs/*.html`. Math written as `\( … \)` or `\[ … \]` is typeset with
KaTeX at build time (pages load the shared stylesheet from
`ratmath.com/assets/katex/`). Every page ends with an editable JavaScript box
that runs with the library in scope; its code comes from the page's
`<template data-runbox>`, and the build runs every box and fails if one throws
(`--verbose` prints what each shows). `docs/assets/runbox.js` and
`scripts/docs-kit.js` are shared verbatim with the core, linalg and algebraic
docs; keep the copies in sync.

## Install

```sh
npm install @ratmath/analytic @ratmath/core
```

ES modules only, for Bun, Node 22+ and browsers. TypeScript declarations are
included. Source: https://github.com/ratmath/analytic. Sibling libraries:
[core](https://ratmath.com/core/), [algebraic](https://ratmath.com/algebraic/),
[linalg](https://ratmath.com/linalg/), [graphics](https://ratmath.com/graphics/).

Design notes: `docs/design/analytic-functions.md` in the [ratmath umbrella](https://github.com/ratmath/ratmath).
This package depends only on Core (not on `packages/reals`).

## Quick start

```js
import { R } from "@ratmath/core";
import { TM, Domain, exp, sin, log, series } from "@ratmath/analytic";

const D = Domain(R`0:1/2`);              // centre defaults to the midpoint, 1/4
const x = TM.x(D, { order: 12 });        // the identity model, degree ≤ 12
const f = exp(sin(x)).multiply(x);

f.at(R`1/4`);       // RationalInterval enclosing f(1/4)
f.range();          // enclosure of f over D
f.integral();       // enclosure of ∫_0^{1/2} f   (or f.integral(a, b))
f.integrate();      // antiderivative model F with F(1/4) = 0
f.coefficients;     // exact Rationals, powers of (x − 1/4)
f.remainder;        // RationalInterval
f.describe();       // domain, order, remainder width, rules used
```

## What is in it

| Area | API |
|---|---|
| Domains | `Domain(R\`a:b\`)`, `Domain(a, b)`, `Domain([a, b], { centre })` |
| Sources | `TM.x(D, opts)`, `TM.constant(D, value or interval)`, `TM.polynomial(D, [a0, a1, …])` (powers of x) |
| Arithmetic | `.add`, `.subtract`, `.negate`, `.multiply`, `.divide`, `.pow(n)` (models or Core numbers) |
| Elementary | `exp`, `sin`, `cos`, `tan`, `log`, `log1p`, `atan`, `asin`, `acos`, `sqrt`, `cbrt`, `erf`, `sinh`, `cosh`, `tanh`, `reciprocal`, `power(g, a)` |
| Evaluation | `.at(point or sub-interval)`, `.range({ depth })` |
| Calculus | `.integrate()`, `.integral(a, b)`, `.derivative()` (exact models only; see below) |
| User series | `series(D, { coefficient: k => a_k, order, rule, … })` |
| Point values | `enclose.exp(x, bits)` etc., `constants.pi(bits)`, `constants.e(bits)` |
| Formulas | `fn(text, { params })`: `.value`, `.range`, `.integral` (Refinements), `.limit(c)`, `.taylor(c, n)`, `.derivative()`, `.model(D)` |
| Limits and improper integrals | `.limit("inf")`, `.limit(c, { side })`, `.asymptotic()`, `.improperIntegral(a, b)` (Refinement) |
| Special functions | `gamma`, `lgamma`, `digamma`, `trigamma`, `beta`, `besselJ`, `Si`, `fresnelS`, `fresnelC`, `erfc` in formulas and as `enclose.*`; `bernoulli(m)` |
| Several variables | `field(text, vars)`: `.partial`, `.gradient`, `.hessian`, `.jet`, `.directional`, `.range`, `.integral`, `.criticalPoints` (Refinements); `divergence`, `curl`, `jacobian`, `lineIntegral`, `surfaceIntegral` |
| Fourier series | `fourier(f, [a, b], { terms, kind })` (Refinement of a `FourierSeries`) |
| Sequences and series | `sequence(term)`: `.limit`, `.monotone`, `.bounds`; `recursive(next, { start })`: `.fixedPoints`, `.limit` by contraction; `sum(term)`: the convergence tests as methods, `.convergence()`, `.sum()` with a proven tail; `powerSeries(c)`: `.radius`, `.interval` with the ends examined; `taylorRemainder`; `functionSequence` |
| Theorems of vector calculus | `greens`, `stokes`, `divergenceTheorem` (both sides enclosed, and the enclosures must meet); `changeOfVariables` with its Jacobian; `potential`; `lagrange` |
| Differential geometry | `curve(components)`: `.curvature`, `.torsion`, `.length`, `.at(t)` with the Frenet frame and osculating circle; `surface(components)`: fundamental forms, Gaussian and mean curvature, `.at(u, v)` with the kind of point; `metric({ E, F, G })`: `.christoffel`, `.geodesic`, `.transport`, `.gaussBonnet` |
| ODEs | `ode.solve(spec)` (Refinement), `ode.step(spec)` |
| Boundary value problems | `bvp({ f, interval, left, right })` (Refinement of a `BVPSolution`) |
| Features | `zeros`, `poles`, `extrema`, `inflections` (Refinements) |
| Fast-then-certified | `Refinement`, `live` |
| Evaluator scope | `createScope({ digits })` (adds `fn`, `d`, `ode`) |

Options: `order` (maximum degree kept, default 12) and `bits` (precision of the
irrational constants, default 96 ≈ 28 digits).

### How the bounds are proven

- **Elementary functions of a model `g`** use the outer function's Taylor
  series about `c0 = g(centre)` with the Lagrange remainder over the whole
  argument range `c0 + range(g − c0)`: exp (`e^max`), sin/cos (1), log and 1/x
  (argument range must exclude 0), atan (`(k−1)!/(1+x²)^(k/2)`), sqrt (range
  above 0). The values `f^(k)(c0)/k!` that are irrational are certified
  intervals; their midpoints go into the polynomial, their radii into the
  remainder.
- **Products** keep degrees ≤ order; the dropped part and the cross terms
  `P·J + Q·I + I·J` go into the remainder.
- **Ranges** use the Bernstein form of the polynomial with bisection.
- **Point values** (`exp`, `log`, `atan`, `sin`, `cos`, `sqrt`, `π`) are
  series with explicit tail bounds and argument reduction, checked in the tests
  against 30-digit references.
- **Derivatives**: the remainder of a model says nothing about the derivative,
  so `.derivative()` refuses unless the model is an exact polynomial. Build the
  model of `f′` from its formula instead.

### User series and their rules

```js
series(D, { coefficient: k => R`1/${2 ** k}`, centre: 0, rule: "ratio", q: R`1/4` });
series(D, { coefficient: k => …, rule: "alternating" });
series(D, { coefficient: k => R`1/${factorial(k)}`, rule: "lagrange", M: 3 });   // M ≥ max |f^(p+1)| on D
series(D, { coefficients: [ … ], rule: "explicit", error: R`1/1000` });
```

`ratio` and `alternating` check their hypothesis on the next `lookahead`
(default 32) terms and refuse when it fails there; beyond that, and for the
`M` and `error` that a caller supplies, the bound is the caller's claim, so the
model is marked `assumed` and `describe()` says so.

## Using it from an evaluator (RatTree, RatCalc)

`createScope` returns plain callable functions that accept Core numbers, Core
intervals and Taylor models alike, so a function worker can put them in scope
next to Core:

```js
import { createScope } from "@ratmath/analytic";
const A = createScope({ digits: 30 });   // or { bits }, { order }

A.exp(R`1/3`);                 // RationalInterval, ≥ 30 correct digits
A.sin(R`-1:1`);                // ±0.84147…, not the term-by-term ±1.18
A.model(x => A.exp(A.sin(x)), R`0:1/2`);          // TaylorModel
A.integral(x => A.exp(A.sin(x)), 0, 1, { pieces: 4 });
A.range(x => x.multiply(A.cos(x)), R`0:3`);
A.pi; A.e;                     // RationalIntervals at the scope's precision
```

## Used by

- RatCalc (terminal and web): `A` is `createScope({ digits: 30 })`, e.g.
  ``A.exp(R`1/3`)``; `analytic({ digits })` for other precisions;
  `help("analytic")` lists everything with examples.
- RatTree (the Stern-Brocot explorer): function code has these names in scope
  (and `analytic.range`); Predefined… → Certified has worked examples.

## Performance

Order 12 `exp(sin(x))·x` with its range takes about 60 ms in Bun; order 20
about 170 ms; a 4-piece certified integral about 250 ms. Keep UI actions in a
worker.

## Fast first, certified last

Every question about a function given as a formula returns a `Refinement`,
the same class `@ratmath/linalg` and `@ratmath/graphics` use (it lives in
`@ratmath/core/refine`), so one `live()` loop drives all three libraries:

| member | what it gives |
| --- | --- |
| `quick` | float preview `{ stage: "float", value, trust }`, computed on first read |
| `exact()` / `exactStage()` | the certified answer, synchronously (fine in a Worker) |
| `settle({ signal, sliceMs, onStage, onProgress })` | the same in time slices; rejects with `AbortError` when aborted |
| `stages()` | float stage, then `{ stage: "progress", done, of, step, partial }` ticks, then `{ stage: "exact", exact: true, value, via }` |

Here the last stage is a certified enclosure at the requested precision
(transcendental values cannot be exact). Progress ticks carry `partial`, the
enclosure so far, so a display can sharpen as it goes. `via` says how the
answer was proven and whether a budget was hit.

```js
import { fn, live } from "@ratmath/analytic";

const f = fn("exp(sin(x))*x");            // same grammar and AST as @ratmath/graphics
f.value("1/3", { digits: 30 }).quick;     // { value: 0.46235716975704894, trust: "good" }
f.value("1/3", { digits: 30 }).exact();   // RationalInterval, 30 digits, proven
f.range(R`0:3`, { digits: 6 }).exact();   // adaptive bisection of Taylor models
f.integral(0, 1, { digits: 20 }).exact(); // Gauss–Legendre preview, certified enclosure
f.derivative().toString();                // "exp(sin(x))*cos(x)*x + exp(sin(x))"
f.derivative().model(Domain(R`0:1`));     // certified model of f′, rebuilt from its formula

const g = fn("a*sin(x)", { params: { a: 1 } });
const update = live((a) => g.with({ a }).value("1/2"), (s) => show(s.value, s.exact));
slider.oninput = () => update(`${slider.value}/8`);
```

| question | preview | certified value |
| --- | --- | --- |
| `f.value(x, { digits = 20 })` | float `f(x)` | `RationalInterval`; a point for rational-only formulas |
| `f.range(I, { digits = 6, order = 8, maxPieces = 256 })` | `[min, max]` of 256 samples, trust `rough` | outer enclosure; pieces holding the extremes are bisected until outer and inner bounds agree to `digits` |
| `f.integral(a, b, { digits = 12, order = 12, maxPieces = 256 })` | 8-panel Gauss–Legendre | enclosure; pieces split until each meets its share of the width budget |

### Expressions and d/dx

`fn(text or AST, { variable = "x", params })` reads calculator notation with
calculator notation (`2x`, `-x^2 = -(x^2)`, `^` right associative, decimals
exact). Functions: `sin cos tan asin acos atan sinh cosh tanh exp log ln log1p
sqrt cbrt erf abs min max` (`arcsin`, `arccos`, `arctan` are accepted too).
`log` and `ln` are the natural log. A power with an odd denominator, such as
`x^(1/3)` or `x^(2/3)`, is the real root and is defined for negative `x`. The AST is the same plain objects
(`num`, `var`, `const`, `op`, `call`), so a parse tree can be passed between
the libraries. Exports: `parse`, `format`, `differentiate(ast, name)`,
`simplify(ast)`, `compileFloat(ast)`, `modelOf(ast, env, base)`.

`simplify` only cancels what is defined everywhere: `sin(x) - sin(x)` becomes
`0`, while `x/x` and `log(x) - log(x)` are left alone because they are not
defined at every point.

```js
fn("sin(x)/x").limit(0);              // [1, 1]: removable points are filled in
fn("x/(exp(x) - 1)").taylor(0, 4);    // 1, -1/2, 1/12, 0, -1/720 as intervals
fn("abs(x)").integral(-1, 2).exact(); // 5/2: integrals may cross a kink
fn("cbrt(x)").range([-8, 8]).exact(); // [-2, 2]
```

`limit(c)` is the value where the function is defined and the certified limit
at a removable point of a quotient; it refuses at poles. `taylor(c, n)` gives
enclosures of the coefficients `f⁽ᵏ⁾(c)/k!` for `n ≤ 16`. Ranges and integrals
work across points where the function is not smooth (`abs`, `cbrt` at 0,
`asin` at ±1); there the bounds come from interval evaluation, which converges
more slowly than Taylor models.

Parameters may be numbers, strings, Rationals or intervals (an interval
parameter gives a result valid for every value in it). `abs`, `min` and `max`
are modelled where they are smooth on the domain and refused where they are
not. Derivatives are symbolic and simplified, so the model of `f′` is built
from `f′`'s formula with its own certified remainder, as the design note asks.

## ODEs: validated Picard steps

```js
import { ode } from "@ratmath/analytic";

const r = ode.solve({ f: "y^2 + t", y0: "1/2", until: "1/2" });
r.quick.value;          // RK4 samples { t: Float64Array, y: Float64Array }
const sol = r.exact();  // ODESolution
sol.final;              // RationalInterval enclosing y(1/2)
sol.at("1/4");          // enclosure at any t in the span
sol.steps;              // [{ t0, t1, models }], one Taylor model per component per step

ode.solve({ f: ["v", "-x"], vars: ["x", "v"], y0: [1, 0], until: 3 });       // systems
ode.solve({ f: (t, y) => exp(y.negate()), float: (t, y) => Math.exp(-y), y0: 0, until: 1 });
ode.step({ f: "y", y0: 1, step: "1/4" }).model;                               // one step
```

Each step on `[t0, t0 + h]` Picard-iterates a polynomial `P`, then looks for an
interval `I` with `Φ(P + I) ⊂ P + I` for the Picard operator
`Φ(y) = y0 + ∫ F(s, y(s)) ds` in Taylor-model arithmetic. That inclusion
proves the solution stays in `P + I` on the whole step. Steps chain through
the enclosure at `t0 + h`. `h` halves when no enclosure is found and while
halving still shrinks the width the step adds (target `tol`, default 2⁻⁴⁰);
it doubles again after a success. Interval initial values are carried. Blow-up
ends with `complete: false` and a `reason` instead of a wrong enclosure.
Options: `order` (10), `step`, `tol`, `maxSteps` (400), `minStep`,
`previewSteps` (200), `time` ("t"), `vars`, `params`.

Each step also follows how the solution depends on the initial value (the
variational equation, kept in a rotating frame), so the uncertainty carried
from step to step turns with the flow instead of being boxed again each time.
The oscillator above ends with widths near 10⁻¹⁴; `track: false` turns this
off, which is 2 to 5 times faster and about 5 times wider there. `until` may
be less than `t0` to integrate backward.

## Zeros, poles, extrema, inflections

The interface graphics asks about. Each returns a `Refinement`: float guesses
first (`{ kind: "guess", at }`, trust `rough`), then certified records.

```js
import { zeros, poles, extrema, inflections } from "@ratmath/analytic";

zeros("x^2 - 4", [-3, 3]).exact();
// [{ kind: "exact", at: -2, unique: true, multiplicity: 1 }, { kind: "exact", at: 2, ... }]
zeros("(x-1)^2*(x^2-2)", [0, 3]).exact();      // 1 exactly (multiplicity 2), √2 in a bracket
poles("(x^2-1)/((x-1)*x^2)", [-3, 3]).exact();  // pole at 0 (order 2), hole at 1 with value 2
extrema("x^3 - 3x", [-3, 3]).exact();           // max at -1 (value 2), min at 1 (value -2)
zeros("sin(x)^2", [-1, 4]).exact();             // 0 exactly with multiplicity 2; near π: possible, atMost 2
```

All take `(f, [a, b], { variable, params, tolerance = 1e-6 })` where `f` is
text, an AST or an `fn`. Records (`lo`, `hi`, `at` are Rationals; `value` is
a RationalInterval):

| function | kinds | extra fields |
| --- | --- | --- |
| `zeros` | `exact`, `sign-change` (a zero is proven inside), `possible`, `undefined` (f could not be evaluated there; no claim) | `unique`, `multiplicity`, `atMost`, `bound` |
| `poles` | `pole`, `hole` (removable: f undefined, limit exists), `undefined` | `order`, `value` (the hole's limit) |
| `extrema` | `max`, `min`, `flat` (f′ = 0 without a sign change), `possible` | `value`, `unique` |
| `inflections` | `inflection`, `possible` | `value`, `unique` |

Brackets with no record certainly contain none. Two engines:

- **Rational functions with rational coefficients** are read into `N/D`
  exactly. `gcd(N, D)` gives the holes, Yun's square-free decomposition gives
  multiplicities and pole orders, and one Sturm sequence isolates every root.
  Brackets narrow by exact sign tests at the simplest rational in the middle
  half, so rational roots come out exactly. Everything is proven and unique.
- **Everything else** uses interval bisection with the Krawczyk test
  `K = m − Y·f(m) + (1 − Y·F′(X))(X − m)`: `K ∩ X = ∅` excludes a zero,
  `K ⊂ int X` proves exactly one, and iterating narrows it quadratically.
  Where f′ may vanish, a bracket is `possible` with `atMost: m` when the m-th
  derivative is proven nonzero (Rolle). At an exact zero, derivatives that
  are exactly 0 there give its multiplicity, and nearby `possible` brackets
  are absorbed when Rolle leaves no room for another zero. Extrema and
  inflections are classified by the next derivative's sign (or by a proven
  sign change). Poles are zeros of denominators (including `tan`'s `cos`)
  with the numerator proven nonzero, and only where the blow-up provably
  reaches f (through sums with bounded terms and products with factors
  bounded away from 0). A division inside `exp`, `sin`, ... gives
  `undefined`, not `pole`: `e^(-1/x²)` tends to 0 at 0.

**Flat functions.** Where every derivative vanishes, as for `e^(-1/x²)` at 0,
no finite test can separate "tiny" from "zero". Brackets on which
`|f| ≤ 2^-flatBits` (default 4 × the working bits, about 10⁻¹⁰⁰) with no
proof of a single crossing come back as `possible` with `bound` (the proven
maximum of |f| there) and no `atMost`, since every derivative is also flat. They are
never reported as zeros. Outside them, f is proven nonzero.

**Holes.** When f has summands that are rational functions of x, as in
`(x^2 - 1)/(x - 1) + sin(2x)/2`, they are combined into N/D and the exact
gcd is cancelled. Zeros, extrema, inflections, integrals and ranges are then
computed on `x + 1 + sin(2x)/2`, which has no singularity to bisect into;
results exactly at a hole are dropped (f is undefined there), `poles` reports
each hole with the limit as `value`, and `value(1)` still refuses.

**Removable points of quotients.** f is first written as one quotient
through products, sums and constant factors (`4·sin(x)/x`, `sin(x)/x + x`).
For f = u/v with v a polynomial, an exact
rational zero c of v where u vanishes to the same order k is a hole: the limit
u^(k)(c)/v^(k)(c) is certified by L'Hôpital, so `sin(x)/x` reports a hole at
0 with value exactly 1. Near c the m-th derivative is written N_m / v^(m+1)
and enclosed by the mean-value form N_m^(K)(X) / (v^(m+1))^(K)(X), which
lets the searches pass through c. Results exactly at c are dropped.

A `possible` extremum or inflection with `touching: true` has f′ (or f″) of
the same proven sign at both ends: either nothing is there (f′ only touches
0, as for 1 + cos 2x at π/2) or a max–min pair lies inside the bracket. Finite
precision cannot tell these apart unless the touch is at a rational point.

**Logs and roots.** `ln(g)` has a vertical asymptote where g has a zero:
`poles` reports it as `kind: "pole"` with `source: "log"` (only where the
blow-up reaches f, so `x·ln(x)` has none). Zeros of `sqrt(g)`, `g^p` (p > 0),
`abs(g)` and constant multiples are found as zeros of g; through an even
power, `sqrt` or `abs` a proven single zero is `isolated` rather than
`sign-change`, since f keeps its sign.

**Budgets.** The general engine works through a stack of brackets and pauses
every 15 ms, so `settle()` keeps a page responsive. Each starting piece has a
budget (`maxBoxes`, default 2000, and a share of `maxMs`, default 8000);
brackets left when it runs out come back as `possible`, and `via` says so.

## Piecewise functions

A piecewise function is a list of (region, rule) pairs; the first region that
contains x wins. Regions are betweenness chains on x, read by Core's `Region`
(`@ratmath/core` 0.9.0); the same text works in `R.region` and RiX chains:

| region | meaning |
| --- | --- |
| `2:x:8` | 2 ≤ x ≤ 8 |
| `_:x:8`, `2:x:_` | x ≤ 8, x ≥ 2 (`_` is an unbounded side) |
| `2:!x:8`, `2:x:!8` | 2 < x ≤ 8, 2 ≤ x < 8 (`:!` is a strict link) |
| `2n :x:! 2n+1` | 2n ≤ x < 2n+1 for some integer n |
| `_:x:!-1 \|\| 1:!x:_` | a union |
| `all`, `else`, `otherwise` | every x |

A name in a bound that is not a parameter is an integer variable; bounds must
be affine in it, and the rule may use it (`x - n if n:x:!n+1` is the
sawtooth). A region can also be a plain function of a Rational returning a
boolean; that answers point questions only, since ranges, integrals and zeros
need breakpoints.

```js
import { fn, piecewise, where } from "@ratmath/analytic";
const f = fn("x^2 if _:x:1; 3 - x if 1:!x:2; 1/2 otherwise");
const square = piecewise([["2n:x:!2n+1", "1"], ["2n+1:x:!2n+2", "-1"]]);
const r = where`${a}:!x:${b}`; // a Region from a template
f.breaks([-2, 4]).exact();     // jumps, removable points, closed sides
```

`value`, `range`, `integral`, `zeros`, `extrema`, `inflections` and `poles`
work piece by piece and tag results with `piece` (and `n`). A sign change
across a jump is not a zero.

## The rest of the calculus sequence

```js
import { fn, field, fourier, bvp, lineIntegral } from "@ratmath/analytic";

fn("(1 + 1/x)^x").limit("inf");                    // an interval around e
fn("1/x").limit(0, { side: "right" });             // Infinity
fn("exp(-x^2)").improperIntegral("-inf", "inf").exact();   // an interval around √π
fn("1/sqrt(x)").improperIntegral(0, 1).exact();    // singular at 0: an interval around 2
fn("1/x").improperIntegral(1, "inf").exact();      // Infinity, a proven divergence
fn("gamma(x)").value("1/2").exact();               // √π again
fn("besselJ(0, x)").integral(0, 5).exact();

const F = field("x^2 + x*y + y^2 - 3x", ["x", "y"]);
F.gradient();                                      // two ScalarFields
F.criticalPoints({ x: [-5, 5], y: [-5, 5] }).exact();      // one proven minimum at (2, −1)
field("x*y", ["x", "y"]).integral("0:x:1 && 0:y:x").exact();   // over a triangle
lineIntegral(["-y", "x"], ["x", "y"], { x: "cos(t)", y: "sin(t)" }, [0, 1]).exact();

const S = fourier("x", [-1, 1], { terms: 8 }).exact();
S.b[1];  S.partial(8);  S.meanSquareError(8);

const s = bvp({ f: "-y", interval: [0, 1], left: { y: 0 }, right: { y: 1 } }).exact();
s.at("1/2");  s.start;                             // y(1/2), and the slope y′(0) that was found
```

A limit or an improper integral is decided by a growth calculus: every
subexpression is bounded on a ray by e^(kx)·x^p·log(x)^m times an enclosed
coefficient, and the tail of an integral is bounded in closed form from that.
Divergence is proven the same way (the p-test with certified constants). The
special functions are enclosed by Stirling series with their proven error term
or by entire series, and they differentiate, integrate and find zeros like the
elementary ones. Integrals in several variables use product rules with error
terms from certified Taylor coefficients, over boxes, iterated bounds or
Core's multi-variable regions. Each topic has a page with a runnable example
at [ratmath.com/analytic](https://ratmath.com/analytic/).

## Not yet done

- Proving the existence of multiple roots of non-polynomial functions (they
  are reported as `possible` with `atMost`), and endpoints of the domain as
  features (open or closed dots are left to the caller).
- Complex analytic functions (contour integrals, residues).
- Limits that need a cancellation of leading terms (`sqrt(x^2 + x) - x`) are
  refused, and conditionally convergent integrals (`sin(x)/x` to infinity)
  come back as `undecided`. Asymptotics do not follow the special functions.
- Speed of the harder problems: a surface integral over a sphere takes about
  20 s for 4 digits, and a nonlinear boundary value problem can take minutes,
  because every shot is a validated ODE solve.
- A zero that sits exactly on an end of the search interval can come back as
  `possible` instead of proven.
- Speed: each elementary composition costs about 10 ms at order 8, so a
  certified range over 26 pieces takes about 0.8 s. Keep certified work in a
  Worker; previews are instant.

## Tests

```sh
bun test tests/
```
