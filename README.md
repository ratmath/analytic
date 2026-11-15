# @ratmath/analytic

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
| Elementary | `exp`, `sin`, `cos`, `tan`, `log`, `log1p`, `atan`, `sqrt`, `sinh`, `cosh`, `tanh`, `reciprocal`, `power(g, a)` |
| Evaluation | `.at(point or sub-interval)`, `.range({ depth })` |
| Calculus | `.integrate()`, `.integral(a, b)`, `.derivative()` (exact models only; see below) |
| User series | `series(D, { coefficient: k => a_k, order, rule, … })` |
| Point values | `enclose.exp(x, bits)` etc., `constants.pi(bits)`, `constants.e(bits)` |
| Evaluator scope | `createScope({ digits })` |

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

## Not yet done (phases 4–6 of the design note)

- Expression front end and symbolic `d/dx` (rebuild models of derivatives).
- Validated ODE steps (Picard iteration with Taylor models).

## Tests

```sh
bun test tests/
```
