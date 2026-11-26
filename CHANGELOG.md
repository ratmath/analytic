# Changelog

## Unreleased

### Fixed

- `atan` at a point whose denominator is longer than the working precision
  (a fraction with dozens of digits, as products of other results often are) no
  longer recurses until the stack overflows. The point was rounded to a dyadic
  one and then, about half the time, taken to need rounding again.
- A function that is identically zero (`x - x`, `0*sin(x)`) no longer reports
  zeros, extrema or inflections one by one: `zeros` returns one `everywhere`
  record and `extrema` one `constant` record.
- `exp` of large arguments (`exp(100)`, `2^400`) and `log` of tiny ones
  (`log(10^-300)`) return tight enclosures instead of an error or a long wait.
- A high-precision call no longer slows later low-precision calls: π and
  log 2 are cached per precision.
- Zeros that sit exactly on a bisection point (`sin(pi*x)` at 1, 2, 3) are
  proven unique instead of reported as `possible`, and are not listed twice.
- `simplify` keeps `x/x` and `log(x) - log(x)`, which are not defined
  everywhere, and still cancels `sin(x) - sin(x)`.
- The parser reports `3.5.2` and reads `sinx` as `sin(x)`.

### Added

- Sequences and series (roadmap 13.4): `sequence` (exact terms, proven
  limits, `monotone`, `bounds`), `recursive` (fixed points with their
  multipliers, limits proven by contraction), `sum` (the nth-term, ratio,
  root, comparison, integral and alternating tests as methods that return
  their verdict and the quantity that decided it; `convergence()`; `sum()` as
  finitely many terms plus a proven interval for the tail), `powerSeries`
  (radius, interval of convergence with each end examined, term-by-term
  derivative and integral), `taylorRemainder` (Lagrange's bound beside the
  true error) and `functionSequence` (pointwise limits, the supremum of
  |f_n − f| enclosed, uniform convergence only with a proof).
- Theorems of vector calculus (roadmap 13.5): `greens`, `stokes` and
  `divergenceTheorem` enclose both sides of each theorem independently, with
  the boundary built from the region piece by piece, and report whether the
  enclosures meet. `changeOfVariables` returns the Jacobian, its determinant
  and the transformed integrand. `potential` decides whether a field is a
  gradient (true, false with a witness, or undecided) and finds the potential.
  `lagrange` returns certified candidates for constrained extremes.
- Differential geometry (roadmap 13.2), also at `@ratmath/analytic/geometry`:
  `curve` (speed, arc length, Frenet frame, curvature, torsion, osculating
  circle, evolute), `surface` (both fundamental forms, normal, Gaussian, mean
  and principal curvatures, each point classified) and `metric` (Christoffel
  symbols, Gaussian curvature from the metric alone, geodesics and parallel
  transport as validated solutions, geodesic curvature, and `gaussBonnet` as
  a checked statement). Formulas come out tidied by the new `tidy`.
- `ode.solve({ ..., track: false })` skips tracking the initial value.
- `enclose.gammaP(a, x)`, `enclose.gammaQ(a, x)` and `enclose.betaI(x, a, b)`:
  certified regularized incomplete gamma and beta functions, the cumulative
  probabilities behind the gamma, chi-square, beta, t and F distributions.
- Several variables: `field(text, vars)` with partials, gradients, Hessians,
  certified values over points and boxes, directional derivatives, ranges,
  classified critical points, and integrals over boxes, iterated bounds and
  Core's multi-variable regions; `divergence`, `curl`, `jacobian`,
  `lineIntegral` and `surfaceIntegral`.
- Limits at infinity and one-sided limits (`limit("inf")`,
  `limit(c, { side })`), `asymptotic()`, and `improperIntegral(a, b)` for
  infinite ends and integrable singularities, with proven divergence.
- Special functions in formulas and as point enclosures: `gamma`, `lgamma`,
  `digamma`, `trigamma`, `beta`, `besselJ`, `Si`, `fresnelS`, `fresnelC`,
  `erfc`; `bernoulli(m)`.
- `fourier(f, [a, b])`: certified Fourier coefficients, half-range series,
  partial sums and the mean-square error by Parseval.
- `bvp(spec)`: two-point boundary value problems for y″ = f(x, y, y′) by
  certified shooting.
- Docs pages for each of these.
- `asin`, `acos`, `cbrt` and `erf` as Taylor models, point enclosures
  (`enclose.*`), in expressions and in the evaluator scope. Powers with an odd
  denominator (`x^(1/3)`) are real roots, defined for negative arguments.
- Ranges and integrals across points where the function is not smooth
  (`abs(x)` over [-1, 2], `cbrt` across 0, `asin` up to ±1).
- `fn(...).limit(c)` and `fn(...).taylor(c, n)`, including removable points
  of quotients such as `sin(x)/x` and `x/(exp(x) - 1)` at 0.
- ODE steps follow the dependence on the initial value in a rotating frame,
  which keeps enclosures of rotating systems tight over long spans
  (`track: false` restores the plain steps). `until` may be less than `t0`.
- `simplify` is exported; derivatives are simplified.
- TypeScript declarations (`index.d.ts`) and a CI workflow.
- Docs pages link to GitHub, npm and the sibling libraries and carry
  descriptions for search and link previews.

### Changed

- `Refinement` and `live` now come from `@ratmath/core/refine` (Core 0.10.0),
  one class shared by every RatMath library. The exports here are unchanged.

## 0.1.0

First version: Taylor models, elementary functions, expressions, certified
values, ranges and integrals, zeros, poles, extrema and inflections, piecewise
functions, validated ODE steps.
