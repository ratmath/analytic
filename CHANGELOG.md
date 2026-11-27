# Changelog

## Unreleased

- Review of batch A6 (Course Test B1):
  - `darboux` on a piece where f′ cannot be enclosed (a corner such as |x| at 0,
    or a cusp) no longer takes the end values as inf and sup: the range of f is
    bounded by interval subdivision, and the sums are labelled enclosures.
  - `termsForError` searches forward correctly from a negative starting index.
- Helpers from the Course Test roadmap (batch A6):
  - `Series#termsForError(ε)`: for an alternating series, the first N whose
    error bound |a(N + 1)| is at most ε, found by doubling and bisection from
    the index where the term sizes are proven to decrease.
  - `newton(f, x0, { exact: true })` iterates in exact fractions, with the
    length of each denominator and the double iterates from the same start
    for comparison.
  - `darboux(f, partition)`: lower and upper Darboux sums, exact where f is
    proven monotone on every piece, otherwise certified enclosures from the
    end values and critical points.
  - `classifyPDE({ A, B, C })` (also `pde.classify`, with the PDE solvers in
    the `pde` namespace): hyperbolic, parabolic or elliptic from B² − 4AC,
    with the region of each type when the coefficients depend on x and y.
  - `constantRational(tree, env)` evaluates with exact variable values.
- `gradientDescent(f, start, { method })` (Course Test batch A8): fixed
  steps, Armijo backtracking, or the exact line search for quadratics; exact
  rational iterates for polynomial objectives; labelled `simulated`. New docs
  page "Gradient descent".
- Types: the curve and surface parameter type is now `ParameterLike`. It was a
  second `PointLike`, which clashed with the scalar-field `PointLike`, so
  TypeScript reported a duplicate identifier in `index.d.ts`.
- Fixes found by the Course Test (ratmath/shelf#7):
  - `newton`, `secant`, `fixedPoint` and `bisection` read an exact starting
    value (`"1/2"`, ``R`1/2` ``) exactly; `Number("1/2")` was NaN and the root
    came back null without an error. The same for `sturmLiouville`'s `from`
    and `to`.
  - `functionSequence(...).pointwise(x)` substitutes x; it was passed as a
    parameter the limit code never used, so `x^n` threw. 1^n and 0^n are
    folded first, so the limit of x^n is found at x = 0 and x = 1 too.
  - The parser reads `sec csc cot sech csch coth asinh acosh atanh` (as
    1/cos(u) and so on); `sec(x)` used to be the product sec·x. An unknown
    name of three or more letters against `(` is refused instead of becoming
    a product.
  - `firstOrder` solves linear equations whose integrating factor is
    exp(−log|u|): it takes 1/u (any constant multiple of an integrating factor
    is one), so y′ = (x + y)/x gives y = x·log|x| + C·x instead of nothing.
  - `ODESolution` is exported, as `index.d.ts` says.

- `seriesSolution` now proves its remainder. Each solution has
  `remainder(ρ)`, a rational bound for all the terms left out that holds on
  the whole complex disc of radius ρ about the point, and `enclose(x)`, the
  partial sum at a rational point with that bound on either side. The result
  also has `provenRadius`, a proven lower bound for the distance to the
  nearest other singular point (by Graeffe root squaring, in exact
  arithmetic). The bound comes from the recurrence itself: Cauchy-type
  bounds on the coefficients of x·p and x²·q, then a comparison sum.

- `@ratmath/core` is now a peer dependency (`>=0.10.0 <0.12.0`): the package
  uses the program's own copy of Core instead of bringing its own, so Core 0.11
  works and there is never a second copy whose `Rational` is not the same class.

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

- Steps and impulses in Laplace transforms (roadmap 13.6 leftovers):
  `laplace` reads `heaviside(t - c)` (both `heaviside(t - c)*g(t)` and the
  textbook `heaviside(t - c)*f(t - c)`) and `dirac(t - c)`; `inverseLaplace`
  reads delays `exp(-c*s)` and returns `heaviside`/`dirac` terms, including a
  `dirac(t)` for a constant polynomial part. New `laplaceSolve(coefficients,
  forcing, initial)` solves constant-coefficient equations with switched or
  impulsive forcing and verifies the answer piece by piece, with the jump an
  impulse puts into the top derivative.
- `linearSystem` beyond 2 by 2: the characteristic polynomial, exact
  eigenvalues where it splits, `e^{At}` as the inverse Laplace transform of
  `(sI − A)⁻¹` (verified by `d/dt E = AE`, `E(0) = I`), and stability from
  exact signs with a rank test for repeated eigenvalues on the imaginary axis.

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
- Differential equations (roadmap 13.1). Solution methods with their steps:
  `firstOrder` (linear, separable, Bernoulli, homogeneous), `exactEquation`
  (with integrating factors) and `linearODE` (characteristic roots,
  undetermined coefficients with resonance, variation of parameters, initial
  values); each formula has a `check` against the validated numerical
  solution. `laplace` and `inverseLaplace`. `linearSystem` (2 by 2: exact
  e^{At}, the equilibrium classified) and `planarSystem` (every equilibrium in
  a box proven and classified, conserved quantities). `seriesSolution` at
  ordinary and regular singular points (Frobenius). `heat`, `laplaceRectangle`
  and `laplaceDisc` by separation of variables with a proven bound on the
  tail; `wave` by d'Alembert's formula; `sturmLiouville` eigenvalues by
  shooting, each bracketed by two validated solutions. `antiderivative` and
  `partialFractions` are the integrals the methods use.
- Fourier transforms (roadmap 13.6), also at `@ratmath/analytic/transform`:
  `fourierTransform` gives F(ω) as two certified improper integrals and, for
  the standard pairs with the shift and multiply-by-x rules, a formula that
  is checked against those integrals before it is returned; three
  conventions. `parseval()` and `inversion(x)` are checked statements,
  `convolution(f, g).theorem(x)` checks the convolution theorem, and
  `heatLine` solves the heat equation on the whole line two ways. `dft` and
  `fft` work exactly in the field of n-th roots of unity (`Cyclotomic`,
  `rootOfUnity`, `cyclotomic`), with the fast algorithm's count beside n²;
  `alias`, `sinusoidSamples` and `sample` for sampling.
- Numerical analysis for teaching (roadmap 13.3), also at
  `@ratmath/analytic/methods`: the textbook methods run as a program would
  run them, each beside the certified answer so the error shown is the true
  one. `floatParts`, `exactOf`, `nearestDouble`, `floatOp` and `roundoff`
  for floating point; `bisection`, `newton`, `secant`, `fixedPoint` with the
  observed order; `interpolate` (divided differences, Newton and Lagrange
  forms, the true maximum error beside the textbook bound), `equallySpaced`,
  `chebyshevNodes`, `spline`, `leastSquares`; `differences`, `richardson`,
  `quadratureRule`, `romberg`, `legendre`, `gaussLegendre`, `gaussRule`;
  `odeMethod`, `stepSizeStudy` and `stability`.
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
