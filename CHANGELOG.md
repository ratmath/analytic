# Changelog

## Unreleased

### Fixed

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

## 0.1.0

First version: Taylor models, elementary functions, expressions, certified
values, ranges and integrals, zeros, poles, extrema and inflections, piecewise
functions, validated ODE steps.
