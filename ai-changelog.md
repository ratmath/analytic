# AI changelog

## Declare Bun 1.4.2 in engines
**Model:** Claude Opus 5.5
**Date:** 2026-11-28

`engines` lists `"bun": ">=1.4.2"` next to Node 22, since Bun 1.4.0 caps BigInt at 2^20 bits and CI runs 1.4.2.

## Course Test helpers, batch A6 (Opus 5.5, 2026-11-27)

Added termsForError, exact Newton, Darboux sums and PDE classification for the Course Test roadmap.

`Series#termsForError`, `newton(..., { exact: true })`, `darboux` and `classifyPDE` (with a `pde` namespace) each have a test in tests/course-helpers.test.js against an independent computation, docs on the sums, root methods, quadrature rules and PDE pages, and typings.

## Course Test helpers, batch A8 (Opus 5.5, 2026-11-27)

Added `gradientDescent`, a simulated run of the method with exact iterates for polynomial objectives.

Fixed step, Armijo backtracking and the exact line search t = |g|²/(gᵀHg) for quadratics. New docs page docs-src/pages/descent.html; tests in tests/course-helpers.test.js.
