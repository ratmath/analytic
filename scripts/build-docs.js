import { buildPages, checkSeeds } from "./build-pages.js";
// Bundle the library (with @ratmath/core) for the docs site. Names are kept so
// values show their class (Rational, RationalInterval, ...) in the code boxes.
// Identifiers are not minified: Bun 1.4 renames classes even with keepNames,
// and Core and the code boxes read class names (external QA review, 2026-11-28).
const out = await Bun.build({ entrypoints: ["./scripts/docs-entry.js"], outdir: "./docs/assets", naming: "analytic.js", target: "browser", format: "esm", minify: { whitespace: true, syntax: true, identifiers: false } });
if (!out.success) {
  for (const m of out.logs) console.error(m);
  process.exit(1);
}
console.log("docs/assets/analytic.js written");
const { count, seeds } = buildPages();
console.log(`${count} pages written to docs/`);
// Every page's code box must run.
// The boxes run against the emitted bundle, which is what the browser loads,
// after a mixed Integer/Rational check that catches bundling mistakes.
const scope = await import("../docs/assets/analytic.js");
{
  const q = new scope.Rational(65n, 2n);
  const got = [new scope.Rational(65n).roundTo(-1), q.add(q.floor()), new scope.Rational(q.floor()), q.floor().constructor.name].map(String).join(" ");
  if (got !== "70 129/2 32 Integer") {
    console.error(`✗ bundle arithmetic gave ${got}, want 70 129/2 32 Integer`);
    process.exit(1);
  }
}
const failed = await checkSeeds(seeds, scope, { verbose: process.argv.includes("--verbose") });
if (failed) {
  console.error(`${failed} code box(es) failed`);
  process.exit(1);
}
console.log(`${seeds.length} code boxes run without errors`);
