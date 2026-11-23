import { buildPages, checkSeeds } from "./build-pages.js";
// Bundle the library (with @ratmath/core) for the docs site. Names are kept so
// values show their class (Rational, RationalInterval, ...) in the code boxes.
const out = await Bun.build({ entrypoints: ["./scripts/docs-entry.js"], outdir: "./docs/assets", naming: "analytic.js", target: "browser", format: "esm", minify: { whitespace: true, syntax: true, identifiers: true, keepNames: true } });
if (!out.success) {
  for (const m of out.logs) console.error(m);
  process.exit(1);
}
console.log("docs/assets/analytic.js written");
const { count, seeds } = buildPages();
console.log(`${count} pages written to docs/`);
// Every page's code box must run.
const scope = await import("./docs-entry.js");
const failed = await checkSeeds(seeds, scope, { verbose: process.argv.includes("--verbose") });
if (failed) {
  console.error(`${failed} code box(es) failed`);
  process.exit(1);
}
console.log(`${seeds.length} code boxes run without errors`);
