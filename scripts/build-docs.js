// Bundle the library (with @ratmath/core) for the docs site.
const out = await Bun.build({ entrypoints: ["./scripts/docs-entry.js"], outdir: "./docs/assets", naming: "analytic.js", target: "browser", format: "esm", minify: true });
if (!out.success) {
  for (const m of out.logs) console.error(m);
  process.exit(1);
}
console.log("docs/assets/analytic.js written");
