// Assemble docs/<page>.html from docs-src/layout.html and docs-src/pages/*.html.
// Each page is a plain HTML fragment; the nav, head and pager are shared.
import { readFileSync, writeFileSync } from "node:fs";
import { renderMath, addRunbox, stampAssets, stampLinks, KATEX_LINK } from "./docs-kit.js";
import { runCode } from "../docs/assets/runbox.js";

// Asset URLs carry a hash of the assets (stampAssets), so a browser never mixes
// a cached old script with a new page (GitHub Pages caches for ten minutes).
// Math in \( … \) and \[ … \] is typeset with KaTeX here; every page ends with
// the runnable code box (docs/assets/runbox.js, shared with the other docs).

export const PAGES = [
  { name: "intro", file: "index.html", title: "Introduction" },
  { name: "reference", title: "Reference" },
  { name: "explore", title: "Explore" },
  { group: "Ideas" },
  { name: "fast", title: "Fast, then certified" },
  { name: "models", title: "Taylor models" },
  { group: "Topics" },
  { name: "points", file: "values.html", title: "Values to many digits" },
  { name: "expressions", title: "Formulas and derivatives" },
  { name: "ranges", title: "Ranges and integrals" },
  { name: "zeros", title: "Zeros, poles and extrema" },
  { name: "piecewise", title: "Piecewise functions" },
  { name: "odes", title: "Differential equations" },
  { name: "bvp", title: "Boundary value problems" },
  { name: "methods", title: "First-order equations: the methods" },
  { name: "linearodes", title: "Linear equations and Laplace transforms" },
  { name: "switches", title: "Steps and impulses" },
  { name: "systems", title: "Systems in the plane" },
  { name: "seriessolutions", title: "Series solutions" },
  { name: "characteristics", title: "First-order equations: characteristics" },
  { name: "pdes", title: "Heat, waves and potentials" },
  { name: "several", title: "Several variables" },
  { name: "improper", title: "Limits and improper integrals" },
  { name: "special", title: "Special functions" },
  { name: "fourier", title: "Fourier series" },
  { name: "transforms", title: "The Fourier transform" },
  { name: "dft", title: "The discrete Fourier transform" },
  { name: "series", title: "Your own series" },
  { name: "sequences", title: "Sequences" },
  { name: "epsilon", title: "ε, N and δ, with certificates" },
  { name: "sums", title: "Series and convergence tests" },
  { name: "power", title: "Power series and uniform convergence" },
  { name: "theorems", title: "Green, Stokes and the divergence theorem" },
  { name: "multipliers", title: "Change of variables, potentials, multipliers" },
  { name: "curves", title: "Curves: length, curvature, torsion" },
  { name: "surfaces", title: "Surfaces and curvature" },
  { name: "geodesics", title: "Geodesics and Gauss-Bonnet" },
  { group: "Numerical methods" },
  { name: "floats", title: "Floating point, exactly" },
  { name: "rootmethods", title: "Root-finding methods" },
  { name: "descent", title: "Gradient descent" },
  { name: "interpolation", title: "Interpolation and approximation" },
  { name: "quadraturerules", title: "Differences and quadrature rules" },
  { name: "odemethods", title: "Euler to Runge-Kutta" },
];

export function buildPages() {
  const v = stampAssets("docs/assets");
  const layout = readFileSync("docs-src/layout.html", "utf8");
  const seeds = [];
  const pages = PAGES.filter((p) => p.name).map((p) => ({ ...p, file: p.file ?? `${p.name}.html` }));
  const fileOf = Object.fromEntries(pages.map((p) => [p.name, p.file]));
  for (const [i, p] of pages.entries()) {
    const src = readFileSync(`docs-src/pages/${p.name}.html`, "utf8");
    const wide = /<!-- wide: yes -->/.test(src) ? " wide" : "";
    const linked = src.replace(/<!-- wide: (yes|no) -->\n?/, "").replace(/href="#([a-z]+)"/g, (m, id) => (fileOf[id] ? `href="${fileOf[id]}"` : m));
    const boxed = addRunbox(linked, { lib: "<code>@ratmath/analytic</code> and Core's <code>R</code>, <code>Rational</code>, <code>RationalInterval</code>" });
    seeds.push({ page: p.name, seed: boxed.seed });
    const math = renderMath(boxed.html);
    const body = math.html;
    const options = pages.map((q) => `    <option value="${q.file}"${q === p ? " selected" : ""}>${q.title}</option>`).join("\n");
    const links = PAGES.map((q) => (q.group ? `    <div class="group">${q.group}</div>` : `    <a href="${fileOf[q.name]}"${q.name === p.name ? ' class="on" aria-current="page"' : ""}>${q.title}</a>`)).join("\n");
    const prev = pages[i - 1];
    const next = pages[i + 1];
    const pager = `${prev ? `<a class="prev" href="${prev.file}">← ${prev.title}</a>` : "<span></span>"}${next ? `<a class="next" href="${next.file}">${next.title} →</a>` : "<span></span>"}`;
    const html = layout
      .replaceAll("{{title}}", p.title)
      .replace("{{file}}", p.name === "intro" ? "" : `${p.name}.html`)
      .replace("{{katex}}", math.count ? KATEX_LINK : "")
      .replace("{{options}}", options)
      .replace("{{links}}", links)
      .replace("{{wide}}", wide)
      .replace("{{name}}", p.name)
      .replace("{{body}}", () => body.trimEnd())
      .replace("{{pager}}", pager);
    writeFileSync(`docs/${p.file}`, stampLinks(html, v));
  }
  return { count: pages.length, seeds };
}

/** Run every page's code box against the library; returns the number that threw. */
export async function checkSeeds(seeds, scope, { verbose = false } = {}) {
  let failed = 0;
  for (const { page, seed } of seeds) {
    const res = await runCode(seed, scope);
    if (res.error) {
      failed++;
      console.error(`✗ ${page}: ${res.error.name}: ${res.error.message}`);
    } else if (verbose) {
      console.log(`— ${page} (${res.ms.toFixed(0)} ms)`);
      for (const pr of res.prints) console.log(`  ${pr.text}`);
      if (res.hasValue) console.log(`  → ${res.type ? `${res.type} ` : ""}${res.text}`);
    }
  }
  return failed;
}

if (import.meta.main) console.log(`${buildPages().count} pages written to docs/`);
