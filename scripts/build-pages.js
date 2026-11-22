// Assemble docs/<page>.html from docs-src/layout.html and docs-src/pages/*.html.
// Each page is a plain HTML fragment; the nav, head and pager are shared.
import { readFileSync, writeFileSync, readdirSync } from "node:fs";
import { createHash } from "node:crypto";

// Stamp every asset URL with a hash of the assets, so a browser never mixes a
// cached old script with a new page (GitHub Pages caches for ten minutes).
const STAMP = /(\.(?:js|css))\?v=[0-9a-f]+/g;
function stampAssets() {
  const dir = "docs/assets";
  const files = readdirSync(dir).filter((f) => /\.(js|css)$/.test(f)).sort();
  const texts = Object.fromEntries(files.map((f) => [f, readFileSync(`${dir}/${f}`, "utf8")]));
  const hash = createHash("sha256");
  for (const f of files) hash.update(f).update(texts[f].replace(STAMP, "$1"));
  const v = hash.digest("hex").slice(0, 10);
  for (const f of files) {
    if (!f.endsWith(".js")) continue;
    const out = texts[f].replace(/(from\s+"\.\/[\w-]+\.js)(?:\?v=[0-9a-f]+)?"/g, `$1?v=${v}"`);
    if (out !== texts[f]) writeFileSync(`${dir}/${f}`, out);
  }
  return v;
}

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
  { name: "series", title: "Your own series" },
];

export function buildPages() {
  const v = stampAssets();
  const layout = readFileSync("docs-src/layout.html", "utf8").replace(/(assets\/[\w-]+\.(?:js|css))"/g, `$1?v=${v}"`);
  const pages = PAGES.filter((p) => p.name).map((p) => ({ ...p, file: p.file ?? `${p.name}.html` }));
  const fileOf = Object.fromEntries(pages.map((p) => [p.name, p.file]));
  for (const [i, p] of pages.entries()) {
    const src = readFileSync(`docs-src/pages/${p.name}.html`, "utf8");
    const wide = /<!-- wide: yes -->/.test(src) ? " wide" : "";
    const body = src.replace(/<!-- wide: (yes|no) -->\n?/, "").replace(/href="#([a-z]+)"/g, (m, id) => (fileOf[id] ? `href="${fileOf[id]}"` : m));
    const options = pages.map((q) => `    <option value="${q.file}"${q === p ? " selected" : ""}>${q.title}</option>`).join("\n");
    const links = PAGES.map((q) => (q.group ? `    <div class="group">${q.group}</div>` : `    <a href="${fileOf[q.name]}"${q.name === p.name ? ' class="on" aria-current="page"' : ""}>${q.title}</a>`)).join("\n");
    const prev = pages[i - 1];
    const next = pages[i + 1];
    const pager = `${prev ? `<a class="prev" href="${prev.file}">← ${prev.title}</a>` : "<span></span>"}${next ? `<a class="next" href="${next.file}">${next.title} →</a>` : "<span></span>"}`;
    const html = layout
      .replace("{{title}}", p.title)
      .replace("{{options}}", options)
      .replace("{{links}}", links)
      .replace("{{wide}}", wide)
      .replace("{{name}}", p.name)
      .replace("{{body}}", body.trimEnd())
      .replace("{{pager}}", pager);
    writeFileSync(`docs/${p.file}`, html);
  }
  return pages.length;
}

if (import.meta.main) console.log(`${buildPages()} pages written to docs/`);
