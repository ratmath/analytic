// Assemble docs/<page>.html from docs-src/layout.html and docs-src/pages/*.html.
// Each page is a plain HTML fragment; the nav, head and pager are shared.
import { readFileSync, writeFileSync } from "node:fs";

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
  const layout = readFileSync("docs-src/layout.html", "utf8");
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
