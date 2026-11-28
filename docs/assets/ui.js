// UI pieces for the docs: element builder, number formatting, a canvas plot,
// and the demo card (inputs on the left; float preview, then certified answer).
import * as A from "./analytic.js?v=1bcf8ad89e";

export { A };

export const h = (tag, attrs = {}, ...kids) => {
  const el = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (v === null || v === undefined || v === false) continue;
    if (k === "class") el.className = v;
    else if (k.startsWith("on")) el.addEventListener(k.slice(2), v);
    else el.setAttribute(k, v === true ? "" : v);
  }
  for (const kid of kids.flat(Infinity)) if (kid !== null && kid !== undefined && kid !== false) el.append(kid instanceof Node ? kid : document.createTextNode(String(kid)));
  return el;
};

// ---- formatting -------------------------------------------------------------

const isQ = (v) => v && typeof v === "object" && typeof v.numerator === "bigint";
const isIv = (v) => v && typeof v === "object" && "low" in v && "high" in v && isQ(v.low);

/** A Rational: the fraction when short, else a decimal with "…". */
export function fmtQ(q, digits = 20) {
  if (!isQ(q)) return String(q);
  const s = q.toString();
  if (s.length <= 24) return s;
  const n = q.toNumber();
  if (Number.isFinite(n) && Math.abs(n) > 1e-300) return n.toPrecision(Math.min(digits, 17)) + "…";
  return q.toDecimal ? q.toDecimal(digits) + "…" : s;
}

/** A RationalInterval in RatMath's compact notation: 0.46235716975[69:70]. */
export function fmtIv(iv) {
  if (!isIv(iv)) return isQ(iv) ? fmtQ(iv) : String(iv);
  if (iv.low.compareTo(iv.high) === 0) return fmtQ(iv.low);
  try {
    const s = String(iv.compactedDecimalInterval());
    if (s.length <= 90) return s;
  } catch {
    /* fall through */
  }
  return `[${fmtQ(iv.low, 12)}, ${fmtQ(iv.high, 12)}]`;
}

export function widthOf(iv) {
  if (!isIv(iv)) return "";
  const w = iv.high.subtract(iv.low).toNumber();
  return w === 0 ? "exact" : `width ${w.toExponential(1)}`;
}

export const fmtF = (x) => (typeof x !== "number" ? String(x) : Number.isFinite(x) ? (Number.isInteger(x) ? String(x) : x.toPrecision(15).replace(/\.?0+$/, "")) : String(x));

// ---- plot ---------------------------------------------------------------------

const css = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim() || "#888";

/**
 * Plot into a canvas.
 *   curves: [{ f: x => number, color, width }]
 *   bands:  [{ x0, x1, y0, y1, color }]        rectangles in data space (certified boxes)
 *   points: [{ x, y, kind: "dot" | "open" | "ring", color, r }]
 *   vlines: [{ x0, x1, color }]                 shaded vertical strips (brackets)
 */
export function plot(canvas, { x: [xa, xb], y, curves = [], bands = [], points = [], vlines = [], samples = 600 }) {
  const dpr = window.devicePixelRatio || 1;
  const W = canvas.clientWidth || 600;
  const H = canvas.clientHeight || 280;
  canvas.width = Math.round(W * dpr);
  canvas.height = Math.round(H * dpr);
  const g = canvas.getContext("2d");
  g.setTransform(dpr, 0, 0, dpr, 0, 0);
  g.clearRect(0, 0, W, H);
  // sample curves first to choose y-range
  const data = curves.map((c) => {
    const xs = new Float64Array(samples + 1);
    const ys = new Float64Array(samples + 1);
    const keys = c.key ? new Array(samples + 1) : null;
    for (let i = 0; i <= samples; i++) {
      const x = xa + ((xb - xa) * i) / samples;
      xs[i] = x;
      let v;
      try {
        v = c.f(x);
      } catch {
        v = NaN;
      }
      ys[i] = v;
      if (keys) {
        try {
          keys[i] = c.key(x);
        } catch {
          keys[i] = null;
        }
      }
    }
    return { xs, ys, keys, c };
  });
  let [ya, yb] = y ?? autoRange(data);
  if (!(yb > ya)) [ya, yb] = [ya - 1, ya + 1];
  const px = (x) => ((x - xa) / (xb - xa)) * W;
  const py = (v) => H - ((v - ya) / (yb - ya)) * H;
  // grid and axes
  g.lineWidth = 1;
  g.strokeStyle = css("--line");
  g.fillStyle = css("--muted");
  g.font = "11px " + css("--font-mono");
  for (const t of ticks(xa, xb, 8)) {
    g.beginPath();
    g.moveTo(px(t) + 0.5, 0);
    g.lineTo(px(t) + 0.5, H);
    g.stroke();
    g.fillText(fmtTick(t), px(t) + 3, H - 4);
  }
  for (const t of ticks(ya, yb, 6)) {
    g.beginPath();
    g.moveTo(0, py(t) + 0.5);
    g.lineTo(W, py(t) + 0.5);
    g.stroke();
    g.fillText(fmtTick(t), 3, py(t) - 3);
  }
  g.strokeStyle = css("--muted");
  if (ya < 0 && yb > 0) {
    g.beginPath();
    g.moveTo(0, py(0) + 0.5);
    g.lineTo(W, py(0) + 0.5);
    g.stroke();
  }
  if (xa < 0 && xb > 0) {
    g.beginPath();
    g.moveTo(px(0) + 0.5, 0);
    g.lineTo(px(0) + 0.5, H);
    g.stroke();
  }
  for (const v of vlines) {
    g.fillStyle = v.color ?? css("--accent-soft");
    const a = px(v.x0);
    const b = Math.max(px(v.x1), a + 2);
    g.fillRect(a - 1, 0, b - a + 2, H);
  }
  for (const b of bands) {
    g.fillStyle = b.color ?? css("--exact-soft");
    g.globalAlpha = b.color ? 0.35 : 1; // explicit colours are solid tokens: let the curve show through
    const x0 = px(b.x0);
    const x1 = px(b.x1);
    const y0 = py(Math.max(b.y1, ya - (yb - ya)));
    const y1 = py(Math.min(b.y0, yb + (yb - ya)));
    g.fillRect(x0, y0, Math.max(1, x1 - x0), Math.max(1, y1 - y0));
  }
  g.globalAlpha = 1;
  for (const { xs, ys, keys, c } of data) {
    g.strokeStyle = c.color ?? css("--accent");
    g.lineWidth = c.width ?? 2;
    g.setLineDash(c.dash ?? []);
    g.beginPath();
    let pen = false;
    for (let i = 0; i < xs.length; i++) {
      const v = ys[i];
      const jump = i > 0 && (Math.abs(v - ys[i - 1]) > (yb - ya) * 0.8 || (keys && keys[i] !== keys[i - 1]));
      if (!Number.isFinite(v) || jump) {
        pen = Number.isFinite(v) && jump ? (g.moveTo(px(xs[i]), py(v)), true) : false;
        continue;
      }
      if (!pen) g.moveTo(px(xs[i]), py(v));
      else g.lineTo(px(xs[i]), py(v));
      pen = true;
    }
    g.stroke();
    g.setLineDash([]);
  }
  for (const p of points) {
    if (!Number.isFinite(p.x) || !Number.isFinite(p.y)) continue;
    const r = p.r ?? 4.5;
    g.beginPath();
    g.arc(px(p.x), py(p.y), r, 0, Math.PI * 2);
    if (p.kind === "open") {
      g.fillStyle = css("--surface");
      g.fill();
      g.lineWidth = 2;
      g.strokeStyle = p.color ?? css("--accent");
      g.stroke();
    } else {
      g.fillStyle = p.color ?? css("--accent");
      g.fill();
    }
  }
  return { px, py, ya, yb };
}

function autoRange(data) {
  const vals = [];
  for (const d of data) for (const v of d.ys) if (Number.isFinite(v)) vals.push(v);
  if (!vals.length) return [-1, 1];
  vals.sort((a, b) => a - b);
  // ignore the extreme 2% so poles do not flatten the picture
  const lo = vals[Math.floor(vals.length * 0.02)];
  const hi = vals[Math.ceil(vals.length * 0.98) - 1];
  const pad = (hi - lo) * 0.12 || 1;
  return [lo - pad, hi + pad];
}

function ticks(a, b, n) {
  const span = b - a;
  const step0 = span / n;
  const mag = 10 ** Math.floor(Math.log10(step0));
  const step = [1, 2, 5, 10].map((m) => m * mag).find((s) => span / s <= n) ?? 10 * mag;
  const out = [];
  for (let t = Math.ceil(a / step) * step; t <= b; t += step) out.push(Math.abs(t) < step * 1e-9 ? 0 : t);
  return out;
}
const fmtTick = (t) => (Math.abs(t) >= 1e4 || (Math.abs(t) < 1e-3 && t !== 0) ? t.toExponential(0) : String(+t.toPrecision(4)));

/** Plot colours: function, extrema darker, inflections lighter, zeros the function colour. */
export const COLORS = {
  get fn() { return css("--accent"); },
  get extreme() { return css("--accent-dark"); },
  get inflection() { return css("--accent-light"); },
  get exact() { return css("--exact"); },
  get band() { return css("--exact-soft"); },
  get float() { return css("--float"); },
  get bad() { return css("--bad"); },
  get muted() { return css("--muted"); },
};

// ---- demo cards -----------------------------------------------------------------

/**
 * demo(el, {
 *   title, inputs: [{ id, label, value, kind: "text" | "range" | "select", min, max, step, options }],
 *   tasks: (vals) => [{ label, job: Refinement, show: (value, exact) => Node|string }],
 *   draw: (canvas, vals, results) => void   // results: { [label]: { quick, exact } }
 *   note
 * })
 */
export function demo(el, spec) {
  const vals = {};
  const fields = spec.inputs.map((inp) => {
    vals[inp.id] = inp.value;
    let control;
    const out = h("output", {}, inp.kind === "range" ? rangeLabel(inp, inp.value) : "");
    if (inp.kind === "range") {
      control = h("input", { type: "range", min: inp.min, max: inp.max, step: inp.step ?? 1, value: inp.value, "aria-label": inp.label });
      control.addEventListener("input", () => {
        vals[inp.id] = control.value;
        out.textContent = rangeLabel(inp, control.value);
        update();
      });
    } else if (inp.kind === "select") {
      control = h("select", { "aria-label": inp.label }, inp.options.map((o) => h("option", { value: o, selected: o === inp.value }, o)));
      control.addEventListener("change", () => {
        vals[inp.id] = control.value;
        update();
      });
    } else {
      control = h("input", { class: "text", value: inp.value, spellcheck: "false", autocomplete: "off", "aria-label": inp.label });
      control.addEventListener("input", () => {
        vals[inp.id] = control.value;
        update();
      });
    }
    return h("label", { class: inp.kind === "range" ? "field slider" : "field" }, h("span", {}, inp.label, " ", out), control);
  });
  const canvas = spec.draw ? h("canvas", { class: "plot", role: "img", "aria-label": `${spec.title} plot` }) : null;
  const floatBody = h("div", { class: "stage-body" });
  const exactBody = h("div", { class: "stage-body" });
  const floatMeta = h("span", { class: "meta" });
  const exactMeta = h("span", { class: "meta" });
  const exactStage = h("div", { class: "stage exact" }, h("div", { class: "stage-head" }, h("span", { class: "chip exact" }, "certified"), exactMeta), exactBody);
  const card = h(
    "div",
    { class: "demo-card" },
    h("div", { class: "demo-title" }, spec.title),
    h(
      "div",
      { class: "demo-grid" },
      h("div", { class: "inputs" }, fields, spec.note ? h("p", { class: "small muted" }, spec.note) : null),
      h(
        "div",
        { class: "fast" },
        canvas,
        h("div", { class: "stage float" }, h("div", { class: "stage-head" }, h("span", { class: "chip float" }, "preview"), floatMeta), floatBody),
        exactStage,
      ),
    ),
  );
  el.replaceChildren(card);

  let ctrl = null;
  let timer = null;
  let results = {};
  const redraw = () => {
    if (!canvas) return;
    try {
      spec.draw(canvas, vals, results);
    } catch (e) {
      console.warn(e);
    }
  };
  function update() {
    ctrl?.abort();
    clearTimeout(timer);
    let tasks;
    results = {};
    try {
      tasks = spec.tasks(vals);
    } catch (e) {
      floatBody.replaceChildren(h("span", { class: "err" }, e.message));
      exactBody.replaceChildren();
      exactMeta.textContent = "";
      redraw();
      return;
    }
    const t0 = performance.now();
    const rows = tasks.map((t) => {
      let quick;
      try {
        quick = t.job.quick;
        results[t.label] = { quick: quick.value };
        return row(t.label, t.show(quick.value, false), h("span", { class: `trust ${quick.trust}` }, quick.trust));
      } catch (e) {
        return row(t.label, h("span", { class: "err" }, e.message));
      }
    });
    floatBody.replaceChildren(h("dl", { class: "kv" }, rows));
    floatMeta.textContent = `${(performance.now() - t0).toFixed(1)} ms`;
    exactStage.classList.add("stale");
    exactMeta.textContent = "";
    exactMeta.classList.add("pending");
    redraw();
    const mine = (ctrl = new AbortController());
    timer = setTimeout(async () => {
      const t1 = performance.now();
      const out = [];
      for (const t of tasks) {
        try {
          const value = await t.job.settle({ signal: mine.signal });
          results[t.label] = { ...(results[t.label] ?? {}), exact: value };
          const via = t.job.exactStage().via;
          out.push(row(t.label, t.show(value, true), via ? h("span", { class: "via small muted" }, via) : null));
        } catch (e) {
          if (e?.name === "AbortError") return;
          out.push(row(t.label, h("span", { class: "err" }, e.message)));
        }
        if (mine.signal.aborted) return;
        exactBody.replaceChildren(h("dl", { class: "kv" }, out));
        redraw();
      }
      exactStage.classList.remove("stale");
      exactMeta.classList.remove("pending");
      exactMeta.textContent = `${(performance.now() - t1).toFixed(0)} ms`;
    }, spec.idleMs ?? 120);
  }
  if (canvas) new ResizeObserver(() => redraw()).observe(canvas);
  update();
  return { update, vals };
}

function row(label, value, extra) {
  return [h("dt", {}, label), h("dd", {}, value, extra ? h("div", {}, extra) : null)];
}

function rangeLabel(inp, v) {
  return inp.format ? inp.format(v) : String(v);
}

/** Plain text node in monospace. */
export const mono = (s) => h("code", { class: "plain" }, s);

/** Records from zeros/extrema/... as a small table. */
export function recordTable(list, cols) {
  if (!list.length) return h("span", { class: "muted" }, "none");
  return h(
    "div",
    { class: "tablewrap" },
    h(
      "table",
      { class: "data" },
      h("tr", {}, cols.map((c) => h("th", {}, c[0]))),
      list.map((r) => h("tr", {}, cols.map((c) => h("td", {}, c[1](r))))),
    ),
  );
}

/** A plot curve for f; piecewise functions break the line where the piece changes. */
export const curveOf = (F, extra = {}) => ({
  f: (x) => F.float(x),
  key: F.locate
    ? (x) => {
        const at = F.locate(A.toRational(x));
        return at ? `${at.index}:${at.n ?? ""}` : null;
      }
    : undefined,
  ...extra,
});

/** Where a record sits: the exact point, or its bracket. */
export const place = (r) => {
  if (typeof r.at === "number") return Number.isInteger(r.at) ? String(r.at) : r.at.toPrecision(12).replace(/\.?0+$/, "");
  if (r.at !== undefined) return fmtQ(r.at);
  return fmtIv(new A.RationalInterval(r.lo, r.hi));
};
export const xOf = (r) => (typeof r.at === "number" ? r.at : r.at ? r.at.toNumber() : (r.lo.toNumber() + r.hi.toNumber()) / 2);
