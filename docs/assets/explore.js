// The explore page: type a function (or a piecewise one), pick an interval,
// move parameter sliders, and ask questions. Every answer shows the float
// preview at once and the certified answer when it arrives.
import { A, h, plot, fmtQ, fmtIv, fmtF, widthOf, mono, recordTable, place, xOf, COLORS, curveOf } from "./ui.js?v=20ed5f3d56";

const STORE = "ratmath-analytic-explore-v1";
const QUESTIONS = [
  ["value", "f(x₀)"],
  ["range", "range"],
  ["integral", "∫"],
  ["zeros", "zeros"],
  ["extrema", "extrema"],
  ["inflections", "inflections"],
  ["poles", "poles & holes"],
  ["breaks", "breaks"],
  ["derivative", "f′"],
  ["model", "Taylor model"],
];
const EXAMPLES = [
  ["sin(a*x)*exp(-x^2/8)", "-6:6"],
  ["x^3 - 3x + a", "-3:3"],
  ["(x^2 - 1)/(x - 1) + sin(2x)/2", "-4:4"],
  ["tan(x)", "-4:4"],
  ["exp(-1/x^2)", "-2:2"],
  ["x - n if n:x:!n+1", "-3:3"],
  ["1 if 2n:x:!2n+1; -1 if 2n+1:x:!2n+2", "-4:4"],
  ["x^2 if _:x:1; 3 - x if 1:!x:2; a otherwise", "-2:4"],
  ["atan(x)/x if _:x:!0 || 0:!x:_; 1 otherwise", "-6:6"],
];

function load() {
  try {
    return JSON.parse(localStorage.getItem(STORE) ?? "null");
  } catch {
    return null;
  }
}
function save(s) {
  try {
    localStorage.setItem(STORE, JSON.stringify(s));
  } catch {
    /* private mode */
  }
}

export function explorer(el) {
  const state = Object.assign({ f: EXAMPLES[0][0], I: EXAMPLES[0][1], x0: "1/2", digits: 12, ask: ["zeros", "extrema", "integral"], params: { a: "1" } }, load() ?? {});
  const fIn = h("input", { class: "text wb-cmd", value: state.f, spellcheck: "false", autocomplete: "off", "aria-label": "function" });
  const iIn = h("input", { class: "text", value: state.I, spellcheck: "false", "aria-label": "interval", size: 10 });
  const xIn = h("input", { class: "text", value: state.x0, spellcheck: "false", "aria-label": "x0", size: 8 });
  const dIn = h("input", { type: "range", min: 2, max: 60, value: state.digits, "aria-label": "digits" });
  const dOut = h("output", {}, String(state.digits));
  const sliders = h("div", { class: "params" });
  const status = h("div", { class: "small muted" });
  const canvas = h("canvas", { class: "plot tall", role: "img", "aria-label": "plot of f" });
  const floatBox = h("div", { class: "stage-body" });
  const exactBox = h("div", { class: "stage-body" });
  const exactMeta = h("span", { class: "meta" });
  const exactStage = h("div", { class: "stage exact" }, h("div", { class: "stage-head" }, h("span", { class: "chip exact" }, "certified"), exactMeta), exactBox);
  const qButtons = QUESTIONS.map(([id, label]) => {
    const b = h("button", { class: state.ask.includes(id) ? "toggle on" : "toggle", "aria-pressed": String(state.ask.includes(id)) }, label);
    b.addEventListener("click", () => {
      state.ask = state.ask.includes(id) ? state.ask.filter((x) => x !== id) : [...state.ask, id];
      b.classList.toggle("on", state.ask.includes(id));
      b.setAttribute("aria-pressed", String(state.ask.includes(id)));
      update();
    });
    return b;
  });
  const examples = EXAMPLES.map(([f, I]) =>
    h("button", { class: "wb-example", onclick: () => ((fIn.value = f), (iIn.value = I), update()) }, f),
  );

  el.replaceChildren(
    h(
      "div",
      { class: "wb" },
      h("div", { class: "wb-cmdrow" }, h("span", { class: "wb-label" }, "f(x) ="), fIn),
      h("div", { class: "wb-examples" }, h("span", { class: "wb-label" }, "Try"), examples),
      h(
        "div",
        { class: "wb-settings" },
        h("label", { class: "wb-check" }, "interval ", iIn),
        h("label", { class: "wb-check" }, "x₀ ", xIn),
        h("label", { class: "wb-check slider" }, "digits ", dIn, " ", dOut),
      ),
      sliders,
      h("div", { class: "wb-buttons" }, h("span", { class: "wb-label" }, "Ask"), qButtons),
      canvas,
      status,
      h("div", { class: "explore-out" }, h("div", { class: "stage float" }, h("div", { class: "stage-head" }, h("span", { class: "chip float" }, "preview")), floatBox), exactStage),
    ),
  );

  for (const inp of [fIn, iIn, xIn]) inp.addEventListener("input", () => update());
  dIn.addEventListener("input", () => {
    dOut.textContent = dIn.value;
    update();
  });

  let ctrl = null;
  let timer = null;
  let results = {};
  let F = null;
  let lo = -1;
  let hi = 1;

  function paramNames(text) {
    try {
      const pieces = A.parsePiecewiseText?.(text);
      const asts = pieces ? pieces.flatMap(([r, rule]) => [A.parse(rule), ...regionAsts(r)]) : [A.parse(text)];
      const names = new Set();
      for (const a of asts) for (const n of A.freeVariables(a)) names.add(n);
      names.delete("x");
      // integer variables of regions are not parameters
      if (pieces) for (const [r] of pieces) for (const n of regionInts(r)) names.delete(n);
      return [...names];
    } catch {
      return Object.keys(state.params);
    }
  }
  const regionAsts = (r) => {
    try {
      return r.split("||").flatMap((alt) => alt.split(":").map((s) => s.replace(/^!/, "").trim()).filter((s) => s && s !== "_" && s !== "x" && !/^(all|else|otherwise)$/.test(s)).map((s) => A.parse(s)));
    } catch {
      return [];
    }
  };
  const regionInts = (r) => {
    const names = new Set();
    for (const a of regionAsts(r)) for (const n of A.freeVariables(a)) names.add(n);
    return [...names].filter((n) => !(n in state.params) || n === "n" || n === "m" || n === "k");
  };

  function buildSliders(names) {
    const have = [...sliders.querySelectorAll("[data-param]")].map((x) => x.dataset.param);
    if (have.join() === names.join()) return;
    sliders.replaceChildren(
      ...names.map((n) => {
        const v = state.params[n] ?? "1";
        const steps = Math.round(Number(A.Rational.from(String(v)).toNumber()) * 8);
        const r = h("input", { type: "range", min: -40, max: 40, value: Number.isFinite(steps) ? steps : 8, "aria-label": n });
        const o = h("output", {}, v);
        r.addEventListener("input", () => {
          state.params[n] = `${r.value}/8`;
          o.textContent = fmtQ(A.Rational.from(state.params[n]));
          update();
        });
        state.params[n] = v;
        return h("label", { class: "field slider", "data-param": n }, h("span", {}, `${n} = `, o), r);
      }),
    );
  }

  function update() {
    state.f = fIn.value;
    state.I = iIn.value;
    state.x0 = xIn.value;
    state.digits = Number(dIn.value);
    save(state);
    ctrl?.abort();
    clearTimeout(timer);
    results = {};
    buildSliders(paramNames(state.f));
    const params = {};
    for (const n of paramNames(state.f)) params[n] = state.params[n] ?? "1";
    let tasks;
    try {
      F = A.fn(state.f, { params });
      const [a, b] = state.I.split(":").map((s) => s.trim());
      lo = A.Rational.from(a).toNumber();
      hi = A.Rational.from(b).toNumber();
      tasks = makeTasks(F, a, b, state);
      status.textContent = F.segments ? `piecewise: ${F.pieces.length} pieces` : `parsed: ${F.toString()}`;
    } catch (e) {
      status.replaceChildren(h("span", { class: "err" }, e.message));
      floatBox.replaceChildren();
      exactBox.replaceChildren();
      draw();
      return;
    }
    const rows = [];
    for (const t of tasks) {
      try {
        const qv = t.job.quick;
        results[t.id] = { quick: qv.value };
        rows.push(h("dt", {}, t.label), h("dd", {}, t.show(qv.value, false), " ", h("span", { class: `trust ${qv.trust}` }, qv.trust)));
      } catch (e) {
        rows.push(h("dt", {}, t.label), h("dd", { class: "err" }, e.message));
      }
    }
    floatBox.replaceChildren(h("dl", { class: "kv" }, rows));
    exactStage.classList.add("stale");
    exactMeta.textContent = "";
    exactMeta.classList.add("pending");
    draw();
    const mine = (ctrl = new AbortController());
    timer = setTimeout(async () => {
      const out = [];
      const t0 = performance.now();
      for (const t of tasks) {
        try {
          const value = await t.job.settle({
            signal: mine.signal,
            onProgress: (p) => {
              if (p.partial !== undefined) {
                results[t.id] = { ...(results[t.id] ?? {}), partial: p.partial };
              }
            },
          });
          results[t.id] = { ...(results[t.id] ?? {}), exact: value };
          out.push(h("dt", {}, t.label), h("dd", {}, t.show(value, true), h("div", { class: "small muted" }, t.job.exactStage().via ?? "")));
        } catch (e) {
          if (e?.name === "AbortError") return;
          out.push(h("dt", {}, t.label), h("dd", { class: "err" }, e.message));
        }
        if (mine.signal.aborted) return;
        exactBox.replaceChildren(h("dl", { class: "kv" }, out));
        draw();
      }
      exactStage.classList.remove("stale");
      exactMeta.classList.remove("pending");
      exactMeta.textContent = `${(performance.now() - t0).toFixed(0)} ms`;
    }, 150);
  }

  function draw() {
    if (!F) return plot(canvas, { x: [lo, hi], curves: [] });
    const curves = [curveOf(F)];
    const pts = [];
    const vlines = [];
    const pick = (k) => results[k]?.exact ?? results[k]?.quick;
    const add = (list, kind, color) => {
      for (const r of list ?? []) {
        const x = xOf(r);
        const y = kind === "zeros" ? 0 : r.value && typeof r.value === "object" ? r.value.low.toNumber() : F.float(x);
        if (kind === "extrema" && r.kind === "flat") continue;
        pts.push({ x, y, kind: r.kind === "possible" ? "open" : "dot", color });
      }
    };
    add(pick("zeros"), "zeros", COLORS.fn);
    add(pick("extrema"), "extrema", COLORS.extreme);
    add(pick("inflections"), "inflections", COLORS.inflection);
    for (const p of results.poles?.exact ?? []) {
      if (p.kind === "hole") pts.push({ x: xOf(p), y: p.value.low.toNumber(), kind: "open", color: COLORS.fn });
      else vlines.push({ x0: p.lo.toNumber(), x1: p.hi.toNumber(), color: COLORS.bad });
    }
    for (const b of results.breaks?.exact ?? []) {
      const x = b.at.toNumber();
      for (const side of [b.left, b.right]) if (side && (!b.value || side.low.compareTo(b.value.low) !== 0)) pts.push({ x, y: side.low.toNumber(), kind: "open", color: COLORS.fn });
      if (b.value) pts.push({ x, y: b.value.low.toNumber(), kind: "dot", color: COLORS.fn });
    }
    if (results.derivative) {
      const D = F.derivative();
      curves.push({ f: (x) => D.float(x), color: COLORS.extreme, width: 1.3, dash: [4, 3] });
    }
    const bands = [];
    const r = results.range?.exact;
    if (r) bands.push({ x0: lo, x1: hi, y0: r.low.toNumber(), y1: r.high.toNumber(), color: COLORS.band });
    plot(canvas, { x: [lo, hi], curves, points: pts, vlines, bands });
  }

  new ResizeObserver(() => draw()).observe(canvas);
  update();
}

function makeTasks(F, a, b, st) {
  const iv = [a, b];
  const digits = st.digits;
  const recCols = (extra = []) => [["kind", (r) => r.kind], ["where", place], ...extra];
  const all = {
    value: () => ({ label: `f(${st.x0})`, job: F.value(st.x0, { digits }), show: ivOrNum }),
    range: () => ({ label: `range on [${a}, ${b}]`, job: F.range(A.R`${a}:${b}`, { digits: Math.min(digits, 8) }), show: ivOrNum }),
    integral: () => ({ label: `∫ from ${a} to ${b}`, job: F.integral(a, b, { digits }), show: ivOrNum }),
    zeros: () => ({ label: "zeros", job: A.zeros(F, iv), show: (v) => recordTable(v, recCols([["mult.", (r) => r.multiplicity ?? (r.atMost ? `≤ ${r.atMost}` : "")], ["unique", (r) => (r.unique ? "yes" : "")]])) }),
    extrema: () => ({ label: "extrema", job: A.extrema(F, iv), show: (v) => recordTable(v, recCols([["value", (r) => (r.value === undefined ? "" : typeof r.value === "number" ? fmtF(r.value) : fmtIv(r.value))]])) }),
    inflections: () => ({ label: "inflections", job: A.inflections(F, iv), show: (v) => recordTable(v, recCols()) }),
    poles: () => ({ label: "poles & holes", job: A.poles(F, iv), show: (v, ex) => (ex ? recordTable(v, recCols([["order / limit", (r) => r.order ?? (r.value ? fmtIv(r.value) : "")]])) : h("span", { class: "muted" }, "certified only")) }),
    breaks: () => (F.breaks ? { label: "breaks", job: F.breaks(iv), show: (v, ex) => (ex ? recordTable(v, [["at", (r) => fmtQ(r.at)], ["kind", (r) => r.kind], ["value", (r) => (r.value ? fmtIv(r.value) : "undefined")], ["left", (r) => (r.left ? fmtIv(r.left) : "–")], ["right", (r) => (r.right ? fmtIv(r.right) : "–")]]) : h("span", { class: "muted" }, "certified only")) } : null),
    derivative: () => {
      const D = F.derivative();
      return { label: "f′", job: D.value(st.x0, { digits }), show: (v, ex) => h("div", {}, mono(D.toString()), h("div", { class: "small" }, `at ${st.x0}: `, ex ? fmtIv(v) : fmtF(v))) };
    },
    model: () => {
      if (F.segments) return null;
      const job = new A.Refinement(
        () => ({ value: "order 8 model on the interval", trust: "good" }),
        function* () {
          const m = F.model(A.R`${a}:${b}`, { order: 8 });
          return { value: m, via: m.notes.join(", ") };
        },
      );
      return { label: "Taylor model", job, show: (v, ex) => (ex ? h("div", { class: "lines" }, h("div", {}, `about ${fmtQ(v.centre)}`), v.coefficients.map((c, j) => h("div", {}, `a${j} = ${fmtQ(c, 12)}`)), h("div", {}, `remainder ${fmtIv(v.remainder)}`)) : v) };
    },
  };
  return st.ask.map((id) => {
    const t = all[id]?.();
    return t ? { id, ...t } : null;
  }).filter(Boolean);
}

const ivOrNum = (v, exact) =>
  exact ? h("span", {}, mono(fmtIv(v)), " ", h("span", { class: "muted small" }, widthOf(v))) : mono(Array.isArray(v) ? `[${v.map(fmtF).join(", ")}]` : fmtF(v));
