// Mounts the demos on each docs page and handles page switching.
import { A, h, demo, plot, fmtQ, fmtIv, fmtF, widthOf, mono, recordTable, place, xOf, COLORS, curveOf } from "./ui.js?v=5f551fee0b";
import { explorer } from "./explore.js?v=5f551fee0b";
import { MORE } from "./more-demos.js?v=5f551fee0b";
import { mountRunboxes } from "./runbox.js?v=5f551fee0b";

const { R, fn } = A;
const num = (s) => A.Rational.from ? A.Rational.from(String(s).trim()) : new A.Rational(String(s).trim());
const ivText = (lo, hi) => R`${lo}:${hi}`;
const ivShow = (v, exact) => (exact ? h("span", {}, mono(fmtIv(v)), " ", h("span", { class: "muted small" }, widthOf(v))) : mono(Array.isArray(v) ? `[${v.map(fmtF).join(", ")}]` : fmtF(v)));
const range2 = (s) => s.split(/[:,]/).map((t) => t.trim());

/** Markers for feature records on a plot (James's colour rules). */
function markers(F, recs, kind) {
  const pts = [];
  for (const r of recs ?? []) {
    const x = xOf(r);
    let y;
    try {
      y = F.float(x);
    } catch {
      y = NaN;
    }
    if (kind === "zeros") pts.push({ x, y: 0, kind: r.kind === "possible" ? "open" : "dot", color: COLORS.fn });
    if (kind === "extrema" && r.kind !== "flat") pts.push({ x, y, kind: r.kind === "possible" ? "open" : "dot", color: COLORS.extreme });
    if (kind === "inflections") pts.push({ x, y, kind: r.kind === "possible" ? "open" : "dot", color: COLORS.inflection });
  }
  return pts;
}

const DEMOS = {
  hero: (el) =>
    demo(el, {
      title: "A damped wave: drag a",
      inputs: [
        { id: "a", label: "a =", kind: "range", min: 1, max: 32, value: 12, format: (v) => `${v}/8` },
        { id: "f", label: "f(x)", value: "sin(a*x)*exp(-x^2/8)" },
      ],
      tasks: ({ a, f }) => {
        const F = fn(f, { params: { a: `${a}/8` } });
        return [
          { label: "zeros on [-5, 5]", job: A.zeros(F, [-5, 5], { tolerance: "1/1000000" }), show: (v, ex) => (ex ? `${v.length} (${v.filter((z) => z.unique).length} proven unique)` : `${v.length} guesses`) },
          { label: "∫ from -5 to 5", job: F.integral(-5, 5, { digits: 10 }), show: ivShow },
          { label: "range on [0, 5]", job: F.range(R`0:5`, { digits: 5 }), show: ivShow },
        ];
      },
      draw: (c, { a, f }, res) => {
        const F = fn(f, { params: { a: `${a}/8` } });
        const z = res["zeros on [-5, 5]"];
        plot(c, { x: [-5, 5], y: [-1.2, 1.2], curves: [curveOf(F)], points: markers(F, z?.exact ?? z?.quick, "zeros") });
      },
    }),

  stages: (el) =>
    demo(el, {
      title: "Preview, progress, certified",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(sin(3x))*x" },
        { id: "I", label: "interval", value: "0:3" },
        { id: "d", label: "digits", kind: "range", min: 2, max: 12, value: 6 },
      ],
      tasks: ({ f, I, d }) => {
        const [lo, hi] = range2(I);
        const job = fn(f).range(ivText(lo, hi), { digits: Number(d) });
        return [
          { label: "range", job, show: ivShow },
          {
            label: "stages",
            job: {
              get quick() {
                return { value: "float preview shown at once", trust: "good" };
              },
              settle: async () => {
                const ticks = [...job.stages()].filter((s) => s.stage === "progress").length;
                return `${ticks} progress ticks, each with a partial enclosure`;
              },
              exactStage: () => ({ via: "" }),
            },
            show: (v) => v,
          },
        ];
      },
    }),

  model: (el) =>
    demo(el, {
      title: "A Taylor model and its remainder",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(sin(x))" },
        { id: "D", label: "domain", value: "0:1" },
        { id: "n", label: "order", kind: "range", min: 0, max: 16, value: 4 },
      ],
      tasks: ({ f, D, n }) => {
        const [lo, hi] = range2(D);
        const F = fn(f);
        const job = new A.Refinement(
          () => ({ value: `Taylor polynomial of degree ${n} about ${(num(lo).toNumber() + num(hi).toNumber()) / 2}`, trust: "good" }),
          function* () {
            const m = F.model(ivText(lo, hi), { order: Number(n) });
            return { value: m, via: m.notes.join(", ") };
          },
        );
        return [
          {
            label: "model",
            job,
            show: (v, ex) => (ex ? h("div", {}, h("div", { class: "lines" }, v.coefficients.map((c, j) => h("div", {}, `a${j} = ${fmtQ(c, 14)}`))), h("p", {}, "remainder ", mono(fmtIv(v.remainder)))) : v),
          },
        ];
      },
      draw: (c, { f, D }, res) => {
        const [lo, hi] = range2(D).map((s) => num(s).toNumber());
        const F = fn(f);
        const m = res.model?.exact;
        const curves = [curveOf(F)];
        const bands = [];
        if (m) {
          const cen = m.centre.toNumber();
          const cs = m.coefficients.map((q) => q.toNumber());
          const P = (x) => cs.reduceRight((acc, a) => acc * (x - cen) + a, 0);
          const r0 = m.remainder.low.toNumber();
          const r1 = m.remainder.high.toNumber();
          const N = 80;
          for (let i = 0; i < N; i++) {
            const x0 = lo + ((hi - lo) * i) / N;
            const x1 = lo + ((hi - lo) * (i + 1)) / N;
            const ys = [P(x0), P(x1), P((x0 + x1) / 2)];
            bands.push({ x0, x1, y0: Math.min(...ys) + r0, y1: Math.max(...ys) + r1 });
          }
          curves.push({ f: P, color: COLORS.exact, width: 1.5, dash: [5, 4] });
        }
        const pad = (hi - lo) * 0.25;
        plot(c, { x: [lo - pad, hi + pad], curves, bands, vlines: [] });
      },
      note: "Dashed: the polynomial P. Shaded: P plus the remainder interval on the domain. The true function must stay inside the shading on the domain; outside it nothing is promised.",
    }),

  points: (el) =>
    demo(el, {
      title: "Point values to many digits",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(x)", kind: "select", options: ["exp(x)", "log(x)", "sin(x)", "cos(x)", "atan(x)", "sqrt(x)", "tanh(x)", "pi + 0*x", "e + 0*x"] },
        { id: "x", label: "x", value: "1/3" },
        { id: "d", label: "digits", kind: "range", min: 5, max: 200, value: 40 },
      ],
      tasks: ({ f, x, d }) => [{ label: `${f.replace(/\+ 0\*x/, "")} at ${x}`, job: fn(f).value(x, { digits: Number(d) }), show: ivShow }],
    }),

  deriv: (el) =>
    demo(el, {
      title: "Symbolic derivatives",
      inputs: [
        { id: "f", label: "f(x)", value: "x^2*sin(x)" },
        { id: "k", label: "how many", kind: "range", min: 1, max: 4, value: 2 },
        { id: "x", label: "check at x =", value: "1/2" },
      ],
      tasks: ({ f, k, x }) => {
        let F = fn(f);
        const out = [];
        for (let i = 1; i <= Number(k); i++) {
          F = F.derivative();
          const G = F;
          out.push({ label: "f" + "′".repeat(i), job: G.value(x, { digits: 15 }), show: (v, ex) => h("div", {}, mono(G.toString()), h("div", { class: "small" }, ex ? `at ${x}: ${fmtIv(v)}` : `at ${x} ≈ ${fmtF(v)}`)) });
        }
        return out;
      },
      draw: (c, { f, k }) => {
        let F = fn(f);
        const curves = [curveOf(F)];
        const colors = [COLORS.extreme, COLORS.inflection, COLORS.float, COLORS.muted];
        for (let i = 0; i < Number(k); i++) {
          F = F.derivative();
          const G = F;
          curves.push({ f: (x) => G.float(x), color: colors[i], width: 1.5 });
        }
        plot(c, { x: [-4, 4], curves });
      },
    }),

  range: (el) =>
    demo(el, {
      title: "Certified range by adaptive bisection",
      inputs: [
        { id: "f", label: "f(x)", value: "x*cos(x)" },
        { id: "I", label: "interval", value: "0:3" },
        { id: "d", label: "digits", kind: "range", min: 1, max: 10, value: 5 },
      ],
      tasks: ({ f, I, d }) => {
        const [lo, hi] = range2(I);
        return [{ label: "range", job: fn(f).range(ivText(lo, hi), { digits: Number(d) }), show: ivShow }];
      },
      draw: (c, { f, I }, res) => {
        const [lo, hi] = range2(I).map((s) => num(s).toNumber());
        const F = fn(f);
        const r = res.range?.exact;
        const bands = r ? [{ x0: lo, x1: hi, y0: r.low.toNumber(), y1: r.high.toNumber() }] : [];
        plot(c, { x: [lo, hi], curves: [curveOf(F)], bands });
      },
    }),

  integral: (el) =>
    demo(el, {
      title: "Certified integrals",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(-x^2)" },
        { id: "a", label: "from", value: "0" },
        { id: "b", label: "to", value: "1" },
        { id: "d", label: "digits", kind: "range", min: 2, max: 30, value: 15 },
      ],
      tasks: ({ f, a, b, d }) => [{ label: "integral", job: fn(f).integral(a, b, { digits: Number(d) }), show: ivShow }],
    }),

  zeros: (el) =>
    demo(el, {
      title: "Zeros, extrema and inflection points",
      inputs: [
        { id: "f", label: "f(x)", value: "x^3 - 3x + 1" },
        { id: "I", label: "interval", value: "-3:3" },
      ],
      tasks: ({ f, I }) => {
        const iv = range2(I);
        const cols = (extra = []) => [["kind", (r) => r.kind], ["where", place], ...extra];
        return [
          { label: "zeros", job: A.zeros(f, iv), show: (v) => recordTable(v, cols([["mult.", (r) => r.multiplicity ?? (r.atMost ? `≤ ${r.atMost}` : "")], ["unique", (r) => (r.unique ? "yes" : "")]])) },
          { label: "extrema", job: A.extrema(f, iv), show: (v) => recordTable(v, cols([["value", (r) => (r.value ? (typeof r.value === "number" ? fmtF(r.value) : fmtIv(r.value)) : "")]])) },
          { label: "inflections", job: A.inflections(f, iv), show: (v) => recordTable(v, cols()) },
          { label: "poles", job: A.poles(f, iv), show: (v, ex) => (ex ? recordTable(v, cols([["order / limit", (r) => r.order ?? (r.value ? fmtIv(r.value) : "")]])) : h("span", { class: "muted" }, "certified only")) },
        ];
      },
      draw: (c, { f, I }, res) => {
        const [lo, hi] = range2(I).map((s) => num(s).toNumber());
        const F = fn(f);
        const pick = (k) => res[k]?.exact ?? res[k]?.quick;
        const pts = [...markers(F, pick("zeros"), "zeros"), ...markers(F, pick("extrema"), "extrema"), ...markers(F, pick("inflections"), "inflections")];
        const vlines = (res.poles?.exact ?? []).map((p) => ({ x0: p.lo.toNumber(), x1: p.hi.toNumber(), color: COLORS.bad }));
        plot(c, { x: [lo, hi], curves: [curveOf(F)], points: pts, vlines });
      },
      note: "Zeros in the function colour, maxima and minima darker, inflection points lighter. Open circles mark brackets that could not be decided.",
    }),

  flat: (el) =>
    demo(el, {
      title: "A function flat to every order",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(-1/x^2)" },
        { id: "I", label: "interval", value: "-1:1" },
      ],
      tasks: ({ f, I }) => [{ label: "zeros", job: A.zeros(f, range2(I)), show: (v, ex) => (ex ? recordTable(v, [["kind", (r) => r.kind], ["where", place], ["|f| ≤", (r) => (r.bound ? r.bound.toNumber().toExponential(1) : "")]]) : `${v.length} guesses`) }],
    }),

  regions: (el) =>
    demo(el, {
      title: "Regions",
      inputs: [
        { id: "r", label: "region", value: "2n :x:! 2n+1" },
        { id: "xs", label: "test these x", value: "-1, -1/2, 0, 1/2, 1, 3/2, 2" },
        { id: "I", label: "list pieces in", value: "-2:3" },
      ],
      tasks: ({ r, xs, I }) => {
        const region = new A.Region(r);
        const job = new A.Refinement(
          () => ({ value: xs.split(",").map((x) => `${x.trim()}: ${region.test(x.trim()) ? "in" : "out"}`), trust: "good" }),
          function* () {
            const [a, b] = range2(I);
            const iv = region.intervals(a, b);
            const show = (p) => `${p.lo === null ? "−∞" : (p.loStrict ? "(" : "[") + fmtQ(p.lo)}, ${p.hi === null ? "∞" : fmtQ(p.hi) + (p.hiStrict ? ")" : "]")}${p.n !== null ? `   n = ${p.n}` : ""}`;
            return { value: iv.map(show), via: region.integer ? `integer variable ${region.integer}` : "" };
          },
        );
        return [{ label: "membership / pieces", job, show: (v) => h("div", { class: "lines" }, v.map((s) => h("div", {}, s))) }];
      },
    }),

  piecewise: (el) =>
    demo(el, {
      title: "Piecewise functions",
      inputs: [
        { id: "f", label: "f(x)", value: "x^2 if _:x:1; 3 - x if 1:!x:2; 1/2 otherwise" },
        { id: "I", label: "interval", value: "-2:4" },
      ],
      tasks: ({ f, I }) => {
        const F = fn(f);
        const iv = range2(I);
        return [
          { label: "breaks", job: F.breaks(iv), show: (v, ex) => (ex ? recordTable(v, [["at", (r) => fmtQ(r.at)], ["kind", (r) => r.kind], ["value", (r) => (r.value ? fmtIv(r.value) : "undefined")], ["left", (r) => (r.left ? fmtIv(r.left) : "–")], ["right", (r) => (r.right ? fmtIv(r.right) : "–")]]) : h("span", { class: "muted" }, "certified only")) },
          { label: "zeros", job: F.zeros(iv), show: (v) => recordTable(v, [["kind", (r) => r.kind], ["where", place], ["piece", (r) => r.piece ?? ""]]) },
          { label: "∫", job: F.integral(iv[0], iv[1], { digits: 12 }), show: ivShow },
        ];
      },
      draw: (c, { f, I }, res) => {
        const F = fn(f);
        const [lo, hi] = range2(I).map((s) => num(s).toNumber());
        const pts = [];
        for (const b of res.breaks?.exact ?? []) {
          const x = b.at.toNumber();
          for (const side of [b.left, b.right]) if (side) pts.push({ x, y: side.low.toNumber(), kind: "open", color: COLORS.fn });
          if (b.value) pts.push({ x, y: b.value.low.toNumber(), kind: "dot", color: COLORS.fn });
        }
        pts.push(...markers(F, res.zeros?.exact ?? res.zeros?.quick, "zeros"));
        plot(c, { x: [lo, hi], curves: [curveOf(F)], points: pts });
      },
      note: "Filled dots: the value at a break. Open dots: a one-sided limit that is not the value there.",
    }),

  ode: (el) =>
    demo(el, {
      title: "A validated ODE solve",
      inputs: [
        { id: "f", label: "y′ =", value: "y^2 + t" },
        { id: "y0", label: "y(0) =", value: "1/2" },
        { id: "T", label: "until t =", value: "1/2" },
        { id: "n", label: "order", kind: "range", min: 4, max: 14, value: 10 },
      ],
      tasks: ({ f, y0, T, n }) => [
        {
          label: "y(T)",
          job: A.ode.solve({ f, y0, until: T, order: Number(n) }),
          show: (v, ex) => (ex ? h("div", {}, mono(fmtIv(v.final)), h("div", { class: "small muted" }, v.describe())) : `RK4: ${fmtF(v?.y.at(-1))}`),
        },
      ],
      draw: (c, { T }, res) => {
        const q = res["y(T)"]?.quick;
        const sol = res["y(T)"]?.exact;
        const t1 = num(T).toNumber();
        const bands = [];
        if (sol) {
          for (const s of sol.steps) {
            const a = s.t0.toNumber();
            const b = s.t1.toNumber();
            const N = 8;
            const len = s.t1.subtract(s.t0);
            const tAt = (i) => s.t0.add(len.multiply(new A.Rational(BigInt(i), BigInt(N))));
            for (let i = 0; i < N; i++) {
              const x0 = a + ((b - a) * i) / N;
              const x1 = a + ((b - a) * (i + 1)) / N;
              const r = s.models[0].at(new A.RationalInterval(tAt(i), tAt(i + 1)));
              bands.push({ x0, x1, y0: r.low.toNumber(), y1: r.high.toNumber() });
            }
          }
        }
        const interp = (t) => {
          if (!q) return NaN;
          const k = Math.round((t / t1) * (q.t.length - 1));
          return q.y[Math.max(0, Math.min(q.y.length - 1, k))];
        };
        plot(c, { x: [0, t1], curves: [{ f: interp }], bands, samples: 200 });
      },
      note: "Line: RK4 preview. Shaded: certified boxes from the Taylor-model steps (each step's model evaluated on eighths of the step).",
    }),

  series: (el) =>
    demo(el, {
      title: "Your own series with a remainder rule",
      inputs: [
        { id: "a", label: "coefficient a_k =", value: "(-1)^k/(2k+1)" },
        { id: "D", label: "domain (centre 0)", value: "0:1/2" },
        { id: "p", label: "degree kept", kind: "range", min: 2, max: 30, value: 10 },
        { id: "rule", label: "rule", kind: "select", options: ["alternating", "ratio"], value: "alternating" },
        { id: "q", label: "q (ratio rule)", value: "1/2" },
      ],
      tasks: ({ a, D, p, rule, q }) => {
        // substitute the integer k into the formula, so (-1)^k is an integer power
        const coef = (k) => {
          const v = fn(a.replace(/(?<![A-Za-z_])k(?![A-Za-z0-9_])/g, `(${k})`)).value("0").exact();
          if (v.low.compareTo(v.high) !== 0) throw new Error("coefficients must be exact rationals");
          return v.low;
        };
        const [lo, hi] = range2(D);
        const job = new A.Refinement(
          () => ({ value: `${Number(p) + 1} terms, ${rule} rule`, trust: "good" }),
          function* () {
            const m = A.series(ivText(lo, hi), { coefficient: coef, degree: Number(p), order: Number(p), centre: 0, rule, q: num(q) });
            return { value: m, via: m.notes.join(", ") };
          },
        );
        return [{ label: "model", job, show: (v, ex) => (ex ? h("div", {}, "remainder ", mono(fmtIv(v.remainder)), h("div", { class: "small muted" }, v.assumed ? "the tail hypothesis was checked on 32 terms; beyond that it is assumed" : "")) : v) }];
      },
    }),

  explore: (el) => explorer(el),
  ...MORE,
};

// ---- page switching -----------------------------------------------------------

const mounted = new WeakSet();
function mountDemos(page) {
  for (const el of page.querySelectorAll("[data-demo]")) {
    if (mounted.has(el)) continue;
    mounted.add(el);
    const make = DEMOS[el.dataset.demo];
    if (!make) continue;
    try {
      make(el);
    } catch (e) {
      el.append(h("p", { class: "err" }, `demo failed: ${e.message}`));
    }
  }
}

// Old single-page links (index.html#zeros) go to the page's own file.
const OLD = { intro: "index.html", reference: "reference.html", explore: "explore.html", fast: "fast.html", models: "models.html", points: "values.html", expressions: "expressions.html", ranges: "ranges.html", zeros: "zeros.html", piecewise: "piecewise.html", odes: "odes.html", series: "series.html" };
const old = OLD[location.hash.slice(1)];
if (old && !location.pathname.endsWith(old)) location.replace(old);
document.getElementById("toc-select")?.addEventListener("change", (e) => (location.href = e.target.value));
mountDemos(document);
mountRunboxes(document, { scope: A });
