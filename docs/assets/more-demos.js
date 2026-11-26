// Demos for the deeper topic pages: precision ladders, argument reduction,
// interval parameters, the dependency problem, order convergence, systems
// and uncertain starts for ODEs, and user series checked against built-ins.
import { A, h, demo, plot, fmtIv, fmtF, widthOf, mono, COLORS, curveOf } from "./ui.js?v=19e23836be";

const { R, fn } = A;
const num = (s) => (A.Rational.from ? A.Rational.from(String(s).trim()) : new A.Rational(String(s).trim()));
const range2 = (s) => s.split(/[:,]/).map((t) => t.trim());
const ivText = (lo, hi) => R`${lo}:${hi}`;
const sci = (x) => (x === 0 ? "0" : x.toExponential(2));
const widthNum = (iv) => iv.high.subtract(iv.low).toNumber();
const ivShow = (v, exact) => (exact ? h("span", {}, mono(fmtIv(v)), " ", h("span", { class: "muted small" }, widthOf(v))) : mono(Array.isArray(v) ? `[${v.map(fmtF).join(", ")}]` : fmtF(v)));

/** The first `sig` significant digits of a Rational's decimal expansion (truncated). */
function decimal(q, sig) {
  let n = q.numerator;
  const d = q.denominator;
  const neg = n < 0n;
  if (neg) n = -n;
  const ip = n / d;
  const intLen = ip === 0n ? 0 : ip.toString().length;
  const frac = Math.max(0, sig - intLen);
  const scaled = (n * 10n ** BigInt(frac)) / d;
  let str = scaled.toString().padStart(frac + 1, "0");
  str = frac ? `${str.slice(0, str.length - frac)}.${str.slice(str.length - frac)}` : str;
  return (neg ? "-" : "") + str;
}

/** A Refinement whose certified stage is one synchronous computation. */
const once = (preview, compute, via = "") =>
  new A.Refinement(
    () => ({ value: preview, trust: "good" }),
    function* () {
      const t0 = performance.now();
      const value = compute();
      return { value, via: via || `${(performance.now() - t0).toFixed(0)} ms` };
    },
  );

export const MORE = {
  // ---- values ---------------------------------------------------------------
  ladder: (el) =>
    demo(el, {
      title: "The same value at more and more digits",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(x)", kind: "select", options: ["exp(x)", "log(x)", "sin(x)", "atan(x)", "sqrt(x)", "exp(sin(x))"] },
        { id: "x", label: "x", value: "7/3" },
      ],
      tasks: ({ f, x }) =>
        [10, 25, 50, 100, 200].map((d) => ({
          label: `${d} digits`,
          job: fn(f).value(x, { digits: d }),
          show: (v, ex) =>
            ex
              ? h("div", {}, h("div", { class: "mono wrap" }, decimal(v.low, d), "…"), h("div", { class: "muted small" }, `lower end, first ${d} digits; interval width ${sci(widthNum(v))}`))
              : mono(fmtF(v)),
        })),
      note: "Each row is certified separately. The float preview is the same in every row: a double has about 16 digits.",
    }),

  reduction: (el) =>
    demo(el, {
      title: "Argument reduction for exp",
      inputs: [
        { id: "x", label: "x", value: "10" },
        { id: "d", label: "digits", kind: "range", min: 10, max: 120, value: 40 },
      ],
      tasks: ({ x, d }) => {
        const q = num(x);
        const a = Math.abs(q.toNumber());
        const e = a === 0 ? 0 : Math.floor(Math.log2(a));
        const s = Math.max(0, e + 3);
        const r = a / 2 ** s;
        const bits = Math.ceil(Number(d) * Math.log2(10)) + 16;
        const wp = bits + s + 16;
        let t = 1;
        let k = 0;
        while (2 * t > 2 ** -wp) {
          k++;
          t *= r / k;
        }
        const plan = h(
          "div",
          { class: "lines" },
          h("div", {}, `|x| = ${fmtF(a)}, so halve s = ${s} times: r = x/2^${s} = ${fmtF(r)}`),
          h("div", {}, `working precision ${wp} bits (${bits} asked + ${s} for the squarings + 16 guard)`),
          h("div", {}, `Σ rᵏ/k! needs ${k} terms before the tail bound 2·r^k/k! < 2^-${wp}`),
          h("div", {}, `then square ${s} times: e^x = (e^r)^(2^${s})`),
        );
        return [
          { label: "plan", job: once(plan, () => plan), show: (v) => v },
          { label: `exp(${x})`, job: fn("exp(x)").value(x, { digits: Number(d) }), show: ivShow },
        ];
      },
    }),

  // ---- expressions -----------------------------------------------------------
  intervalParam: (el) =>
    demo(el, {
      title: "A parameter that is an interval",
      inputs: [
        { id: "f", label: "f(x)", value: "a*sin(x) + x/4" },
        { id: "a", label: "a in", value: "1/2:3/2" },
        { id: "I", label: "x in", value: "0:3" },
      ],
      tasks: ({ f, a, I }) => {
        const [al, ah] = range2(a);
        const [lo, hi] = range2(I);
        const F = fn(f, { params: { a: ivText(al, ah) } });
        return [
          { label: "range for every a", job: F.range(ivText(lo, hi), { digits: 3, maxPieces: 32 }), show: ivShow },
          { label: `f(1) for every a`, job: F.value("1", { digits: 8, maxBits: 128 }), show: ivShow },
        ];
      },
      draw: (c, { f, a, I }, res) => {
        const [al, ah] = range2(a).map((s) => num(s).toNumber());
        const [lo, hi] = range2(I).map((s) => num(s).toNumber());
        const curves = [al, (al + ah) / 2, ah].map((v, i) => ({ ...curveOf(fn(f, { params: { a: String(v) } })), color: i === 1 ? COLORS.fn : COLORS.muted, width: i === 1 ? 2 : 1.2 }));
        const r = res["range for every a"]?.exact;
        const bands = r ? [{ x0: lo, x1: hi, y0: r.low.toNumber(), y1: r.high.toNumber() }] : [];
        plot(c, { x: [lo, hi], curves, bands });
      },
      note: "Grey: f at the two ends of a's interval. Shaded: the certified range, which holds for every a in the interval at once.",
    }),

  tree: (el) =>
    demo(el, {
      title: "What the parser builds",
      inputs: [{ id: "f", label: "f(x)", value: "2x sin(x)^2 - 1/x" }],
      tasks: ({ f }) => {
        const ast = A.parse(f);
        const lines = [];
        const walk = (n, depth) => {
          const pad = "  ".repeat(depth);
          if (n.type === "num") lines.push(`${pad}num ${n.value}`);
          else if (n.type === "var") lines.push(`${pad}var ${n.name}`);
          else if (n.type === "const") lines.push(`${pad}const ${n.name}`);
          else {
            lines.push(`${pad}${n.type} ${n.op ?? n.name}`);
            for (const c of n.args) walk(c, depth + 1);
          }
        };
        walk(ast, 0);
        const view = h("div", {}, h("pre", { class: "tree" }, lines.join("\n")), h("p", { class: "small" }, "formatted back: ", mono(A.format(ast))));
        return [{ label: "tree", job: once(view, () => view), show: (v) => v }];
      },
      note: "Implicit products (2x, 2 sin x) become explicit * nodes. The same tree drives the float compiler, the Taylor-model compiler and d/dx.",
    }),

  // ---- ranges ----------------------------------------------------------------
  dependency: (el) =>
    demo(el, {
      title: "Three ways to bound a range",
      inputs: [
        { id: "f", label: "f(x)", value: "x*(1 - x)" },
        { id: "I", label: "interval", value: "0:1" },
      ],
      tasks: ({ f, I }) => {
        const [lo, hi] = range2(I);
        const D = ivText(lo, hi);
        const F = fn(f);
        // an order-0 model is a constant plus a remainder: plain interval arithmetic
        const naive = once("computed below", () => F.model(D, { order: 0 }).range());
        return [
          { label: "order-0 model (plain intervals)", job: naive, show: ivShow },
          { label: "order-8 Taylor model, Bernstein bound", job: once("computed below", () => F.model(D, { order: 8 }).range()), show: ivShow },
          { label: "adaptive pieces, 6 digits", job: F.range(D, { digits: 6 }), show: ivShow },
        ];
      },
      draw: (c, { f, I }, res) => {
        const [lo, hi] = range2(I).map((s) => num(s).toNumber());
        const bands = [];
        const cols = [COLORS.bad, COLORS.band, COLORS.exact];
        ["order-0 model (plain intervals)", "order-8 Taylor model, Bernstein bound", "adaptive pieces, 6 digits"].forEach((k, i) => {
          const r = res[k]?.exact;
          if (r) bands.push({ x0: lo + ((hi - lo) * i) / 3, x1: lo + ((hi - lo) * (i + 1)) / 3, y0: r.low.toNumber(), y1: r.high.toNumber(), color: cols[i] });
        });
        plot(c, { x: [lo, hi], curves: [curveOf(fn(f))], bands });
      },
      note: "Left to right: the three bounds as shaded strips. An order-0 model is interval arithmetic about the centre: it forgets that every x in the formula is the same number, so x·(1 − x) on [0, 1] comes out far wider than its true range [0, 1/4]. One order-8 model already gets it exactly.",
    }),

  pieces: (el) =>
    demo(el, {
      title: "More digits, more pieces",
      inputs: [
        { id: "f", label: "f(x)", value: "sin(x)/(1 + x^2)" },
        { id: "a", label: "from", value: "0" },
        { id: "b", label: "to", value: "4" },
      ],
      tasks: ({ f, a, b }) =>
        [4, 8, 16, 32].map((d) => ({
          label: `${d} digits`,
          job: fn(f).integral(a, b, { digits: d }),
          show: (v, ex) => (ex ? h("span", {}, mono(fmtIv(v)), " ", h("span", { class: "muted small" }, widthOf(v))) : mono(fmtF(v))),
        })),
      note: "The line under each certified answer says how many pieces it took. Order-12 models gain roughly 12 digits each time the pieces halve in width, so the count grows slowly.",
    }),

  // ---- Taylor models -----------------------------------------------------------
  orders: (el) =>
    demo(el, {
      title: "Remainder width against order",
      inputs: [
        { id: "f", label: "f(x)", value: "exp(sin(x))" },
        { id: "D", label: "domain", value: "0:1" },
      ],
      tasks: ({ f, D }) => {
        const [lo, hi] = range2(D);
        const F = fn(f);
        return [2, 4, 6, 8, 12, 16, 20].map((n) => ({
          label: `order ${n}`,
          job: once("certified only", () => F.model(ivText(lo, hi), { order: n }).remainder),
          show: (v, ex) => (ex ? h("span", {}, mono(sci(widthNum(v))), " ", h("span", { class: "muted small" }, "remainder width")) : v),
        }));
      },
      note: "For an analytic f the width falls roughly like (h/2)^(n+1)/(n+1)!·max|f^(n+1)|, where h is the domain width: each extra order buys a fixed number of digits once n passes the scale of f's derivatives.",
    }),

  // ---- ODEs --------------------------------------------------------------------
  oscillator: (el) =>
    demo(el, {
      title: "A rotating flow and the wrapping effect",
      inputs: [
        { id: "x0", label: "x(0) in", value: "199/200:201/200" },
        { id: "T", label: "until t =", value: "3" },
        { id: "n", label: "order", kind: "range", min: 6, max: 14, value: 10 },
      ],
      tasks: ({ x0, T, n }) => {
        const [a, b] = range2(x0);
        return [
          {
            label: "(x, v) at T",
            job: A.ode.solve({ f: ["v", "-x"], vars: ["x", "v"], y0: [ivText(a, b), "0"], until: T, order: Number(n) }),
            show: (v, ex) => {
              if (!ex) return `RK4 from the midpoint: x ≈ ${fmtF(v?.y?.[0]?.at(-1))}, v ≈ ${fmtF(v?.y?.[1]?.at(-1))}`;
              const w0 = num(b).subtract(num(a)).toNumber();
              const [X, V] = v.final;
              return h(
                "div",
                {},
                h("div", {}, "x ∈ ", mono(fmtIv(X))),
                h("div", {}, "v ∈ ", mono(fmtIv(V))),
                h("div", { class: "small muted" }, `start box ${sci(w0)} wide; final box ${sci(widthNum(X))} × ${sci(widthNum(V))}. The true set of solutions is a segment of length ${sci(w0)} turned by T radians.`),
              );
            },
          },
        ];
      },
      draw: (c, _vals, res) => {
        const sol = res["(x, v) at T"]?.exact;
        const bands = [];
        if (sol) {
          for (const s of sol.steps) {
            const [X, V] = sol.at(s.t1);
            bands.push({ x0: X.low.toNumber(), x1: X.high.toNumber(), y0: V.low.toNumber(), y1: V.high.toNumber(), color: COLORS.exact });
          }
        }
        const up = (x) => (Math.abs(x) <= 1 ? Math.sqrt(1 - x * x) : NaN);
        plot(c, { x: [-1.5, 1.5], y: [-1.5, 1.5], curves: [{ f: up, color: COLORS.muted, width: 1 }, { f: (x) => -up(x), color: COLORS.muted, width: 1 }], bands });
      },
      note: "x′ = v, v′ = −x turns the phase plane at unit speed. Boxes: the enclosure of (x, v) at the end of each step, horizontal axis x, vertical axis v. The true set is a short segment that only rotates; the boxes around it grow.",
    }),

  uncertainStart: (el) =>
    demo(el, {
      title: "An uncertain starting value",
      inputs: [
        { id: "f", label: "y′ =", value: "y" },
        { id: "y0", label: "y(0) in", value: "1:101/100" },
        { id: "T", label: "until t =", value: "2" },
      ],
      tasks: ({ f, y0, T }) => {
        const [a, b] = range2(y0);
        return [
          {
            label: "y(T)",
            job: A.ode.solve({ f, y0: ivText(a, b), until: T }),
            show: (v, ex) => {
              if (!ex) return "RK4 runs from the midpoint only";
              const w0 = num(b).subtract(num(a)).toNumber();
              const w = widthNum(v.final);
              return h("div", {}, mono(fmtIv(v.final)), h("div", { class: "small muted" }, `width ${sci(w0)} at t = 0 became ${sci(w)}: a factor of ${fmtF(Number((w / w0).toPrecision(6)))}`));
            },
          },
        ];
      },
      note: "For y′ = y every starting value is multiplied by e^T, so the true set of solutions grows by exactly e^T (7.389… for T = 2). The enclosure is valid but grows faster: each step bounds the effect of its starting interval without remembering that the start is a single number in that interval.",
    }),

  // ---- user series -------------------------------------------------------------
  seriesCheck: (el) =>
    demo(el, {
      title: "A user series against the built-in function",
      inputs: [
        { id: "which", label: "series", kind: "select", options: ["log(1+x): (-1)^(k+1)/k", "atan(x): odd terms (-1)^j/(2j+1)", "exp(x): 1/k!"], value: "log(1+x): (-1)^(k+1)/k" },
        { id: "x", label: "evaluate at", value: "1/4" },
        { id: "p", label: "degree kept", kind: "range", min: 4, max: 40, value: 16 },
      ],
      tasks: ({ which, x, p }) => {
        const fact = (k) => {
          let f = 1n;
          for (let i = 2n; i <= BigInt(k); i++) f *= i;
          return f;
        };
        const spec =
          which[0] === "l"
            ? { coefficient: (k) => (k === 0 ? new A.Rational(0n) : new A.Rational(k % 2 ? 1n : -1n, BigInt(k))), rule: "alternating", f: "log(1 + x)" }
            : which[0] === "a"
              ? { coefficient: (k) => (k % 2 === 0 ? new A.Rational(0n) : new A.Rational(((k - 1) / 2) % 2 ? -1n : 1n, BigInt(k))), rule: "alternating", f: "atan(x)" }
              : { coefficient: (k) => new A.Rational(1n, fact(k)), rule: "lagrange", M: 2, f: "exp(x)" };
        const D = R`0:1/2`;
        const userJob = once("certified only", () => {
          const m = A.series(D, { coefficient: spec.coefficient, degree: Number(p), order: Number(p), centre: 0, rule: spec.rule, M: spec.M });
          return { at: m.at(num(x)), assumed: m.assumed, notes: m.notes };
        });
        return [
          {
            label: "user series",
            job: userJob,
            show: (v, ex) => (ex ? h("div", {}, mono(fmtIv(v.at)), " ", h("span", { class: "muted small" }, widthOf(v.at)), h("div", { class: "small muted" }, `${spec.rule} rule${v.assumed ? ", partly assumed" : ""}`)) : v),
          },
          { label: `built-in ${spec.f}`, job: fn(spec.f).value(x, { digits: 30 }), show: ivShow },
        ];
      },
      note: "Domain [0, 1/2], centre 0 (for negative x the log series does not alternate, and the rule is refused). The two enclosures must overlap; the user series is only as tight as its degree and rule allow.",
    }),
};
