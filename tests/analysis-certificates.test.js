// Course Test roadmap, Fable items B2 to B5 (ratmath/shelf course-test/ROADMAP.md):
// certified limits of power forms, N for ε, δ for ε, suprema, limsup/liminf,
// uniform convergence. Each result is checked against a value known by hand.
import { describe, expect, test, setDefaultTimeout } from "bun:test";
import { Rational } from "@ratmath/core";
import * as A from "../index.js";

// certified searches: seconds each here, more on a slow machine
setDefaultTimeout(120000);

const Q = (n, d = 1) => new Rational(BigInt(n), BigInt(d));
const mid = (iv) => (typeof iv === "number" ? iv : iv.low.add(iv.high).divide(Q(2)).toNumber());
const width = (iv) => iv.high.subtract(iv.low).toNumber();

describe("B2: limits of f(n)^g(n)", () => {
  const cases = [
    ["(1 + 1/n)^n", Math.E],
    ["(n/(n + 1))^n", 1 / Math.E],
    ["(1 - 1/n^2)^n", 1],
    ["((n + 1)/(n - 1))^n", Math.E ** 2],
    ["(1 + 3/n + 1/n^2)^n", Math.E ** 3],
    ["(1 + 1/n^2)^(n^2 + n)", Math.E],
    ["n^n/(n + 1)^(n + 1)*(n + 1)", 1 / Math.E],
    ["((n + 1)/(2n))^n", 0],
    ["n!/n^n", 0],
  ];
  for (const [text, want] of cases) {
    test(`${text} → ${want}`, () => {
      const L = A.sequence(text).limit({ digits: 12 });
      expect(mid(L)).toBeCloseTo(want, 9);
      expect(width(L)).toBeLessThan(1e-9);
    });
  }
  test("powers that outgrow every bound are proven to tend to infinity through their reciprocal", () => {
    expect(A.sequence("(1 + 1/n)^(n^2)").limit()).toBe(Infinity);
    expect(A.sequence("((2n + 1)/(n + 3))^n").limit()).toBe(Infinity);
    expect(A.sequence("n^n/n!").limit()).toBe(Infinity);
    expect(A.sequence("-(1 + 1/n)^(n^2)").limit()).toBe(-Infinity);
  });
  test("the limit encloses the terms far out (an independent check)", () => {
    const L = A.sequence("(n/(n + 1))^n").limit({ digits: 12 });
    const far = (1e7 / (1e7 + 1)) ** 1e7;
    expect(Math.abs(mid(L) - far)).toBeLessThan(1e-7);
  });
  test("the ratio test on Σ n!/nⁿ finds the limit 1/e", () => {
    const r = A.sum("n!/n^n").ratioTest();
    expect(r.verdict).toBe("convergent");
    expect(mid(r.limit)).toBeCloseTo(1 / Math.E, 12);
    const r2 = A.sum("n^n/n!").ratioTest();
    expect(r2.verdict).toBe("divergent");
    expect(mid(r2.limit)).toBeCloseTo(Math.E, 12);
  });
  test("(1 + 1/n)^n is proven increasing, (1 + 1/n)^(n + 1) decreasing", () => {
    const up = A.sequence("(1 + 1/n)^n").monotone();
    expect(up.direction).toBe("increasing");
    expect(up.from).toBe(1);
    expect(up.reason).toMatch(/tends to 0/);
    expect(A.sequence("(1 + 1/n)^(n + 1)").monotone().direction).toBe("decreasing");
    expect(A.sequence("(1 + 1/n)^(n + 1/2)").monotone().direction).toBe("decreasing");
    expect(A.sequence("(1 - 1/n)^n", { from: 2 }).monotone().direction).toBe("increasing");
    // the first terms agree with the proof
    const t = A.sequence("(1 + 1/n)^n").terms(6).map((x) => (x instanceof Rational ? x.toNumber() : mid(x)));
    for (let i = 1; i < t.length; i++) expect(t[i]).toBeGreaterThan(t[i - 1]);
  }, 120000);
});

describe("B3: an N for ε", () => {
  test("1/√n < 1/100 from N = 10001, the least", () => {
    const r = A.sequence("1/sqrt(n)").nFor("1/100");
    expect(r.N).toBe(10001);
    expect(r.least).toBe(true);
    expect(r.method).toBe("monotone tail");
    expect(A.verifyCertificate(r.certificate).valid).toBe(true);
  });
  test("(3n² + 1)/(2n² − n) → 3/2: N by hand", () => {
    // a(n) − 3/2 = (3n + 2)/(2(2n² − n)) < 1/1000 first at n = 752
    const r = A.sequence("(3n^2 + 1)/(2n^2 - n)").nFor("1/1000");
    const d = (n) => (3 * n + 2) / (2 * (2 * n * n - n));
    expect(d(r.N)).toBeLessThan(1e-3);
    expect(d(r.N - 1)).toBeGreaterThanOrEqual(1e-3);
    expect(r.N).toBe(752);
  });
  test("an alternating sequence is handled along n = 2m and n = 2m + 1", () => {
    const r = A.sequence("(-1)^n/n").nFor("1/100");
    expect(r.N).toBe(101); // 1/100 itself is not below 1/100
    expect(r.least).toBe(true);
    expect(A.verifyCertificate(r.certificate).valid).toBe(true);
  });
  test("sin(n)/n has no monotone tail: a dominating sequence 1/n, then the terms one by one", () => {
    const r = A.sequence("sin(n)/n").nFor("1/100");
    expect(r.method).toBe("dominating sequence");
    expect(r.least).toBe(true);
    // brute force: the last n with |sin n|/n ≥ 1/100
    let last = 0;
    for (let n = 1; n <= 200; n++) if (Math.abs(Math.sin(n)) / n >= 0.01) last = n;
    expect(r.N).toBe(last + 1);
    expect(A.verifyCertificate(r.certificate).valid).toBe(true);
  });
  test("an irrational limit: (1 + 1/n)^n within 1/100 of e", () => {
    const r = A.sequence("(1 + 1/n)^n").nFor("1/100");
    const d = (n) => Math.E - (1 + 1 / n) ** n;
    expect(d(r.N)).toBeLessThan(0.01);
    expect(d(r.N - 1)).toBeGreaterThanOrEqual(0.01);
    expect(A.verifyCertificate(r.certificate).valid).toBe(true);
  }, 120000);
  test("a certificate whose N is moved before a bump in the terms fails", () => {
    // 1/(1 + (n − 50)²) → 0: the terms at 49, 50, 51 are 1/2, 1, 1/2, so the least N for ε = 1/2 is 52
    const c = A.sequence("1/(1+(n-50)^2)").nFor("1/2").certificate;
    expect(c.N).toBe(52);
    expect(A.verifyCertificate(c).valid).toBe(true);
    expect(A.verifyCertificate({ ...c, N: 1 }).valid).toBe(false);
    expect(A.verifyCertificate({ ...c, N: 50 }).valid).toBe(false);
    // a part that is not a subsequence of the sequence, or a missing residue class, fails
    expect(A.verifyCertificate({ ...c, parts: [{ ...c.parts[0], term: "1/n" }] }).valid).toBe(false);
    const alt = A.sequence("(-1)^n/n").nFor("1/100").certificate;
    expect(A.verifyCertificate({ ...alt, parts: alt.parts.slice(0, 1) }).valid).toBe(false);
  });
  test("a wrong limit, an unbounded sequence and a bad ε are refused; a tampered certificate fails", () => {
    expect(() => A.sequence("1/n").nFor("1/10", { limit: "1" })).toThrow(/not the limit/);
    expect(() => A.sequence("n^2").nFor("1/10")).toThrow(/unbounded/);
    expect(() => A.sequence("1/n").nFor("0")).toThrow(/positive/);
    const r = A.sequence("1/n").nFor("1/10");
    expect(r.N).toBe(11);
    expect(A.verifyCertificate({ ...r.certificate, N: 9 }).valid).toBe(false);
    expect(A.verifyCertificate({ ...r.certificate, N: 20 }).valid).toBe(false); // 20 works but is not least
  });
});

describe("B3: a δ for ε", () => {
  test("x² at 2 with ε = 1/100: δ = 0.002 works, and the worst case is 2001/250000", () => {
    const r = A.deltaFor("x^2", 2, "1/100", { delta: "0.002" });
    expect(r.holds).toBe(true);
    expect(r.worst.equals(Q(2001, 250000))).toBe(true);
    expect(A.verifyCertificate(r.certificate).valid).toBe(true);
    expect(A.deltaFor("x^2", 2, "1/100", { delta: "0.0025" }).holds).toBe(false);
  });
  test("the largest δ for x² at 2 is √4.01 − 2", () => {
    const r = A.deltaFor("x^2", 2, "1/100");
    const want = Math.sqrt(4.01) - 2;
    expect(Math.abs(mid(r.largest) - want)).toBeLessThan(1e-14);
    // exactly: (2 + δ)² = 4.01 lies between the squares of the ends
    expect(Q(2).add(r.largest.low).pow(2).compareTo(Q(401, 100)) <= 0).toBe(true);
    expect(Q(2).add(r.largest.high).pow(2).compareTo(Q(401, 100)) >= 0).toBe(true);
    expect(r.largest.high.subtract(r.largest.low).toNumber()).toBeLessThan(1e-15);
    expect(r.delta.equals(Q(249, 100000))).toBe(true);
    expect(A.verifyCertificate(r.certificate).valid).toBe(true);
  });
  test("exact largest δ where the equation has a rational solution", () => {
    expect(A.deltaFor("2x + 1", 1, "1/100").largest.equals(Q(1, 200))).toBe(true);
    expect(A.deltaFor("1/x", 1, "1/10").largest.equals(Q(1, 11))).toBe(true); // 1/x = 11/10 at x = 10/11
    const s = A.deltaFor("sqrt(x)", 4, "1/10"); // 1.9² = 3.61 is nearer to 4 than 2.1² = 4.41
    expect(s.largest.equals(Q(39, 100))).toBe(true);
    expect(A.verifyCertificate(s.certificate).valid).toBe(true);
    expect(A.verifyCertificate(A.deltaFor("2x + 1", 1, "1/100").certificate).valid).toBe(true);
  });
  test("a corner: |x| at 0", () => {
    const r = A.fn("abs(x)").deltaFor(0, "1/10");
    expect(r.largest.equals(Q(1, 10))).toBe(true);
  });
  test("a δ that is too large fails the checker", () => {
    const r = A.deltaFor("x^2", 2, "1/100");
    expect(A.verifyCertificate({ ...r.certificate, delta: Q(3, 1000) }).valid).toBe(false);
  });
});

describe("B3: suprema and infima", () => {
  test("1 − 1/n: sup 1 not attained, inf 0 attained at n = 1", () => {
    const a = A.sequence("1 - 1/n");
    const [s, i] = [a.supremum(), a.infimum()];
    expect(s.value.equals(Q(1))).toBe(true);
    expect(s.attained).toBe(false);
    expect(i.value.equals(Q(0))).toBe(true);
    expect(i.attained).toBe(true);
    expect(i.at).toBe(1);
  });
  test("n/2ⁿ peaks at 1/2 (n = 1 and 2); n² is unbounded above", () => {
    const s = A.sequence("n/2^n").supremum();
    expect(s.value.equals(Q(1, 2))).toBe(true);
    expect(s.attained).toBe(true);
    expect(A.sequence("n/2^n").infimum().attained).toBe(false);
    expect(A.sequence("n^2").supremum().value).toBe(Infinity);
  });
  test("(−1)ⁿ(1 + 1/n): sup 3/2 at n = 2, inf −2 at n = 1", () => {
    const a = A.sequence("(-1)^n*(1 + 1/n)");
    expect(a.supremum().value.equals(Q(3, 2))).toBe(true);
    expect(a.supremum().at).toBe(2);
    expect(a.infimum().value.equals(Q(-2))).toBe(true);
    expect(a.infimum().at).toBe(1);
  });
  test("(1 + 1/n)ⁿ: sup e, not attained", () => {
    const s = A.sequence("(1 + 1/n)^n").supremum();
    expect(s.attained).toBe(false);
    expect(mid(s.value)).toBeCloseTo(Math.E, 12);
  });
});

describe("B4: lim sup and lim inf", () => {
  test("(−1)ⁿ(1 + 1/n): lim sup 1, lim inf −1, and limit() says it oscillates", () => {
    const a = A.sequence("(-1)^n*(1 + 1/n)");
    expect(a.limsup().low.equals(Q(1))).toBe(true);
    expect(a.liminf().high.equals(Q(-1))).toBe(true);
    expect(() => a.limit()).toThrow(/oscillate.*lim sup 1.*lim inf -1/);
  });
  test("period 4 and period 3", () => {
    const acc = A.sequence("cos(pi*n/2) + 1/n").accumulation();
    expect(acc.period).toBe(4);
    expect(acc.limsup.low.equals(Q(1))).toBe(true);
    expect(acc.liminf.high.equals(Q(-1))).toBe(true);
    expect(acc.converges).toBe(false);
    const b = A.sequence("sin(2*pi*n/3)*(n + 1)/n");
    expect(mid(b.limsup())).toBeCloseTo(Math.sqrt(3) / 2, 12);
    expect(mid(b.liminf())).toBeCloseTo(-Math.sqrt(3) / 2, 12);
  });
  test("subsequences with one limit give a limit", () => {
    const L = A.sequence("(-1)^n/n").limit();
    expect(L.low.equals(Q(0)) && L.high.equals(Q(0))).toBe(true);
    expect(A.sequence("(-1)^n/n").accumulation().converges).toBe(true);
  });
  test("sin(n) is refused in plain words", () => {
    expect(() => A.sequence("sin(n)").limit()).toThrow(/does not repeat on the whole numbers/);
  });
});

describe("B5: uniform convergence decided", () => {
  const U = (s, I, lim) => A.functionSequence(s).uniform(I, lim);
  test("xⁿ: uniform on [0, 1/2], not on [0, 1]", () => {
    const u = U("x^n", ["0", "1/2"]);
    expect(u.verdict).toBe("uniform");
    expect(u.method).toBe("monotone in x");
    const v = U("x^n", ["0", "1"]);
    expect(v.verdict).toBe("not uniform");
    expect(v.witness.x).toBe("1");
  });
  test("witnesses x = 1/n: nx/(1 + n²x²), nx·e^(−nx), n²x(1 − x)ⁿ", () => {
    for (const s of ["n*x/(1+n^2*x^2)", "n*x*exp(-n*x)", "n^2*x*(1-x)^n"]) {
      const r = U(s, ["0", "1"]);
      expect(r.verdict).toBe("not uniform");
      expect(r.method).toBe("witness");
    }
    // the sup of nx/(1 + n²x²) is 1/2 at x = 1/n for every n: the witness limit is that value
    expect(U("n*x/(1+n^2*x^2)", ["0", "1"]).witness.limit.low.equals(Q(1, 2))).toBe(true);
  });
  test("uniform away from the trouble, and by a bound for every x at once", () => {
    expect(U("n*x/(1+n^2*x^2)", ["1", "2"]).verdict).toBe("uniform");
    expect(U("sin(n*x)/n", ["0", "7"]).verdict).toBe("uniform");
    expect(U("x^n/n", ["0", "1"]).verdict).toBe("uniform");
    expect(U("x^2 + 1/n", ["-3", "3"], "x^2").verdict).toBe("uniform");
  });
  test("a wrong limit function is not uniform; a pole inside is not called monotone", () => {
    expect(U("x^n", ["0", "1/2"], "1").verdict).toBe("not uniform");
    const r = U("-1/(n*(x - 1/2))", ["0", "1"]);
    expect(r.verdict).not.toBe("uniform");
  });
  test("the decision agrees with the enclosed suprema in the table", () => {
    const u = U("x^n", ["0", "1/2"]);
    // sup |xⁿ| on [0, 1/2] is 2^(−n)
    for (const row of u.table) expect(row.sup.high.toNumber()).toBeGreaterThanOrEqual(0.5 ** row.n - 1e-12);
  });
});
