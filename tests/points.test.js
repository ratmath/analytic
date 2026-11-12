import { describe, test, expect } from "bun:test";
import { R } from "@ratmath/core";
import { createScope, constants, enclose } from "../index.js";
import { expectEncloses, dec } from "./helpers.js";

const s = createScope({ digits: 30 });

describe("certified point values (30-digit references from mpmath)", () => {
  const cases = [
    ["exp", R`1/3`, "1.395612425086089528628125319602586837598"],
    ["exp", R`-50`, "1.928749847963917783017342816527012574753e-22", "1e-50"],
    ["sin", R`7/5`, "0.9854497299884601806594745788060975173563"],
    ["cos", R`7/5`, "0.1699671429002409386167480352036498029282"],
    ["sin", R`1000000`, "-0.3499935021712929521176524867807714690614"],
    ["log", R`7/3`, "0.8472978603872036137101075065206540249896"],
    ["log", R`1/1000`, "-6.907755278982137052053974364053092622803"],
    ["atan", R`-5/2`, "-1.190289949682531732927733774829318337601"],
    ["atan", R`3/4`, "0.6435011087932843868028092287173226380415"],
    ["sqrt", R`1/3`, "0.5773502691896257645091487805019574556476"],
    ["tan", R`1`, "1.557407724654902230506974807458360173087"],
    ["tanh", R`1/2`, "0.4621171572600097585023184836436725487303"],
    ["cosh", R`2`, "3.762195691083631459562213477773746108294"],
    ["sinh", R`-1/3`, "-0.3395405572561501391012606113386035850724"],
  ];
  for (const [name, x, ref, w] of cases) {
    test(`${name}(${x})`, () => expectEncloses(s[name](x), ref, w ?? "1e-29"));
  }
  test("pi and e", () => {
    expectEncloses(s.pi, "3.141592653589793238462643383279502884197", "1e-29");
    expectEncloses(s.e, "2.718281828459045235360287471352662497757", "1e-29");
    expectEncloses(constants.pi(200), "3.141592653589793238462643383279502884197", "1e-55");
  });
  test("exact special values", () => {
    expect(s.exp(R`0`).toString()).toBe("1:1");
    expect(s.log(R`1`).low.toString()).toBe("0");
    expect(s.sqrt(R`9/4`).low.toString()).toBe("3/2");
  });
  test("domain refusals", () => {
    expect(() => s.log(R`0`)).toThrow(/positive/);
    expect(() => s.sqrt(R`-1`)).toThrow(/non-negative/);
    expect(() => s.log(R`-1:2`)).toThrow(/positive/);
  });
});

describe("interval arguments", () => {
  test("monotone functions use endpoints", () => {
    const r = s.exp(R`0:1`);
    expectEncloses({ lo: r.low, hi: r.low }, "1", "1");
    expectEncloses({ lo: r.high, hi: r.high }, "2.718281828459045235360287471352662497757", "1");
  });
  test("sin(-1:1) is ±sin(1), not the term-by-term ±1.18", () => {
    const r = s.sin(R`-1:1`);
    const sin1 = dec("0.8414709848078965066525023216302989996226");
    expect(r.high.compareTo(sin1) >= 0).toBe(true);
    expect(r.high.subtract(sin1).toNumber()).toBeLessThan(1e-12);
    expect(r.low.toNumber()).toBeGreaterThan(-0.8414709849);
  });
  test("sin over a wide interval is clamped to [-1, 1]", () => {
    const r = enclose.sin(R`0:100`);
    expect(r.low.toString()).toBe("-1");
    expect(r.high.toString()).toBe("1");
  });
  test("cos over [3, 4] contains the minimum -1", () => {
    const r = s.cos(R`3:4`);
    expect(r.low.toNumber()).toBeLessThanOrEqual(-1);
    expect(r.low.toNumber()).toBeGreaterThan(-1.0000001);
  });
});
