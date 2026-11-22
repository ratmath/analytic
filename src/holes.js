// Removable singularities of rational parts. In (x^2 - 1)/(x - 1) + sin(2x)/2
// the summands that are rational functions of x are combined into N/D and the
// common factor G = gcd(N, D) is cancelled. The reduced tree agrees with the
// original wherever the original is defined, and is also defined at the zeros
// of G, the holes. Zeros, extrema, integrals and ranges are then computed on
// the reduced tree, which has no singularity to bisect into.
import { Rational } from "@ratmath/core";
import { S, num, v, op } from "./expr.js";
import * as RP from "./rpoly.js";
import { isZero } from "./rat.js";

/** Top-level summands of a tree, each with a sign. */
function summands(ast, sgn = 1, out = []) {
  if (ast.type === "op" && ast.op === "+") {
    summands(ast.args[0], sgn, out);
    summands(ast.args[1], sgn, out);
  } else if (ast.type === "op" && ast.op === "-") {
    summands(ast.args[0], sgn, out);
    summands(ast.args[1], -sgn, out);
  } else if (ast.type === "op" && ast.op === "neg") {
    summands(ast.args[0], -sgn, out);
  } else out.push({ ast, sgn });
  return out;
}

/** A polynomial (array of Rationals) as a tree in `variable`, by Horner's rule. */
export function polyAst(p, variable) {
  const x = v(variable);
  let t = num(p[p.length - 1]);
  for (let i = p.length - 2; i >= 0; i--) t = S.add(S.mul(t, x), isZero(p[i]) ? num(0) : num(p[i]));
  return t;
}

/**
 * { ast, G } with the rational summands combined and reduced, or null when
 * nothing cancels (G constant) or the tree has no rational summands.
 * `params` must map names to Rationals.
 */
export function cancelHoles(ast, variable, params = {}) {
  const terms = summands(ast);
  let N = null;
  let D = null;
  const rest = [];
  let count = 0;
  for (const t of terms) {
    const rf = RP.rationalFunction(t.ast, variable, params);
    if (!rf || RP.deg(rf.den) < 0) {
      rest.push(t);
      continue;
    }
    count++;
    const n = t.sgn < 0 ? RP.scale(rf.num, new Rational(-1n)) : rf.num;
    if (!N) [N, D] = [n, rf.den];
    else [N, D] = [RP.add(RP.mul(N, rf.den), RP.mul(n, D)), RP.mul(D, rf.den)];
  }
  if (!count || RP.isZeroPoly(D)) return null;
  const G = RP.gcd(N, D);
  if (RP.deg(G) < 1) return null;
  let Nr = RP.divmod(N, G).quo;
  let Dr = RP.divmod(D, G).quo;
  // make the reduced denominator monic so constants stay readable
  const lead = Dr[Dr.length - 1];
  Nr = RP.scale(Nr, lead.reciprocal());
  Dr = RP.scale(Dr, lead.reciprocal());
  let tree = RP.deg(Dr) === 0 ? polyAst(Nr, variable) : op("/", polyAst(Nr, variable), polyAst(Dr, variable));
  for (const t of rest) tree = t.sgn < 0 ? S.sub(tree, t.ast) : S.add(tree, t.ast);
  return { ast: tree, G };
}
