// Type declarations for @ratmath/analytic.
import type { Rational, RationalInterval } from "@ratmath/core";

/** Anything read as an exact rational: a Core Rational, a bigint, an integer number or a string such as "3/4" or "0.#3". */
export type RationalLike = Rational | bigint | number | string;
/** An interval given as [lo, hi], a Core RationalInterval or a Domain. */
export type IntervalLike = [RationalLike, RationalLike] | RationalInterval | DomainClass;
/** An expression: source text or a parsed tree. */
export type ExpressionLike = string | Ast;
/** Named parameter values, exact. */
export type Params = Record<string, RationalLike>;

/** A parsed expression tree. */
export type Ast =
  | { type: "num"; value: Rational }
  | { type: "var"; name: string }
  | { type: "op"; op: "+" | "-" | "*" | "/" | "^" | "neg"; args: Ast[] }
  | { type: "call"; name: string; args: Ast[] };

export type Trust = "good" | "rough" | "unsure" | string;
export interface Stage<T> {
  value: T;
  /** How far the value can be relied on. */
  trust?: Trust;
  /** "float" for the quick stage; later stages name themselves. */
  stage?: string;
  /** True when the value is certified. */
  exact?: boolean;
  [extra: string]: unknown;
}

/**
 * A computation with a fast answer and a certified one.
 * `quick` is immediate (floating point), `exact()` runs the certified stages to the end,
 * and iterating yields each stage as it sharpens.
 */
export class Refinement<Q = unknown, E = Q> implements Iterable<Stage<E>> {
  constructor(quick: () => Stage<Q> | Q, exact: () => Iterator<Stage<E>> | Stage<E> | E);
  readonly quick: Stage<Q>;
  readonly settled: boolean;
  exactStage(): Stage<E>;
  exact(): E;
  [Symbol.iterator](): Iterator<Stage<E>>;
}

/**
 * Run a Refinement without blocking: `onStage` gets the quick stage at once and then each
 * certified stage in short slices. Returns a function that cancels the run.
 */
export function live<Q, E>(
  compute: () => Refinement<Q, E>,
  onStage: (stage: Stage<Q | E>, info: { exact: boolean }) => void,
  options?: { idleMs?: number; sliceMs?: number; onProgress?: (info: unknown) => void; onError?: (error: unknown) => void },
): () => void;

export class AnalyticError extends Error {
  constructor(code: string, message: string, details?: Record<string, unknown>);
  /** A stable identifier such as "pole", "not-smooth", "no-enclosure", "syntax". */
  code: string;
  details: Record<string, unknown>;
}

// ---- Taylor models

export const DEFAULTS: { order: number; bits: number };

export class DomainClass {
  constructor(lo: Rational, hi: Rational, centre?: Rational);
  lo: Rational;
  hi: Rational;
  /** The expansion point (also available as `t`). */
  centre: Rational;
  t: Rational;
  readonly interval: RationalInterval;
  readonly width: Rational;
  readonly radius: Rational;
  contains(x: RationalLike): boolean;
  equals(other: DomainClass): boolean;
  toString(): string;
  toJSON(): { lo: string; hi: string; centre: string };
}
export function Domain(lo: RationalLike, hi: RationalLike, options?: { centre?: RationalLike }): DomainClass;
export function Domain(interval: IntervalLike, options?: { centre?: RationalLike }): DomainClass;

export interface ModelOptions {
  /** Degree of the polynomial part. */
  order?: number;
  /** Working precision in bits for rounding coefficients (the rounding error goes into the remainder). */
  bits?: number;
}

/** A polynomial in (x − centre) with exact coefficients plus an interval that holds the error on the whole domain. */
export class TaylorModel {
  static x(domain: IntervalLike, options?: ModelOptions): TaylorModel;
  static constant(domain: IntervalLike, value: RationalLike | RationalInterval, options?: ModelOptions): TaylorModel;
  static polynomial(domain: IntervalLike, coefficients: RationalLike[], options?: ModelOptions): TaylorModel;
  domain: DomainClass;
  order: number;
  bits: number;
  /** True when the model rests on a hypothesis the library could not check (see `series`). */
  assumed: boolean;
  notes: string[];
  readonly centre: Rational;
  /** Coefficients in powers of (x − centre), constant first. */
  readonly coefficients: Rational[];
  /** Coefficients in powers of x. */
  readonly coefficientsInX: Rational[];
  readonly remainder: RationalInterval;
  readonly isExact: boolean;
  readonly degree: number;
  polyBound(depth?: number): RationalInterval;
  bound(depth?: number): RationalInterval;
  /** An enclosure of the function at a point or over a sub-interval. */
  at(x: RationalLike | RationalInterval, options?: { depth?: number }): RationalInterval;
  range(options?: { depth?: number }): RationalInterval;
  add(other: TaylorModel | RationalLike): TaylorModel;
  subtract(other: TaylorModel | RationalLike): TaylorModel;
  negate(): TaylorModel;
  multiply(other: TaylorModel | RationalLike): TaylorModel;
  divide(other: TaylorModel | RationalLike): TaylorModel;
  pow(n: number): TaylorModel;
  /** The antiderivative that vanishes at the left end of the domain. */
  integrate(): TaylorModel;
  integral(a?: RationalLike, b?: RationalLike): RationalInterval;
  /** The derivative of the polynomial part only (the remainder says nothing about slopes). */
  derivative(): Rational[];
  describe(): string;
  toString(): string;
  toJSON(): Record<string, unknown>;
}
export { TaylorModel as TM };

export function exp(g: TaylorModel): TaylorModel;
export function sin(g: TaylorModel): TaylorModel;
export function cos(g: TaylorModel): TaylorModel;
export function tan(g: TaylorModel): TaylorModel;
export function log(g: TaylorModel): TaylorModel;
export function log1p(g: TaylorModel): TaylorModel;
export function atan(g: TaylorModel): TaylorModel;
export function asin(g: TaylorModel): TaylorModel;
export function acos(g: TaylorModel): TaylorModel;
export function sqrt(g: TaylorModel): TaylorModel;
/** The real cube root, defined for negative arguments too. */
export function cbrt(g: TaylorModel): TaylorModel;
export function erf(g: TaylorModel): TaylorModel;
export function reciprocal(g: TaylorModel): TaylorModel;
export function sinh(g: TaylorModel): TaylorModel;
export function cosh(g: TaylorModel): TaylorModel;
export function tanh(g: TaylorModel): TaylorModel;
/** g^a for a rational a. Negative bases are allowed when a has an odd denominator. */
export function power(g: TaylorModel, a: RationalLike): TaylorModel;

export interface SeriesSpec extends ModelOptions {
  centre?: RationalLike;
  degree?: number;
  coefficient?: (k: number) => RationalLike;
  coefficients?: RationalLike[];
  /** How the tail is bounded. */
  rule?: "exact" | "ratio" | "alternating" | "geometric" | "bound" | null;
  lookahead?: number;
  proven?: boolean;
  [extra: string]: unknown;
}
/** A Taylor model from a power series you supply, with a stated rule for the tail. */
export function series(domain: IntervalLike, spec?: SeriesSpec): TaylorModel;

type PointFunction = (x: RationalLike | RationalInterval, bits?: number) => RationalInterval;
/** Certified enclosures of the elementary functions at a point or over an interval. */
export const enclose: Record<
  "exp" | "log" | "log1p" | "sqrt" | "cbrt" | "atan" | "asin" | "acos" | "sin" | "cos" | "tan" | "erf" | "sinh" | "cosh" | "tanh"
  | "gamma" | "lgamma" | "digamma" | "Si" | "fresnelS" | "fresnelC" | "erfc",
  PointFunction
> & {
  /** ψ⁽ᵐ⁾: m = 0 is digamma, m = 1 trigamma. */
  polygamma(m: number, x: RationalLike | RationalInterval, bits?: number): RationalInterval;
  beta(a: RationalLike | RationalInterval, b: RationalLike | RationalInterval, bits?: number): RationalInterval;
  /** The regularized lower incomplete gamma function P(a, x) = γ(a, x)/Γ(a), for exact a > 0 and x ≥ 0. */
  gammaP(a: RationalLike, x: RationalLike | RationalInterval, bits?: number): RationalInterval;
  /** Q(a, x) = 1 − P(a, x). */
  gammaQ(a: RationalLike, x: RationalLike | RationalInterval, bits?: number): RationalInterval;
  /** The regularized incomplete beta function I_x(a, b), for exact a, b > 0 and 0 ≤ x ≤ 1. */
  betaI(x: RationalLike | RationalInterval, a: RationalLike, b: RationalLike, bits?: number): RationalInterval;
  /** The Bessel function J_n for a whole number n. */
  besselJ(n: number, x: RationalLike | RationalInterval, bits?: number): RationalInterval;
};
/** The Bernoulli number B_m, exactly. */
export function bernoulli(m: number): Rational;
export const constants: { pi(bits?: number): RationalInterval; e(bits?: number): RationalInterval };
export function bitsForDigits(digits: number): number;
/** The functions bound to one set of defaults: createScope({ order, bits }) or createScope({ digits }). */
export function createScope(options?: ModelOptions & { digits?: number }): Record<string, any>;

// ---- expressions

export function parse(text: string): Ast;
export function format(ast: Ast): string;
export function differentiate(ast: Ast, variable?: string): Ast;
/** Tidy an expression. Only cancels what is defined everywhere, so x/x and log(x) − log(x) stay. */
export function simplify(ast: Ast): Ast;
export function compileFloat(ast: Ast, variable?: string, params?: Record<string, number>): (x: number) => number;
export function modelOf(ast: Ast, x: TaylorModel, env?: Record<string, TaylorModel | RationalLike>): TaylorModel;
export function freeVariables(ast: Ast): Set<string>;
export function num(value: RationalLike): Ast;
export function v(name: string): Ast;
export function op(op: string, ...args: Ast[]): Ast;
export function call(name: string, ...args: Ast[]): Ast;
/** Read a number, bigint, decimal or fraction string as an exact Rational ("0.1" is 1/10). */
export function toRational(value: RationalLike | { numerator: bigint; denominator: bigint }): Rational;
/** Function names the parser knows. */
export const FUNCTIONS: Set<string>;
export const CONSTANTS: Set<string>;
/** erf in floating point (about 1e-15 accurate). */
export function erfFloat(x: number): number;
/** A certified interval for an expression with interval values for its variables. */
export function encloseAst(ast: Ast, env: Record<string, RationalInterval | RationalLike>, bits?: number): RationalInterval;

// ---- functions

export interface DigitsOptions extends ModelOptions {
  /** Decimal digits asked of the certified answer. */
  digits?: number;
  maxPieces?: number;
  maxBits?: number;
}

export class AnalyticFunction {
  constructor(expression: ExpressionLike, options?: { variable?: string; params?: Params });
  ast: Ast;
  variable: string;
  params: Params;
  toString(): string;
  /** The same function with other parameter values. */
  with(params: Params): AnalyticFunction;
  derivative(): AnalyticFunction;
  /** The function with removable points filled in where that can be read off the expression. */
  regular(): AnalyticFunction;
  float(x: number): number;
  model(domain: IntervalLike, options?: ModelOptions & { centre?: RationalLike }): TaylorModel;
  value(x: RationalLike, options?: DigitsOptions): Refinement<number, RationalInterval>;
  /** Certified Taylor coefficients f^(k)(c)/k! for k = 0…n (n ≤ 16), also at removable points such as sin(x)/x at 0. */
  taylor(c: RationalLike, n?: number, options?: { digits?: number }): RationalInterval[];
  /**
   * The limit at a rational point c (two-sided, or one-sided with `side`),
   * or at "inf" / "-inf". A RationalInterval that holds the limit, or
   * ±Infinity. Throws AnalyticError "no-limit" where none exists.
   */
  limit(c: RationalLike | EndLike, options?: { digits?: number; side?: "left" | "right" }): RationalInterval | number;
  /** The leading behaviour far out: f(x) = term·(coefficient + a part that dies out). */
  asymptotic(at?: "inf" | "-inf", options?: { digits?: number }): Asymptotic;
  /**
   * An improper integral: an end at "inf" or "-inf", or an end where f is
   * undefined. The exact value is a RationalInterval when it converges,
   * ±Infinity when it is proven to diverge (NaN: diverges with both signs).
   */
  improperIntegral(a: RationalLike | EndLike, b: RationalLike | EndLike, options?: { digits?: number; singular?: RationalLike[] }): Refinement<number, RationalInterval | number>;
  range(interval: IntervalLike, options?: DigitsOptions & { samples?: number }): Refinement<[number, number], RationalInterval>;
  integral(a: RationalLike, b: RationalLike, options?: DigitsOptions): Refinement<number, RationalInterval>;
}
export function fn(expression: ExpressionLike, options?: { variable?: string; params?: Params }): AnalyticFunction;
/** An infinite end of an interval. */
export type EndLike = "inf" | "-inf" | "+inf" | "∞" | "-∞" | number;
export interface Asymptotic {
  /** k, p and m in exp(k·x)·x^p·log(x)^m. */
  exp: Rational;
  power: Rational;
  log: Rational;
  coefficient: RationalInterval;
  /** True when the coefficient is only a range (sin(x)/x). */
  oscillates: boolean;
  /** The term as text, such as "exp(-2*x)*x^2". */
  term: string;
}

// ---- zeros, poles, extrema, inflections

export interface SearchOptions {
  variable?: string;
  params?: Params;
  /** Target width of each enclosure. */
  tolerance?: RationalLike;
  [extra: string]: unknown;
}
/** A floating-point guess from the quick stage. */
export interface Guess {
  kind: string;
  at: number;
  value?: number;
}
export interface ZeroRecord {
  /** "exact", "sign-change" and "isolated" are proven zeros; "possible" could not be decided; "everywhere" means the function is zero on all of [lo, hi]. */
  kind: "exact" | "sign-change" | "isolated" | "possible" | "undefined" | "everywhere" | string;
  lo: Rational;
  hi: Rational;
  /** True when exactly one zero is proven to lie in [lo, hi]. */
  unique: boolean;
  multiplicity?: number | null;
  [extra: string]: unknown;
}
export interface PoleRecord {
  kind: string;
  at: Rational | null;
  lo: Rational;
  hi: Rational;
  order: number | null;
  unique: boolean;
  [extra: string]: unknown;
}
export interface ExtremumRecord {
  /** "min", "max", "possible", or "constant" when the function is constant on [lo, hi]. */
  kind: "min" | "max" | "flat" | "possible" | "constant" | string;
  at: Rational | null;
  lo: Rational;
  hi: Rational;
  value: RationalInterval | null;
  unique: boolean;
  [extra: string]: unknown;
}
export function zeros(expression: ExpressionLike | AnalyticFunction, interval: IntervalLike, options?: SearchOptions): Refinement<Guess[], ZeroRecord[]>;
export function poles(expression: ExpressionLike | AnalyticFunction, interval: IntervalLike, options?: SearchOptions): Refinement<Guess[], PoleRecord[]>;
export function extrema(expression: ExpressionLike | AnalyticFunction, interval: IntervalLike, options?: SearchOptions): Refinement<Guess[], ExtremumRecord[]>;
export function inflections(expression: ExpressionLike | AnalyticFunction, interval: IntervalLike, options?: SearchOptions): Refinement<Guess[], ZeroRecord[]>;
/** The rational with the smallest denominator in [lo, hi]. */
export function simplestBetween(lo: RationalLike, hi: RationalLike): Rational;

// ---- differential equations

export interface OdeSpec extends ModelOptions {
  /** Right-hand side: one expression, or one per unknown. */
  f: ExpressionLike | ExpressionLike[];
  /** Initial value(s); an interval is allowed. */
  y0: RationalLike | RationalInterval | Array<RationalLike | RationalInterval>;
  t0?: RationalLike;
  /** Where to stop; may be less than t0 to integrate backward. */
  until: RationalLike;
  vars?: string[];
  time?: string;
  params?: Params;
  step?: RationalLike;
  minStep?: RationalLike;
  maxSteps?: number;
  tol?: RationalLike;
  /** Follow how the solution depends on the initial value (tighter over long times). Default true. */
  track?: boolean;
  previewSteps?: number;
  [extra: string]: unknown;
}
export interface OdeStep {
  t0: Rational;
  t1: Rational;
  models: TaylorModel[];
  [extra: string]: unknown;
}
export class ODESolution {
  steps: OdeStep[];
  /** False when the solver stopped before `until`; `reason` says why. */
  complete: boolean;
  reason: string | null;
  readonly t0: Rational;
  readonly t1: Rational;
  /** Certified enclosure(s) of y(t). */
  at(t: RationalLike): RationalInterval | RationalInterval[];
  readonly final: RationalInterval | RationalInterval[];
  describe(): string;
}
export const ode: {
  solve(spec: OdeSpec): Refinement<{ t: number[]; y: number[] | number[][] } | null, ODESolution>;
  step(spec: Omit<OdeSpec, "until"> & { step: RationalLike }): OdeStep & { model?: TaylorModel };
  ODESolution: typeof ODESolution;
};

// ---- piecewise functions

export type RegionSpec = string | IntervalLike | Region | ((x: Rational) => boolean);
export class Region {
  static from(spec: RegionSpec, options?: { variable?: string; params?: Params }): Region;
  constructor(spec: RegionSpec, options?: { variable?: string; params?: Params });
  match(x: RationalLike): boolean;
  test(x: number): boolean;
  intervals(a: RationalLike, b: RationalLike): unknown[];
  breakpoints(a: RationalLike, b: RationalLike): Rational[];
  toString(): string;
}
/** A region written as a template: where`0 <= x < ${b}`. */
export function where(strings: TemplateStringsArray, ...values: unknown[]): Region;
export function parsePiecewiseText(text: string): Array<[string, string]>;

export type PieceSpec = [RegionSpec, ExpressionLike | AnalyticFunction | number | bigint];
export class PiecewiseFunction {
  constructor(pieces: PieceSpec[] | string, options?: { variable?: string; params?: Params });
  toString(): string;
  with(params: Params): PiecewiseFunction;
  rule(i: number, n?: number | null): AnalyticFunction;
  locate(x: RationalLike): number;
  float(x: number): number;
  segments(a: RationalLike, b: RationalLike): unknown[];
  derivative(): PiecewiseFunction;
  value(x: RationalLike, options?: DigitsOptions): Refinement<number, RationalInterval>;
  range(interval: IntervalLike, options?: DigitsOptions): Refinement<[number, number], RationalInterval>;
  integral(a: RationalLike, b: RationalLike, options?: DigitsOptions): Refinement<number, RationalInterval>;
  /** Where the rule changes inside the interval, with the jump at each break. */
  breaks(interval: IntervalLike, options?: DigitsOptions): Refinement<unknown[], unknown[]>;
}
export function piecewise(pieces: PieceSpec[] | string, options?: { variable?: string; params?: Params }): PiecewiseFunction;

// ---- several variables

/** A box { x: [0, 1], y: [0, 2] }, iterated bounds { x: [0, 1], y: ["0", "x^2"] }, region text "0:x:1 && 0:y:x", or a Core MultiRegion. */
export type RegionLike = Record<string, [RationalLike | string, RationalLike | string]> | Array<[RationalLike | string, RationalLike | string]> | string | object;
export type PointLike = RationalLike[] | Record<string, RationalLike | [RationalLike, RationalLike] | RationalInterval>;
export interface Jet {
  value: RationalInterval;
  /** null where the function is not differentiable on the box. */
  gradient: RationalInterval[] | null;
  hessian: RationalInterval[][] | null;
  smooth: boolean;
}
export interface CriticalRecord {
  /** "min", "max", "saddle", "degenerate" (proven point, Hessian undecided) or "possible" (undecided box). */
  kind: "min" | "max" | "saddle" | "degenerate" | "possible";
  unique: boolean;
  point: RationalInterval[];
  value: RationalInterval | null;
}
export interface FieldOptions {
  digits?: number;
  bits?: number;
  maxBoxes?: number;
}
export class ScalarField {
  constructor(expression: ExpressionLike, variables: string[], options?: { params?: Params });
  ast: Ast;
  variables: readonly string[];
  params: Params;
  readonly dimension: number;
  toString(): string;
  with(params: Params): ScalarField;
  float(point: number[] | Record<string, number>): number;
  /** ∂f/∂name; several names give a higher partial. */
  partial(...names: string[]): ScalarField;
  gradient(): ScalarField[];
  hessian(): ScalarField[][];
  laplacian(): ScalarField;
  substitute(values: Record<string, RationalLike | string>): ScalarField | AnalyticFunction;
  /** f along a curve given by an expression for each variable. */
  along(curve: Record<string, string>, options?: { variable?: string }): AnalyticFunction;
  /** Value, gradient and Hessian at a point or over a box, certified. */
  jet(point: PointLike, options?: { digits?: number; order?: 0 | 1 | 2 }): Jet;
  value(point: PointLike, options?: { digits?: number }): Refinement<number, RationalInterval>;
  directional(point: PointLike, direction: Array<RationalLike | string> | Record<string, RationalLike | string>, options?: { digits?: number; unit?: boolean }): Refinement<number, RationalInterval>;
  /** The tangent plane at a point. */
  linearization(point: PointLike, options?: { digits?: number }): ScalarField;
  range(region: RegionLike, options?: FieldOptions & { samples?: number }): Refinement<[number, number], RationalInterval>;
  integral(region: RegionLike, options?: FieldOptions & { nodes?: number }): Refinement<number, RationalInterval>;
  criticalPoints(box: RegionLike, options?: FieldOptions & { starts?: number }): Refinement<Array<{ point: number[]; value: number }>, CriticalRecord[]>;
}
export function field(expression: ExpressionLike, variables: string[], options?: { params?: Params }): ScalarField;
export function jet(ast: Ast, env: Record<string, unknown>, names: string[], bits?: number, order?: number): unknown;
export function divergence(F: ExpressionLike[], variables: string[], options?: { params?: Params }): ScalarField;
/** Three ScalarFields in three variables; the scalar curl in two. */
export function curl(F: ExpressionLike[], variables: string[], options?: { params?: Params }): ScalarField[] | ScalarField;
export function jacobian(F: ExpressionLike[], variables: string[], options?: { params?: Params }): ScalarField[][];
/** ∫_C F·dr for a list F, or ∫_C f ds for one expression, along r(t). */
export function lineIntegral(F: ExpressionLike[] | ExpressionLike, variables: string[], curve: Record<string, string>, interval: [RationalLike, RationalLike], options?: DigitsOptions & { variable?: string; params?: Params }): Refinement<number, RationalInterval>;
/** The flux of F through r(u, v), or ∫∫ f dS for one expression. */
export function surfaceIntegral(F: ExpressionLike[] | ExpressionLike, variables: string[], surface: Record<string, string>, parameters: [string, string], region: RegionLike, options?: FieldOptions & { params?: Params }): Refinement<number, RationalInterval>;
/** ∫_a^b of a tree in one variable by fixed-point Taylor series, to the absolute width `tol`. */
export function quadrature(ast: Ast, variable: string, env: Record<string, unknown>, a: Rational, b: Rational, options: { tol: Rational; bits?: number; maxPieces?: number; order?: number }): { iv: unknown; pieces: number; met: boolean };

// ---- Fourier series

export class FourierSeries {
  interval: [Rational, Rational];
  /** b − a. */
  length: Rational;
  period: Rational;
  kind: "full" | "sine" | "cosine";
  terms: number;
  /** a[0] is a₀ (the mean is a₀/2). */
  a: RationalInterval[];
  /** b[0] is 0. */
  b: RationalInterval[];
  coefficient(n: number): { a: RationalInterval; b: RationalInterval };
  amplitude(n: number, bits?: number): RationalInterval;
  /** The partial sum as a function, for plotting. */
  partial(N?: number): AnalyticFunction;
  /** The partial sum at a rational point, certified. */
  value(x: RationalLike, N?: number, bits?: number): RationalInterval;
  /** (1/L)·∫ f². */
  meanSquare(): RationalInterval;
  /** (1/L)·∫ (f − S_N)², by Parseval. */
  meanSquareError(N?: number): RationalInterval;
  toString(N?: number, places?: number): string;
}
export function fourier(
  f: ExpressionLike | AnalyticFunction | PiecewiseFunction,
  interval: [RationalLike, RationalLike],
  options?: { terms?: number; digits?: number; kind?: "full" | "sine" | "cosine"; params?: Params; variable?: string },
): Refinement<{ a: number[]; b: number[] }, FourierSeries>;

// ---- boundary value problems

export interface BvpSpec {
  /** y″ as a formula in x, y and dy. */
  f: ExpressionLike;
  interval: [RationalLike, RationalLike];
  left: { y: RationalLike } | { dy: RationalLike };
  right: { y: RationalLike } | { dy: RationalLike };
  /** Names of y and y′ (default ["y", "dy"]) and of the independent variable (default "x"). */
  vars?: [string, string];
  time?: string;
  params?: Params;
  digits?: number;
  /** A starting guess for the unknown left-end value. */
  guess?: number;
  order?: number;
}
export class BVPSolution {
  tube: ODESolution;
  unknown: "y" | "dy";
  /** The enclosure of the left-end value that was solved for. */
  start: RationalInterval;
  linear: boolean;
  unique: boolean;
  interval: [Rational, Rational];
  at(x: RationalLike | RationalInterval): RationalInterval;
  slopeAt(x: RationalLike | RationalInterval): RationalInterval;
}
export function bvp(spec: BvpSpec): Refinement<{ t: Float64Array; y: Float64Array; dy: Float64Array; start: number } | null, BVPSolution>;

// ---- sequences and series

export interface SequenceOptions {
  /** The index (default "n"). */
  variable?: string;
  /** The first index (default 1). */
  from?: number;
  params?: Params;
}
export class Sequence {
  constructor(term: ExpressionLike, options?: SequenceOptions);
  readonly variable: string;
  readonly from: number;
  /** An exact Rational where the formula is rational at n, else a certified enclosure. */
  term(n: number, options?: { digits?: number }): Rational | RationalInterval;
  terms(count?: number, options?: { digits?: number }): Array<Rational | RationalInterval>;
  /** The limit as n → ∞, or ±Infinity. Throws AnalyticError ("no-limit", "undecided") where none is proven. */
  limit(options?: { digits?: number }): RationalInterval | number;
  /** The direction, proven for every n ≥ from. */
  monotone(options?: { digits?: number }): { direction: "increasing" | "decreasing" | "constant"; from: number; proven: string };
  /** Bounds on every term; null for a bound that does not exist. */
  bounds(options?: { digits?: number }): { lower: Rational | null; upper: Rational | null; bounded: boolean };
  series(): Series;
}
export function sequence(term: ExpressionLike, options?: SequenceOptions): Sequence;

export interface FixedPoint {
  point: RationalInterval;
  /** g′ at the fixed point. */
  multiplier: RationalInterval | null;
  kind: "attracting" | "repelling" | "neutral or undecided";
  unique: boolean | null;
}
export class RecursiveSequence {
  constructor(next: ExpressionLike, options: { start: RationalLike; variable?: string; params?: Params });
  /** Exact Rationals while the fractions stay short, then certified enclosures. */
  terms(count?: number, options?: { digits?: number; maxDigits?: number }): Array<Rational | RationalInterval>;
  fixedPoints(interval: IntervalLike, options?: { digits?: number }): FixedPoint[];
  /** The limit, proven by contraction on `basin`; `enters` is the first term proven to lie in it. */
  limit(interval: IntervalLike, options?: { digits?: number; maxSteps?: number }): { limit: RationalInterval; enters: number; rate: Rational; basin: RationalInterval };
}
export function recursive(next: ExpressionLike, options: { start: RationalLike; variable?: string; params?: Params }): RecursiveSequence;

export interface TestResult {
  test: "nth term" | "ratio" | "root" | "comparison" | "integral" | "alternating";
  verdict: "convergent" | "divergent" | "inconclusive";
  reason: string;
  /** The limit that decided (nth term, ratio, root). */
  limit?: RationalInterval | number;
  /** comparison: the scale n^p·log(n)^m the term behaves like. */
  like?: string;
  exponent?: Rational;
  log?: Rational;
  coefficient?: RationalInterval | null;
  /** integral, alternating: the index from which the hypothesis is proven. */
  from?: number;
  integral?: RationalInterval;
}
export interface SeriesSum {
  /** Holds the sum. */
  enclosure: RationalInterval;
  /** How many terms were added. */
  terms: number;
  upTo: number;
  partial: Rational | RationalInterval;
  /** Holds the sum of all later terms. */
  tail: RationalInterval;
  /** The argument that bounds the tail. */
  by: string;
  /** Whether the width asked for was reached. */
  met: boolean;
}
export class Series {
  constructor(term: ExpressionLike, options?: SequenceOptions);
  term(n: number, options?: { digits?: number }): Rational | RationalInterval;
  partial(N: number, options?: { digits?: number }): Rational | RationalInterval;
  divergenceTest(options?: { digits?: number }): TestResult;
  ratioTest(options?: { digits?: number }): TestResult;
  rootTest(options?: { digits?: number }): TestResult;
  comparisonTest(options?: { digits?: number }): TestResult;
  integralTest(options?: { digits?: number }): TestResult;
  alternatingTest(options?: { digits?: number }): TestResult;
  tests(options?: { digits?: number }): TestResult[];
  convergence(options?: { digits?: number }): { convergence: "absolutely convergent" | "conditionally convergent" | "convergent" | "divergent" | "undecided"; by: string | null; reason: string; test?: TestResult };
  /** Throws AnalyticError for a divergent or undecided series. */
  sum(options?: { digits?: number; maxTerms?: number }): SeriesSum;
}
export function sum(term: ExpressionLike, options?: SequenceOptions): Series;

export interface EndPoint {
  point: Rational;
  convergence: string;
  by: string | null;
  reason: string;
}
export class PowerSeries {
  constructor(coefficient: ExpressionLike, options?: { index?: string; from?: number; centre?: RationalLike; variable?: string });
  coefficient(n: number): Rational | RationalInterval;
  radius(options?: { digits?: number }): { radius: RationalInterval | number; limit: RationalInterval | number; by: string };
  /** `text` is the interval of convergence, with "?" at an end no test decided. */
  interval(options?: { digits?: number }): { radius: Rational | RationalInterval | number; left: EndPoint | null; right: EndPoint | null; text: string };
  at(x: RationalLike): Series;
  value(x: RationalLike, options?: { digits?: number; maxTerms?: number }): SeriesSum;
  partial(N: number): AnalyticFunction;
  derivative(): PowerSeries;
  integral(): PowerSeries;
}
export function powerSeries(coefficient: ExpressionLike, options?: { index?: string; from?: number; centre?: RationalLike; variable?: string }): PowerSeries;

/** Lagrange's bound M·r^(n+1)/(n+1)! beside the true maximum of |f − T_n| on the interval. */
export function taylorRemainder(
  f: ExpressionLike | AnalyticFunction,
  options: { about?: RationalLike; order?: number; on: [RationalLike, RationalLike]; variable?: string; digits?: number },
): { coefficients: RationalInterval[]; M: RationalInterval; radius: Rational; bound: Rational; actual: RationalInterval; holds: boolean };

export class FunctionSequence {
  constructor(term: ExpressionLike, options?: { variable?: string; index?: string });
  member(n: number): AnalyticFunction;
  pointwise(x: RationalLike, options?: { digits?: number }): RationalInterval | number;
  /** sup |f_n − limit| on the interval: the upper end is a proven bound, the lower end a value that is taken. */
  supDistance(n: number, interval: [RationalLike, RationalLike], limit?: ExpressionLike, options?: { digits?: number; samples?: number }): RationalInterval;
  uniform(interval: [RationalLike, RationalLike], limit?: ExpressionLike, options?: { ns?: number[]; digits?: number }): { verdict: "uniform" | "not uniform so far" | "undecided"; table: Array<{ n: number; sup: RationalInterval }>; reason: string; from?: number };
}
export function functionSequence(term: ExpressionLike, options?: { variable?: string; index?: string }): FunctionSequence;

// ---- theorems of vector calculus

export type Bounds = Record<string, [RationalLike | string, RationalLike | string]>;
export interface TheoremSide {
  name: string;
  value: RationalInterval;
  pieces?: Array<{ side?: string; face?: string; curve?: Record<string, string>; integrand?: string; value: RationalInterval }>;
  integrand?: ScalarField | string;
  curl?: ScalarField[];
  normal?: string[];
}
export interface TheoremCheck {
  statement: string;
  left: TheoremSide;
  right: TheoremSide;
  /** Whether the two enclosures meet, as the theorem says they must. */
  agree: boolean;
  overlap: RationalInterval | null;
}
export function greens(F: [ExpressionLike, ExpressionLike], variables: [string, string], region: Bounds, options?: { digits?: number; flux?: boolean }): TheoremCheck;
export function stokes(F: ExpressionLike[], variables: string[], surface: Record<string, ExpressionLike>, parameters: [string, string], region: Bounds, options?: { digits?: number }): TheoremCheck;
export function divergenceTheorem(
  F: ExpressionLike[],
  variables: string[],
  solid: Bounds,
  options?: { digits?: number; surface?: Array<{ name?: string; r: Record<string, ExpressionLike>; parameters: [string, string]; region: Bounds; orientation?: 1 | -1 }> },
): TheoremCheck;
export function changeOfVariables(
  f: ExpressionLike,
  variables: string[],
  map: Record<string, ExpressionLike>,
  newVariables: string[],
  region: Bounds,
  options?: { digits?: number; original?: RegionLike; directDigits?: number },
): { jacobian: string[][]; determinant: string; sign: string; factor: string; integrand: string; value: RationalInterval; direct?: RationalInterval; overlap?: RationalInterval | null; agree?: boolean };
export function potential(
  F: ExpressionLike[],
  variables: string[],
  options?: { digits?: number },
): {
  /** true: the curl multiplies out to 0. false: it is proven nonzero at `witness`. null: undecided. */
  conservative: boolean | null;
  curl: string[];
  witness: { point: Record<string, Rational>; curl: RationalInterval } | null;
  /** In closed form for polynomial fields. */
  potential: ScalarField | null;
  check: string[] | null;
  /** φ(p) − φ(from), by a certified line integral along the segment. */
  value(p: Array<RationalLike | string>, from?: Array<RationalLike | string>, options?: { digits?: number }): RationalInterval;
};
export interface LagrangeCandidate {
  point: Record<string, RationalInterval>;
  multiplier: RationalInterval;
  value: RationalInterval;
  unique: boolean | null;
  proven: boolean;
}
export function lagrange(
  f: ExpressionLike,
  constraint: ExpressionLike,
  variables: string[],
  box: Bounds,
  options?: { multiplier?: [RationalLike, RationalLike]; multiplierName?: string; digits?: number; maxBoxes?: number },
): { lagrangian: string; candidates: LagrangeCandidate[]; max: { value: RationalInterval; at: Array<Record<string, RationalInterval>> } | null; min: { value: RationalInterval; at: Array<Record<string, RationalInterval>> } | null; complete: boolean };

// ---- differential geometry (also "@ratmath/analytic/geometry")
/** A quotient of polynomials in variables and calls, with sin² + cos² = 1 used and common factors cancelled. */
export function tidy(tree: Ast): Ast;
export type PointLike = RationalLike | string | RationalInterval;
export interface CurvePoint {
  point: RationalInterval[];
  velocity: RationalInterval[];
  speed: RationalInterval;
  tangent: RationalInterval[];
  normal: RationalInterval[] | null;
  binormal?: RationalInterval[] | null;
  /** Signed for a plane curve: positive where it turns left. */
  curvature: RationalInterval;
  torsion?: RationalInterval | null;
  /** Radius and centre of the osculating circle; null where the curvature may vanish. */
  radius: RationalInterval | null;
  centre: RationalInterval[] | null;
}
export class Curve {
  constructor(components: ExpressionLike[], parameter?: string, options?: { params?: Record<string, PointLike> });
  readonly parameter: string;
  readonly dimension: 2 | 3;
  readonly position: string[];
  readonly velocity: string[];
  readonly acceleration: string[];
  speed(): string;
  curvature(): string;
  curvatureAst(): Ast;
  torsion(): string;
  torsionAst(): Ast;
  evolute(): Curve;
  length(interval: [PointLike, PointLike], options?: { digits?: number }): RationalInterval;
  totalCurvature(interval: [PointLike, PointLike], options?: { digits?: number }): RationalInterval;
  at(t: PointLike, options?: { digits?: number }): CurvePoint;
}
export function curve(components: ExpressionLike[], parameter?: string, options?: { params?: Record<string, PointLike> }): Curve;
export interface GaussBonnetReport {
  statement: string;
  curvature: { name: string; value: RationalInterval };
  boundary: { name: string; value: RationalInterval; pieces: Array<{ side: string; path: Record<string, string>; value: RationalInterval }> };
  angles: { name: string; value: RationalInterval; corners: Array<{ at: RationalInterval[]; exterior: RationalInterval }> };
  total: RationalInterval;
  expected: RationalInterval;
  agree: boolean;
}
export class Metric {
  constructor(g: { E: ExpressionLike | number; F?: ExpressionLike | number; G: ExpressionLike | number }, parameters?: [string, string], options?: { params?: Record<string, PointLike> });
  readonly parameters: [string, string];
  first(): { E: string; F: string; G: string };
  /** Keys such as "u_uv" for Γᵘ_uv. */
  christoffel(): Record<string, string>;
  christoffelAst(): Ast[][][];
  gaussian(): string;
  gaussianAst(): Ast;
  area(region: Bounds, options?: { digits?: number }): RationalInterval;
  totalCurvature(region: Bounds, options?: { digits?: number }): RationalInterval;
  /** State (u, v, u′, v′). */
  geodesic(spec: { from: [PointLike, PointLike]; direction: [PointLike, PointLike]; until: RationalLike | string; unit?: boolean; order?: number; tol?: RationalLike | string; track?: boolean; step?: RationalLike | string }): Refinement<{ t: Float64Array; y: Float64Array[] } | null, ODESolution>;
  transport(
    path: Record<string, ExpressionLike>,
    interval: [RationalLike | string, RationalLike | string],
    vector: [PointLike, PointLike],
    options?: { parameter?: string; order?: number; tol?: RationalLike | string; step?: RationalLike | string },
  ): { start: RationalInterval[]; vector: RationalInterval[]; length: RationalInterval; lengthAfter: RationalInterval | null; angle: RationalInterval | null; solution: ODESolution };
  geodesicCurvature(path: Record<string, ExpressionLike>): string;
  geodesicCurvature(path: Record<string, ExpressionLike>, t: PointLike, options?: { parameter?: string; digits?: number }): RationalInterval;
  gaussBonnet(region: Bounds, options?: { digits?: number }): GaussBonnetReport;
}
export function metric(g: { E: ExpressionLike | number; F?: ExpressionLike | number; G: ExpressionLike | number }, parameters?: [string, string], options?: { params?: Record<string, PointLike> }): Metric;
export interface SurfacePoint {
  point: RationalInterval[];
  normal: RationalInterval[];
  E: RationalInterval; F: RationalInterval; G: RationalInterval;
  L: RationalInterval; M: RationalInterval; N: RationalInterval;
  gaussian: RationalInterval;
  mean: RationalInterval;
  principal: [RationalInterval, RationalInterval];
  /** null when the enclosures cannot tell. */
  kind: "elliptic" | "hyperbolic" | "parabolic" | "planar" | null;
}
export class Surface extends Metric {
  constructor(components: ExpressionLike[], parameters?: [string, string], options?: { params?: Record<string, PointLike> });
  readonly position: string[];
  normal(): string[];
  second(): { L: string; M: string; N: string };
  mean(): string;
  meanAst(): Ast;
  intrinsicGaussian(): string;
  at(u: PointLike, v: PointLike, options?: { digits?: number }): SurfacePoint;
}
export function surface(components: ExpressionLike[], parameters?: [string, string], options?: { params?: Record<string, PointLike> }): Surface;

// ---- differential equations: methods
export interface MethodStep { what: string; formula: string }
export interface CheckReport { agree: boolean; numeric: RationalInterval; formula?: RationalInterval; relation?: RationalInterval; constant?: RationalInterval }
export interface ParticularSolution {
  x0: RationalLike | string;
  y0: RationalLike | string;
  constant: string;
  /** The explicit solution, or null when the method gives only a relation. */
  solution: string | null;
  relation: string | null;
  at(x: PointLike, options?: { digits?: number }): RationalInterval;
  /** The formula against the validated numerical solution at x1. */
  check(x1: RationalLike | string, options?: { digits?: number; order?: number; tol?: RationalLike | string; track?: boolean }): CheckReport;
}
export interface FirstOrderSolution {
  equation: string;
  type: "linear" | "separable" | "bernoulli" | "homogeneous" | "exact" | null;
  types: string[];
  steps: MethodStep[];
  /** "y = …" with the constant C, or null. */
  general: string | null;
  /** "G(x, y) = C", or null. */
  implicit: string | null;
  singular: string[];
  through(x0: RationalLike | string, y0: RationalLike | string): ParticularSolution;
}
export function firstOrder(rhs: ExpressionLike, options?: { x?: string; y?: string; method?: "linear" | "separable" | "bernoulli" | "homogeneous" }): FirstOrderSolution;
export function exactEquation(M: ExpressionLike, N: ExpressionLike, options?: { x?: string; y?: string }): FirstOrderSolution & { exact: boolean; factor: string | null; potential: string | null };
export interface LinearODESolution {
  order: number;
  characteristic: string;
  roots: Array<{ root: string; kind: "real" | "complex"; multiplicity: number }>;
  basis: string[];
  homogeneous: string;
  particular: string | null;
  method: "undetermined coefficients" | "variation of parameters" | null;
  verified?: boolean;
  steps: MethodStep[];
  general: string | null;
  initial(values: Array<RationalLike | string>, x0?: RationalLike | string): { constants: string[]; solution: string; tree: Ast; at(x: PointLike, options?: { digits?: number }): RationalInterval; check(x1: RationalLike | string, options?: { digits?: number; order?: number; tol?: RationalLike | string }): CheckReport };
}
/** Coefficients highest derivative first: linearODE([1, -3, 2], "exp(x)") is y″ − 3y′ + 2y = eˣ. */
export function linearODE(coefficients: Array<RationalLike | string>, forcing?: ExpressionLike | number, options?: { x?: string; y?: string }): LinearODESolution;
export function laplace(f: ExpressionLike, options?: { t?: string; s?: string; delay?: RationalLike | string }): string;
export function inverseLaplace(F: ExpressionLike, options?: { t?: string; s?: string }): { partialFractions: string; result: string; tree: Ast };
export function linearSystem(matrix: Array<Array<RationalLike | string>>, options?: { t?: string }): {
  matrix: Rational[][];
  trace: Rational;
  determinant: Rational;
  discriminant: Rational;
  eigenvalues: string[];
  eigenvectors: Array<string[] | null> | null;
  kind: string;
  stability: string;
  exponential: string[][];
  solution(x0: Array<RationalLike | string>): string[];
};
export interface Equilibrium {
  point: RationalInterval[];
  unique: boolean;
  jacobian: RationalInterval[][];
  trace: RationalInterval;
  determinant: RationalInterval;
  kind: string | null;
  stability: string | null;
  hyperbolic: boolean | null;
}
export class PlanarSystem {
  constructor(field: ExpressionLike[], variables?: [string, string], options?: { params?: Record<string, PointLike> });
  jacobian(): string[][];
  nullclines(): Record<string, string>;
  equilibria(box: Bounds, options?: { digits?: number; tol?: RationalLike | string; maxBoxes?: number }): Equilibrium[] & { complete: boolean };
  conserves(H: ExpressionLike): boolean;
  along(V: ExpressionLike): string;
  orbit(spec: { from: Array<RationalLike | string>; until: RationalLike | string; order?: number; tol?: RationalLike | string }): Refinement<unknown, ODESolution>;
}
export function planarSystem(field: ExpressionLike[], variables?: [string, string], options?: { params?: Record<string, PointLike> }): PlanarSystem;
export function seriesSolution(spec: { p?: ExpressionLike | number; q?: ExpressionLike | number; about?: RationalLike | string; order?: number; x?: string }): {
  about: Rational;
  kind: "ordinary" | "regular singular" | "irregular singular";
  indicial?: string;
  exponents?: Array<Rational | string> | null;
  solutions: Array<{ exponent: Rational; coefficients: Rational[]; text: string }>;
  notes: string[];
  /** Distance to the nearest other singular point (a floating-point estimate; Infinity when there is none). */
  radius?: number;
};
export interface SeriesValue { value: RationalInterval | null; partial: RationalInterval; tail: Rational | null }
export interface SeparatedSolution {
  equation: string;
  terms: number;
  at(...point: Array<RationalLike | string>): SeriesValue;
  formula(terms?: number, digits?: number): string;
}
export function heat(spec: { k?: RationalLike | string; length?: RationalLike | string; initial: ExpressionLike; ends?: "fixed" | "insulated"; terms?: number; digits?: number; x?: string }): SeparatedSolution & { coefficients: RationalInterval[]; modes: Array<{ n: number; coefficient: RationalInterval; rate: string }> };
export function laplaceRectangle(spec: { width?: RationalLike | string; height?: RationalLike | string; top: ExpressionLike; terms?: number; digits?: number; x?: string }): SeparatedSolution & { coefficients: RationalInterval[] };
export function laplaceDisc(spec: { radius?: RationalLike | string; boundary: ExpressionLike; terms?: number; digits?: number; angle?: string }): SeparatedSolution & { coefficients: { a: RationalInterval[]; b: RationalInterval[] }; mean: RationalInterval };
export function wave(spec: { c?: RationalLike | string; length?: RationalLike | string | null; position?: ExpressionLike; velocity?: ExpressionLike; digits?: number; x?: string }): {
  equation: string;
  speed: Rational;
  length: Rational | null;
  at(x: RationalLike | string, t: RationalLike | string): RationalInterval;
  travelling: { right: string; left: string } | null;
  modes(N?: number): Array<{ n: number; frequency: string; cos: RationalInterval; sin: RationalInterval }>;
};
export function sturmLiouville(spec: { p?: ExpressionLike; q?: ExpressionLike; w?: ExpressionLike; interval: [RationalLike | string, RationalLike | string]; count?: number; from?: number; to?: number; width?: RationalLike | string; certify?: boolean; x?: string }): Array<{ index: number; eigenvalue: RationalInterval; estimate: number; proven: boolean }>;
export function antiderivative(tree: Ast, name?: string): { tree: Ast; trust: "proven" | "checked" } | null;
export function partialFractions(N: Rational[], D: Rational[]): { poly: Rational[]; linear: Array<{ root: Rational; power: number; coeff: Rational }>; quadratic: Array<{ p: Rational; q: Rational; alpha: Rational; beta: Rational }> } | null;

// ---- numerical methods for teaching (also "@ratmath/analytic/methods")
export function exactOf(x: number): Rational;
export function nearestDouble(q: RationalLike | string): number;
export function floatParts(x: number, intended?: string): {
  value: number; sign: number; exponent: number; mantissa: bigint; bits: string; exact: Rational; ulp: Rational; next: number; previous: number;
  intended?: Rational; error?: Rational; relativeError?: Rational;
};
export function floatOp(op: "+" | "-" | "*" | "/", a: number, b: number): { result: number; exact: Rational; error: Rational; relativeError: Rational | null; exactlyRepresentable: boolean };
export function roundoff(expression: ExpressionLike, inputs?: Record<string, number>, options?: { digits?: number }): {
  float: number; exact: RationalInterval; error: number; relativeError: number; digitsLost: number;
  steps: Array<{ expression: string; float: number; exact: RationalInterval; relativeError: number }>;
};
export interface RootIteration { n: number; x: number; fx?: number; dfx?: number; a?: number; b?: number; bound?: number; error: number | null }
export interface RootRun { method: string; iterations: RootIteration[]; root: RationalInterval | null; estimate: number; order: number | null; derivative?: string; multiplier?: RationalInterval | null; ratio?: number | null }
export interface RootOptions { variable?: string; steps?: number; tol?: number; digits?: number }
export function bisection(f: ExpressionLike, bracket: [number, number], options?: RootOptions): RootRun;
export function newton(f: ExpressionLike, x0: number, options?: RootOptions): RootRun;
export function secant(f: ExpressionLike, x0: number, x1: number, options?: RootOptions): RootRun;
export function fixedPoint(g: ExpressionLike, x0: number, options?: RootOptions): RootRun;
export interface Interpolant {
  nodes: Rational[]; values: Rational[]; degree: number; dividedDifferences: Rational[][]; newton: string; lagrange: string; polynomial: string; coefficients: Rational[];
  at(x: RationalLike | string): Rational;
  error(x: RationalLike | string): RationalInterval;
  maxError(interval: [RationalLike | string, RationalLike | string]): { value: RationalInterval; attained: Rational; at: Rational; textbook: Rational | null };
}
export function interpolate(source: Array<[RationalLike | string, RationalLike | string]> | ExpressionLike, options?: { nodes?: Array<RationalLike | string>; variable?: string }): Interpolant;
export function equallySpaced(a: RationalLike | string, b: RationalLike | string, n: number): Rational[];
export function chebyshevNodes(a: RationalLike | string, b: RationalLike | string, n: number, bits?: number): Rational[];
export function spline(points: Array<[RationalLike | string, RationalLike | string]>): { pieces: Array<{ from: Rational; to: Rational; coefficients: Rational[]; polynomial: string }>; moments: Rational[]; at(x: RationalLike | string): Rational };
export function leastSquares(points: Array<[RationalLike | string, RationalLike | string]>, degree?: number): { coefficients: Rational[]; polynomial: string; residual: Rational; at(x: RationalLike | string): Rational };
export function differences(f: ExpressionLike, x: number, options?: { kind?: "forward" | "backward" | "central" | "second"; steps?: number[]; variable?: string }): { exact: RationalInterval; rows: Array<{ h: number; value: number; error: number; truncation: number | null }>; best: { h: number; value: number; error: number } };
export function richardson(f: ExpressionLike, x: number, options?: { h?: number; levels?: number; variable?: string }): { table: number[][]; errors: number[][]; exact: RationalInterval };
export function quadratureRule(f: ExpressionLike, interval: [RationalLike | string, RationalLike | string], options?: { rule?: "midpoint" | "trapezoid" | "simpson"; n?: number; variable?: string }): { rule: string; panels: number; h: Rational; order: number; value: RationalInterval; exact: RationalInterval; error: RationalInterval; bound: Rational | null };
export function romberg(f: ExpressionLike, interval: [RationalLike | string, RationalLike | string], options?: { levels?: number; variable?: string }): { table: number[][]; errors: number[][]; exact: RationalInterval };
export function legendre(n: number): Rational[];
export function gaussLegendre(n: number, options?: { digits?: number }): { polynomial: Rational[]; nodes: RationalInterval[]; weights: RationalInterval[] };
export function gaussRule(f: ExpressionLike, interval: [RationalLike | string, RationalLike | string], n?: number, options?: { digits?: number; variable?: string }): { value: RationalInterval; exact: RationalInterval; error: RationalInterval; nodes: RationalInterval[]; weights: RationalInterval[] };
export type OneStepMethod = "euler" | "heun" | "midpoint" | "rk4" | "ab2";
export interface OdeMethodSpec { method?: OneStepMethod; t0?: number; y0: number; until: number; steps?: number; variables?: [string, string] }
export function odeMethod(f: ExpressionLike, spec: OdeMethodSpec): { method: string; order: number; h: number; steps: Array<{ n: number; t: number; y: number; exact: RationalInterval | null; error: number | null }>; finalError: number | null };
export function stepSizeStudy(f: ExpressionLike, spec: OdeMethodSpec & { counts?: number[] }): { rows: Array<{ steps: number; h: number; error: number | null; ratio: number | null; observedOrder: number | null }> };
export function stability(method?: "euler" | "heun" | "midpoint" | "rk4"): { method: string; polynomial: string; interval: [RationalInterval, RationalInterval]; largestStep(lambda: RationalLike | string | number): RationalInterval };
