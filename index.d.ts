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
  "exp" | "log" | "log1p" | "sqrt" | "cbrt" | "atan" | "asin" | "acos" | "sin" | "cos" | "tan" | "erf" | "sinh" | "cosh" | "tanh",
  PointFunction
>;
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
  /** The two-sided limit at c, certified, including removable points. */
  limit(c: RationalLike, options?: { digits?: number }): RationalInterval;
  range(interval: IntervalLike, options?: DigitsOptions & { samples?: number }): Refinement<[number, number], RationalInterval>;
  integral(a: RationalLike, b: RationalLike, options?: DigitsOptions): Refinement<number, RationalInterval>;
}
export function fn(expression: ExpressionLike, options?: { variable?: string; params?: Params }): AnalyticFunction;

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
