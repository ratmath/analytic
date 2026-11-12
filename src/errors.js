/**
 * Raised when an operation cannot return a valid enclosure: a hypothesis
 * fails (argument range touches a singularity), domains differ, or an input
 * has the wrong type. The library refuses rather than returning a bound that
 * is not proven.
 */
export class AnalyticError extends Error {
  constructor(code, message, details = {}) {
    super(message);
    this.name = "AnalyticError";
    this.code = code;
    this.details = details;
  }
}

export function refuse(code, message, details) {
  throw new AnalyticError(code, message, details);
}
