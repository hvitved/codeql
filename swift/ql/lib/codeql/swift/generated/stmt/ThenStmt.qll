// generated by codegen/codegen.py
/**
 * This module provides the generated definition of `ThenStmt`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.expr.Expr
import codeql.swift.elements.stmt.Stmt

/**
 * INTERNAL: This module contains the fully generated definition of `ThenStmt` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * A statement implicitly wrapping values to be used in branches of if/switch expressions. For example in:
   * ```
   * let rank = switch value {
   *     case 0..<0x80: 1
   *     case 0x80..<0x0800: 2
   *     default: 3
   * }
   * ```
   * the literal expressions `1`, `2` and `3` are wrapped in `ThenStmt`.
   * INTERNAL: Do not reference the `Generated::ThenStmt` class directly.
   * Use the subclass `ThenStmt`, where the following predicates are available.
   */
  class ThenStmt extends Synth::TThenStmt, Stmt {
    override string getAPrimaryQlClass() { result = "ThenStmt" }

    /**
     * Gets the result of this then statement.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Expr getImmediateResult() {
      result =
        Synth::convertExprFromRaw(Synth::convertThenStmtToRaw(this).(Raw::ThenStmt).getResult())
    }

    /**
     * Gets the result of this then statement.
     */
    final Expr getResult() {
      exists(Expr immediate |
        immediate = this.getImmediateResult() and
        result = immediate.resolve()
      )
    }
  }
}
