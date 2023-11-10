// generated by codegen/codegen.py
/**
 * This module provides the generated definition of `GuardStmt`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.stmt.BraceStmt
import codeql.swift.elements.stmt.LabeledConditionalStmt

module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::GuardStmt` class directly.
   * Use the subclass `GuardStmt`, where the following predicates are available.
   */
  class GuardStmt extends Synth::TGuardStmt, LabeledConditionalStmt {
    override string getAPrimaryQlClass() { result = "GuardStmt" }

    /**
     * Gets the body of this guard statement.
     */
    BraceStmt getBody() {
      result =
        Synth::convertBraceStmtFromRaw(Synth::convertGuardStmtToRaw(this).(Raw::GuardStmt).getBody())
    }
  }
}
