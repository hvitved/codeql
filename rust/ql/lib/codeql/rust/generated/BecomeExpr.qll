// generated by codegen
/**
 * This module provides the generated definition of `BecomeExpr`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.generated.Synth
private import codeql.rust.generated.Raw
import codeql.rust.elements.Expr

/**
 * INTERNAL: This module contains the fully generated definition of `BecomeExpr` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::BecomeExpr` class directly.
   * Use the subclass `BecomeExpr`, where the following predicates are available.
   */
  class BecomeExpr extends Synth::TBecomeExpr, Expr {
    override string getAPrimaryQlClass() { result = "BecomeExpr" }

    /**
     * Gets the expression of this become expression.
     */
    Expr getExpr() {
      result =
        Synth::convertExprFromRaw(Synth::convertBecomeExprToRaw(this).(Raw::BecomeExpr).getExpr())
    }
  }
}
