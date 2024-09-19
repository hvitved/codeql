// generated by codegen, do not edit
/**
 * This module provides the generated definition of `RecordExprField`.
 * INTERNAL: Do not import directly.
 */

private import codeql.rust.elements.internal.generated.Synth
private import codeql.rust.elements.internal.generated.Raw
import codeql.rust.elements.internal.AstNodeImpl::Impl as AstNodeImpl
import codeql.rust.elements.Attr
import codeql.rust.elements.Expr
import codeql.rust.elements.NameRef

/**
 * INTERNAL: This module contains the fully generated definition of `RecordExprField` and should not
 * be referenced directly.
 */
module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::RecordExprField` class directly.
   * Use the subclass `RecordExprField`, where the following predicates are available.
   */
  class RecordExprField extends Synth::TRecordExprField, AstNodeImpl::AstNode {
    override string getAPrimaryQlClass() { result = "RecordExprField" }

    /**
     * Gets the `index`th attr of this record expression field (0-based).
     */
    Attr getAttr(int index) {
      result =
        Synth::convertAttrFromRaw(Synth::convertRecordExprFieldToRaw(this)
              .(Raw::RecordExprField)
              .getAttr(index))
    }

    /**
     * Gets any of the attrs of this record expression field.
     */
    final Attr getAnAttr() { result = this.getAttr(_) }

    /**
     * Gets the number of attrs of this record expression field.
     */
    final int getNumberOfAttrs() { result = count(int i | exists(this.getAttr(i))) }

    /**
     * Gets the expression of this record expression field, if it exists.
     */
    Expr getExpr() {
      result =
        Synth::convertExprFromRaw(Synth::convertRecordExprFieldToRaw(this)
              .(Raw::RecordExprField)
              .getExpr())
    }

    /**
     * Holds if `getExpr()` exists.
     */
    final predicate hasExpr() { exists(this.getExpr()) }

    /**
     * Gets the name reference of this record expression field, if it exists.
     */
    NameRef getNameRef() {
      result =
        Synth::convertNameRefFromRaw(Synth::convertRecordExprFieldToRaw(this)
              .(Raw::RecordExprField)
              .getNameRef())
    }

    /**
     * Holds if `getNameRef()` exists.
     */
    final predicate hasNameRef() { exists(this.getNameRef()) }
  }
}
