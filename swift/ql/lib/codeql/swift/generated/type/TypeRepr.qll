// generated by codegen/codegen.py
private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.AstNode
import codeql.swift.elements.type.Type

module Generated {
  class TypeRepr extends Synth::TTypeRepr, AstNode {
    override string getAPrimaryQlClass() { result = "TypeRepr" }

    /**
     * Gets the type of this type representation.
     *
     * This includes nodes from the "hidden" AST. It can be overridden in subclasses to change the
     * behavior of both the `Immediate` and non-`Immediate` versions.
     */
    Type getImmediateType() {
      result =
        Synth::convertTypeFromRaw(Synth::convertTypeReprToRaw(this).(Raw::TypeRepr).getType())
    }

    /**
     * Gets the type of this type representation.
     */
    final Type getType() {
      exists(Type immediate |
        immediate = this.getImmediateType() and
        if exists(this.getResolveStep()) then result = immediate else result = immediate.resolve()
      )
    }
  }
}
