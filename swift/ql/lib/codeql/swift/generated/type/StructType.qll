// generated by codegen/codegen.py
/**
 * This module provides the generated definition of `StructType`.
 * INTERNAL: Do not import directly.
 */

private import codeql.swift.generated.Synth
private import codeql.swift.generated.Raw
import codeql.swift.elements.type.NominalType

module Generated {
  /**
   * INTERNAL: Do not reference the `Generated::StructType` class directly.
   * Use the subclass `StructType`, where the following predicates are available.
   */
  class StructType extends Synth::TStructType, NominalType {
    override string getAPrimaryQlClass() { result = "StructType" }
  }
}
