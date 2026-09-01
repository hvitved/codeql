/** Provides classes representing types without type arguments. */

import unified
private import unified as Unified
private import TypeInference
private import codeql.unified.internal.StaticNameBinding

/**
 * Holds if `a` is an associated type parameter of the protocol `c`,
 * either directly or inherited from a base protocol.
 */
private predicate associatedTypeParameter(
  ClassLikeDeclaration c, AssociatedTypeDeclaration a, boolean inherited
) {
  c.hasModifier("protocol") and // todo
  (
    a = c.getAMember() and
    inherited = false
    or
    associatedTypeParameterInherited(c, a, _, _, _) and
    inherited = true
  )
}

/**
 * TODO
 */
pragma[nomagic]
predicate associatedTypeParameterInherited(
  ClassLikeDeclaration c, AssociatedTypeDeclaration a, ClassLikeDeclaration base,
  NamedTypeExpr baseRef, string name
) {
  associatedTypeParameter(base, a, _) and
  baseRef = c.getABaseType().getType() and
  base.getName() = getStaticBindingTarget(baseRef.getName()) and
  name = a.getName().getValue()
}

// todo: not a newtype?
cached
newtype TType =
  TClassLikeDeclarationType(ClassLikeDeclaration c) { CachedStage::ref() } or
  TClosureParameterPseudoType(Parameter p) {
    exists(FunctionExpr fe |
      p = fe.getAParameter() and
      not exists(p.getType())
    )
  } or
  TTypeParameterType(Unified::TypeParameter tp) or
  TAssociatedTypeParameterType(
    ClassLikeDeclaration c, AssociatedTypeDeclaration a, boolean inherited
  ) {
    associatedTypeParameter(c, a, inherited)
  } or
  TUnknownType()

/**
 * A type without type arguments.
 *
 * Note that this type includes things that, strictly speaking, are not Rust
 * types, such as traits and implementation blocks.
 */
abstract class Type extends TType {
  /**
   * Gets the `i`th positional type parameter of this type, if any.
   *
   * This excludes synthetic type parameters, such as associated types in traits.
   */
  abstract TypeParameter getPositionalTypeParameter(int i);

  /**
   * Gets a type parameter of this type.
   *
   * This includes both positional type parameters and synthetic type parameters,
   * such as associated types in traits.
   */
  TypeParameter getATypeParameter() { result = this.getPositionalTypeParameter(_) }

  /** Gets a textual representation of this type. */
  abstract string toString();

  /** Gets the location of this type. */
  abstract Location getLocation();
}

class ClassLikeDeclarationType extends Type, TClassLikeDeclarationType {
  ClassLikeDeclaration c;

  ClassLikeDeclarationType() { this = TClassLikeDeclarationType(c) }

  /** Gets the type item that this data type represents. */
  ClassLikeDeclaration getClassLikeDeclaration() { result = c }

  string getName() { result = c.getName().getValue() }

  override TypeParameter getPositionalTypeParameter(int i) {
    result = TTypeParameterType(c.getTypeParameter(i))
  }

  override TypeParameter getATypeParameter() {
    result = super.getATypeParameter()
    or
    result = TAssociatedTypeParameterType(c, _, _)
  }

  override string toString() { result = c.getName().getValue() }

  override Location getLocation() { result = c.getLocation() }
}

class StructType extends ClassLikeDeclarationType {
  StructType() { c.getAModifier().getValue() = "struct" }
}

class BuiltinType extends StructType {
  BuiltinType() { this.getLocation().getFile().getBaseName() = "builtin.swift" }
}

abstract class PseudoType extends Type {
  override TypeParameter getPositionalTypeParameter(int i) { none() }
}

/**
 * A special pseudo type used to indicate that the actual type may have to be
 * inferred by propagating type information back into call arguments.
 *
 * For example, in
 *
 * ```rust
 * let x = Default::default();
 * foo(x);
 * ```
 *
 * `Default::default()` is assigned this type, which allows us to infer the actual
 * type from the type of `foo`'s first parameter.
 *
 * Unknown types are not restricted to root types, for example in a call like
 * `Vec::new()` we assign this type at the type path corresponding to the type
 * parameter of `Vec`.
 *
 * Unknown types are used to restrict when type information is allowed to flow
 * into call arguments (including method call receivers), in order to avoid
 * combinatorial explosions.
 */
class UnknownType extends PseudoType, TUnknownType {
  override string toString() { result = "(unknown type)" }

  override Location getLocation() { result instanceof EmptyLocation }
}

class ClosureParameterPseudoType extends PseudoType, TClosureParameterPseudoType {
  private Parameter param;

  ClosureParameterPseudoType() { this = TClosureParameterPseudoType(param) }

  Parameter getParam() { result = param }

  override string toString() { result = "(closure parameter " + param + ")" }

  override Location getLocation() { result = param.getLocation() }
}

/** A type parameter. */
abstract class TypeParameter extends Type {
  override TypeParameter getPositionalTypeParameter(int i) { none() }

  abstract AstNode getDeclaringItem();
}

private class IdAstNode =
  @unified_type_parameter or @unified_class_like_declaration or @unified_associated_type_declaration;

private predicate id(IdAstNode x, IdAstNode y) { x = y }

private predicate idOf(IdAstNode x, int y) = equivalenceRelation(id/2)(x, y)

int idOfTypeParameterAstNode(AstNode node) { idOf(node, result) }

/** A type parameter from source code. */
class TypeParameterType extends TypeParameter, TTypeParameterType {
  private Unified::TypeParameter typeParam;

  TypeParameterType() { this = TTypeParameterType(typeParam) }

  Unified::TypeParameter getTypeParameter() { result = typeParam }

  override ClassLikeDeclaration getDeclaringItem() { typeParam = result.getATypeParameter() }

  override string toString() { result = typeParam.getName().getValue() }

  override Location getLocation() { result = typeParam.getLocation() }
}

class AssociatedTypeParameterType extends TypeParameter, TAssociatedTypeParameterType {
  private Unified::ClassLikeDeclaration c;
  private Unified::AssociatedTypeDeclaration assocTypeDecl;
  private boolean inherited;

  AssociatedTypeParameterType() { this = TAssociatedTypeParameterType(c, assocTypeDecl, inherited) }

  Unified::AssociatedTypeDeclaration getAssociatedTypeDeclaration() { result = assocTypeDecl }

  override ClassLikeDeclaration getDeclaringItem() { result = c }

  override string toString() {
    if inherited = true
    then result = assocTypeDecl.getName().getValue() + " (inherited)"
    else result = assocTypeDecl.getName().getValue()
  }

  override Location getLocation() {
    if inherited = true then result = c.getLocation() else result = assocTypeDecl.getLocation()
  }
}
