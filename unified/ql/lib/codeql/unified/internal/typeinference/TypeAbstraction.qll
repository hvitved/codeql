private import unified as Unified
private import Type

/**
 * A type abstraction. I.e., a place in the program where type variables may
 * be introduced.
 *
 * Example:
 *
 * ```swift
 * class C<A, B> { }
 * //    ^^^^^^^ a type abstraction
 * ```
 */
abstract class TypeAbstraction extends AstNode {
  abstract TypeParameter getATypeParameter();
}

final class ClassLikeDeclarationTypeAbstraction extends TypeAbstraction instanceof Unified::ClassLikeDeclaration
{
  override TypeParameter getATypeParameter() { this = result.getDeclaringItem() }
}
