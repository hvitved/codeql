private import unified as Unified
private import Type
private import TypeInference
private import codeql.unified.internal.StaticNameBinding

abstract class TypeMention extends AstNode {
  pragma[nomagic]
  abstract Type getTypeAt(TypePath path);

  final Type getType() { result = this.getTypeAt(TypePath::nil()) }
}

class NamedTypeExprTypeMention extends TypeMention, NamedTypeExpr {
  private Type t;

  NamedTypeExprTypeMention() {
    exists(NameDeclaration decl | decl = getStaticBindingTarget(this.getName()) |
      decl = t.(ClassLikeDeclarationType).getClassLikeDeclaration().getName()
      or
      decl = t.(TypeParameterType).getTypeParameter().getName()
    )
  }

  Type getRootType() { result = t }

  override Type getTypeAt(TypePath path) {
    result = this.getRootType() and
    path.isEmpty()
    or
    exists(
      ClassLikeDeclaration c, AssociatedTypeDeclaration a, ClassLikeDeclaration base,
      AssociatedTypeParameterType baseTp, string name
    |
      // protocol Base {
      //   associatedtype BaseTp
      // }
      associatedTypeParameterInherited(c, a, base, this, name) and
      baseTp = TAssociatedTypeParameterType(base, a, _)
    |
      // protocol Sub : Base {
      //                ^^^^
      // }
      path = TypePath::singleton(baseTp) and
      result = TAssociatedTypeParameterType(c, a, _)
      or
      // struct S : Base {
      //            ^^^^
      //   typealias BaseTp = String
      // }
      exists(TypeAliasDeclaration alias, TypePath suffix |
        alias = c.getAMember() and
        alias.getName().getValue() = name and
        path = TypePath::cons(baseTp, suffix) and
        result = alias.getType().(TypeMention).getTypeAt(suffix)
      )
    )
  }
}

class GenericTypeExprTypeMention extends TypeMention, GenericTypeExpr {
  private NamedTypeExprTypeMention base;

  GenericTypeExprTypeMention() { base = this.getBase() }

  override Type getTypeAt(TypePath path) {
    result = base.getRootType() and
    path.isEmpty()
    or
    exists(ClassLikeDeclarationType c, int i, TypeParameter tp, TypePath suffix |
      c = base.getRootType() and
      tp = c.getPositionalTypeParameter(i) and
      result = this.getTypeArgument(i).(TypeMention).getTypeAt(suffix) and
      path = TypePath::cons(tp, suffix)
    )
  }
}

class ClassLikeDeclarationTypeMention extends TypeMention, Identifier {
  private ClassLikeDeclaration c;

  ClassLikeDeclarationTypeMention() { this = c.getName() }

  ClassLikeDeclarationType getRootType() { c = result.getClassLikeDeclaration() }

  override Type getTypeAt(TypePath path) {
    result = this.getRootType() and
    path.isEmpty()
    or
    result =
      any(TypeParameter tp |
        this = tp.getDeclaringItem() and
        path = TypePath::singleton(tp)
      )
  }
}
