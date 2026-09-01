private import unified as Unified
private import Type
private import TypeInference
private import codeql.unified.internal.StaticNameBinding
private import codeql.unified.internal.ExprPositions

abstract class TypeMention extends AstNode {
  pragma[nomagic]
  abstract Type getTypeAt(TypePath path);

  final Type getType() { result = this.getTypeAt(TypePath::nil()) }
}

class ExprTypeMention extends TypeMention, Expr {
  ExprTypeMention() { isInTypeContext(this) }

  private Type getRootType0() {
    exists(NameBinding b | b = getStaticBindingTarget(this) |
      b = result.(ClassLikeDeclarationType).getClassLikeDeclaration().getNameNode()
      or
      b = result.(TypeParameterType).getTypeParameter().getNameNode()
    )
    or
    this instanceof FunctionExpr and
    result instanceof FunctionType
    or
    result.(TupleType).getArity() = this.(TupleExpr).getNumberOfElements()
  }

  Type getRootType() {
    result = this.getRootType0()
    or
    not exists(this.getRootType0()) and
    result instanceof UnknownType
  }

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
        alias.getName() = name and
        path = TypePath::cons(baseTp, suffix) and
        result = alias.getType().(TypeMention).getTypeAt(suffix)
      )
    )
    or
    this =
      any(FunctionExpr fe |
        exists(TupleType tt | tt.getArity() = fe.getNumberOfParameters() |
          result = tt and
          path = TypePath::singleton(getFunctionArgsTypeParameter())
          or
          exists(TypePath suffix, int i |
            result = fe.getParameter(i).getType().(TypeMention).getTypeAt(suffix) and
            path =
              TypePath::cons(getFunctionArgsTypeParameter(),
                TypePath::cons(tt.getPositionalTypeParameter(i), suffix))
          )
        )
        or
        exists(TypePath suffix |
          result = fe.getReturnType().(TypeMention).getTypeAt(suffix) and
          path = TypePath::cons(getFunctionReturnTypeParameter(), suffix)
        )
      )
    or
    this =
      any(TupleExpr te |
        exists(TupleType tt, int i, TypePath suffix |
          tt.getArity() = te.getNumberOfElements() and
          result = te.getElement(i).getValue().(TypeMention).getTypeAt(suffix) and
          path = TypePath::cons(tt.getPositionalTypeParameter(i), suffix)
        )
      )
  }
}

class GenericTypeExprTypeMention extends ExprTypeMention, GenericTypeExpr {
  override Type getTypeAt(TypePath path) {
    exists(ExprTypeMention base | base = this.getBase() |
      result = base.getRootType() and
      path.isEmpty()
      or
      exists(Type root, int i, TypeParameter tp, TypePath suffix |
        root = base.getRootType() and
        tp = root.getPositionalTypeParameter(i) and
        result = this.getTypeArgument(i).(TypeMention).getTypeAt(suffix) and
        path = TypePath::cons(tp, suffix)
      )
    )
  }
}

/** A class declaration mentions itself. */
class ClassLikeDeclarationTypeMention extends TypeMention, Identifier {
  private ClassLikeDeclaration c;

  ClassLikeDeclarationTypeMention() { this = c.getNameNode() }

  ClassLikeDeclarationType getRootType() { c = result.getClassLikeDeclaration() }

  ClassLikeDeclaration getClassLikeDeclaration() { result = c }

  override Type getTypeAt(TypePath path) {
    result = this.getRootType() and
    path.isEmpty()
    or
    result =
      any(TypeParameter tp |
        c = tp.getDeclaringItem() and
        path = TypePath::singleton(tp)
      )
  }
}

TypeMention getClassLikeDeclarationTypeMention(ClassLikeDeclaration c) {
  result = c.getNameNode()
  or
  result = c.getExtensionTarget()
}
