/** Provides functionality for inferring types. */

private import codeql.util.Boolean
private import codeql.util.Option
private import codeql.util.Unit
// private import unified
// private import codeql.rust.internal.PathResolution
private import Type
private import Type as T
private import TypeAbstraction
private import TypeAbstraction as TA
// private import Type as T
private import TypeMention
// private import codeql.rust.internal.typeinference.DerefChain
// private import FunctionType
// private import FunctionOverloading as FunctionOverloading
// private import BlanketImplementation as BlanketImplementation
// private import codeql.rust.elements.internal.VariableImpl::Impl as VariableImpl
private import codeql.typeinference.internal.TypeInference
// private import codeql.rust.frameworks.stdlib.Stdlib
// private import codeql.rust.frameworks.stdlib.Builtins as Builtins
// private import codeql.rust.elements.internal.CallExprImpl::Impl as CallExprImpl
private import utils.test.InlineExpectationsTest

class Type = T::Type;

private module Input1 implements InputSig1<Location> {
  private import Type as T

  class Type = T::Type;

  class PseudoType = T::PseudoType;

  class TypeParameter = T::TypeParameter;

  class TypeAbstraction = TA::TypeAbstraction;

  int getTypeParameterId(TypeParameter tp) {
    tp =
      rank[result](TypeParameter tp0, int kind, int id1, int id2 |
        kind = 1 and
        id1 = idOfTypeParameterAstNode(tp0.(TypeParameterType).getTypeParameter()) and
        id2 = 0
        or
        kind = 2 and
        exists(ClassLikeDeclaration c, AssociatedTypeDeclaration a |
          tp0 = TAssociatedTypeParameterType(c, a, _) and
          id1 = idOfTypeParameterAstNode(c) and
          id2 = idOfTypeParameterAstNode(a)
        )
      |
        tp0 order by kind, id1, id2
      )
  }
}

private import Input1

private module M1 = Make1<Location, Input1>;

import M1

predicate getTypePathLimit = Input1::getTypePathLimit/0;

predicate getTypeParameterId = Input1::getTypeParameterId/1;

class TypePath = M1::TypePath;

module TypePath = M1::TypePath;

private module Input2 implements InputSig2<TypeMention> {
  TypeMention getATypeParameterConstraint(TypeParameter tp) {
    result = tp.(TypeParameterType).getTypeParameter().getBound()
  }

  /**
   * Use the constraint mechanism in the shared type inference library to
   * support traits. In Rust `constraint` is always a trait.
   *
   * See the documentation of `conditionSatisfiesConstraint` in the shared type
   * inference module for more information.
   */
  predicate conditionSatisfiesConstraint(
    TypeAbstraction abs, TypeMention condition, TypeMention constraint, boolean transitive
  ) {
    transitive = true and
    abs =
      any(ClassLikeDeclaration c |
        condition = c.getName() and
        constraint = c.getABaseType().getType()
      )
  }

  predicate typeParameterIsFunctionallyDetermined(TypeParameter tp) {
    tp instanceof AssociatedTypeParameterType
  }

  predicate typeAbstractionHasAmbiguousConstraintAt(
    TypeAbstraction abs, Type constraint, TypePath path
  ) {
    none() // todo
  }
}

private import Input2

private module M2 = Make2<TypeMention, Input2>;

import M2

private module Input3 implements InputSig3 {
  private import unified as Unified

  predicate cacheRevRef() { any() }

  predicate inferTypeForDefaults = M3::inferType/2;

  class UnknownType = T::UnknownType;

  class BoolType extends BuiltinType {
    BoolType() { this.getName() = "Bool" }
  }

  class AstNode = Unified::AstNode;

  final class Expr = ExprImpl;

  abstract private class ExprImpl extends AstNode { }

  private class ExprExpr extends ExprImpl, Unified::Expr { }

  // private class ArgListExpr extends ExprImpl, ArgList { }
  class Cast extends Expr, TypeCastExpr {
    TypeMention getType() { result = TypeCastExpr.super.getType() }
  }

  class Switch extends Expr {
    Switch() { none() }

    Expr getExpr() { none() }

    Case getCase(int index) { none() }
  }

  class Case extends AstNode {
    AstNode getAPattern() { none() }

    AstNode getBody() { none() }
  }

  class ConditionalExpr extends Expr instanceof IfExpr {
    Expr getCondition() { result = super.getCondition() }

    Expr getThen() { result = super.getThen() }

    Expr getElse() { result = super.getElse() }
  }

  class BinaryExpr extends Expr, Unified::BinaryExpr {
    Expr getLeftOperand() { result = super.getLeft() }

    Expr getRightOperand() { result = super.getRight() }
  }

  class LogicalAndExpr extends BinaryExpr, Unified::LogicalAndExpr { }

  class LogicalOrExpr extends BinaryExpr, Unified::LogicalOrExpr { }

  final class Assignment = AssignmentImpl;

  abstract private class AssignmentImpl extends BinaryExpr { }

  class AssignExpr extends AssignmentImpl {
    AssignExpr() { none() }
  }

  class ParenExpr extends Expr {
    ParenExpr() { none() }

    Expr getExpr() { none() }
  }

  final class Declaration = DeclarationImpl;

  abstract private class DeclarationImpl extends AstNode {
    abstract TypeMention getDeclaringType();

    abstract TypeMention getType();
  }

  class Variable extends AstNode {
    Variable() { none() }

    AstNode getDefiningNode() { none() }

    Expr getAnAccess() { none() }

    string toString() { result = this.getDefiningNode().toString() }

    Location getLocation() { result = this.getDefiningNode().getLocation() }
  }

  final class VariableDeclaration = VariableDeclarationImpl;

  abstract private class VariableDeclarationImpl extends DeclarationImpl {
    abstract predicate isCoercionSite();

    abstract AstNode getPattern();

    abstract AstNode getInitializer();

    override TypeMention getDeclaringType() { none() }
  }

  final class Field = FieldImpl;

  abstract private class FieldImpl extends DeclarationImpl {
    // no case for variants as those can only be destructured using pattern matching
    // abstract Struct getStruct();
    override TypeMention getDeclaringType() { none() }
  }

  class FieldAccess extends Expr {
    FieldAccess() { none() }

    Expr getReceiver() { none() }

    Field getField() {
      // mutual recursion; resolving fields requires resolving types and vice versa
      none()
    }
  }

  // Type inferFieldAccessReceiverType(FieldAccess fa, TypePath path) {
  //   exists(TypePath path0 | result = inferType(fa.getReceiver(), path0) |
  //     // adjust for implicit deref
  //     path0.isCons(getRefTypeParameter(_), path)
  //     or
  //     not path0.isCons(getRefTypeParameter(_), _) and
  //     not (result instanceof RefType and path0.isEmpty()) and
  //     path = path0
  //   )
  // }
  Type inferFieldAccessReceiverTypeContextual(Expr receiver, TypePath path) {
    result = M3::inferFieldAccessReceiverTypeContextualDefault(_, receiver, path)
  }

  class Return extends ReturnExpr {
    Expr getExpr() { result = this.getValue() }
  }

  final class Parameter = ParameterImpl;

  abstract private class ParameterImpl extends VariableDeclarationImpl {
    override predicate isCoercionSite() { any() } // doesn't really matter, since there are no initializers/default values

    override AstNode getInitializer() { none() }
  }

  final class Parameterizable = ParameterizableImpl;

  abstract private class ParameterizableImpl extends DeclarationImpl {
    abstract TypeParameter getTypeParameter(int pos);

    abstract TypeMention getAdditionalTypeParameterConstraint(TypeParameter tp);

    abstract Parameter getParameter(int i);
  }

  class Callable extends ParameterizableImpl instanceof Unified::Callable {
    override TypeMention getDeclaringType() { none() }

    override TypeParameter getTypeParameter(int pos) { none() }

    override TypeMention getAdditionalTypeParameterConstraint(TypeParameter tp) { none() }

    override Parameter getParameter(int i) { none() }

    override TypeMention getType() { none() }

    AstNode getBody() { none() }
  }

  Callable getEnclosingCallable(AstNode node) { none() }

  class ResolutionContext = Unit;

  final class Invocation = InvocationImpl;

  abstract private class InvocationImpl extends Expr {
    abstract Type getTypeQualifier(TypePath path);

    abstract Type getTypeArgument(int pos, TypePath path);

    abstract Expr getArgument(int i);

    abstract Parameterizable getTarget(ResolutionContext c);

    abstract Parameterizable getATargetForTypeQualifierMatching();
  }

  Type inferInvocationArgumentTypeContextual(Expr arg, TypePath path) {
    result = M3::inferInvocationArgumentTypeContextualDefault(_, _, _, arg, path)
  }

  Type inferInvocationType(Invocation invocation, TypePath path) {
    result = M3::inferInvocationTypeDefault(invocation, _, path)
  }

  // Type inferInvocationTypeContextual(Invocation invocation, TypePath path) {
  //   exists(TypePath path0 |
  //     result = inferType(invocation, path0) and
  //     // index expression `x[i]` desugars to `*x.index(i)`, so we must account for
  //     // the implicit deref
  //     if invocation instanceof IndexExpr or invocation instanceof DerefExpr
  //     then path = TypePath::cons(getRefTypeParameter(_), path0)
  //     else path = path0
  //   )
  // }
  class Closure extends Expr, Callable instanceof Unified::FunctionExpr { }

  class ClosureParameterPseudoType extends T::ClosureParameterPseudoType {
    Parameter getParameter() { result = this.getParam() }
  }

  /**
   * Gets the root type of a closure.
   *
   * We model closures as `dyn Fn` trait object types. A closure might implement
   * only `Fn`, `FnMut`, or `FnOnce`. But since `Fn` is a subtrait of the others,
   * giving closures the type `dyn Fn` works well in practice -- even if not
   * entirely accurate.
   */
  pragma[nomagic]
  private Type closureRootType() { none() }

  bindingset[c]
  Type getClosureType(Closure c) {
    result = closureRootType() and
    exists(c)
  }

  /** Gets the path to a closure's `index`th parameter type, where the arity is `arity`. */
  pragma[nomagic]
  private TypePath closureParameterPath(int arity, int index) {
    none()
    // result =
    //   TypePath::cons(TDynTraitTypeParameter(_, any(FnTrait t).getTypeParam()),
    //     TypePath::singleton(getTupleTypeParameter(arity, index)))
  }

  TypePath getClosureParameterTypePath(Parameter p) {
    exists(FunctionExpr fe, int index |
      p = fe.getParameter(index) and
      result = closureParameterPath(fe.getNumberOfParameters(), index)
    )
  }

  /** Gets the path to a closure's return type. */
  pragma[nomagic]
  private TypePath closureReturnPath() {
    none()
    // result =
    //   TypePath::singleton(TDynTraitTypeParameter(any(FnTrait t), any(FnOnceTrait t).getOutputType()))
  }

  bindingset[c]
  TypePath getClosureReturnTypePath(Closure c) {
    result = closureReturnPath() and
    exists(c)
  }

  predicate stepLanguageSpecific(AstNode n1, TypePath prefix1, AstNode n2, TypePath prefix2) {
    none()
  }

  pragma[nomagic]
  private Type inferUnknownType(AstNode n, TypePath path) { none() }

  pragma[nomagic]
  Type inferTypeLanguageSpecific(AstNode n, TypePath path) { result = inferUnknownType(n, path) }

  pragma[nomagic]
  Type inferTypeCertainLanguageSpecific(AstNode n, TypePath path) { none() }
}

private module M3 = Make3<Input3>;

predicate inferType = M3::inferType/1;

predicate inferType = M3::inferType/2;

predicate inferTypeCertain = M3::inferTypeCertain/2;

module Consistency = M3::Consistency;

module CachedStage = M3::CachedStage;

private predicate typeTestAstNodeRepr(AstNode n, string repr) {
  repr = [n.toString(), n.(Identifier).getValue()]
}

module TypeTest implements TestSig {
  private module M = M3::TypeTest<typeTestAstNodeRepr/2>;

  import M

  predicate hasOptionalResult = M::hasOptionalResult/4;
}

/** Provides predicates for debugging the type inference implementation. */
private module Debug {
  // Locatable getRelevantLocatable() {
  //   exists(string filepath, int startline, int startcolumn, int endline, int endcolumn |
  //     result.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn) and
  //     filepath.matches("%/main.rs") and
  //     startline = 103
  //   )
  // }
  // Type debugInferType(AstNode n, TypePath path) {
  //   n = getRelevantLocatable() and
  //   result = inferType(n, path)
  // }
  // Addressable debugResolveCallTarget(InvocationExpr c, boolean dispatch) {
  //   c = getRelevantLocatable() and
  //   result = resolveCallTarget(c, dispatch)
  // }
  // predicate debugConditionSatisfiesConstraint(
  //   TypeAbstraction abs, TypeMention condition, TypeMention constraint, boolean transitive
  // ) {
  //   abs = getRelevantLocatable() and
  //   Input2::conditionSatisfiesConstraint(abs, condition, constraint, transitive)
  // }
  // predicate debugInferShorthandSelfType(ShorthandSelfParameterMention self, TypePath path, Type t) {
  //   self = getRelevantLocatable() and
  //   t = self.getTypeAt(path)
  // }
  // predicate debugTypeMention(TypeMention tm, TypePath path, Type type) {
  //   tm = getRelevantLocatable() and
  //   tm.getTypeAt(path) = type
  // }
  predicate atLimit = M3::Debug::atLimit/1;

  predicate inferTypeForNodeAtLimit = M3::Debug::inferTypeForNodeAtLimit/2;

  predicate countTypesForNodeAtLimit = M3::Debug::countTypesForNodeAtLimit/2;

  predicate maxTypes = M3::Debug::maxTypes/4;

  predicate maxTypePath = M3::Debug::maxTypePath/4;

  predicate maxTypePaths = M3::Debug::maxTypePaths/4;
  // Type debugInferTypeCertain(AstNode n, TypePath path) {
  //   n = getRelevantLocatable() and
  //   result = inferTypeCertain(n, path)
  // }
  // Type debugInferCertainNonUniqueType(AstNode n, TypePath path) {
  //   n = getRelevantLocatable() and
  //   Consistency::nonUniqueCertainType(n, path) and
  //   result = inferTypeCertain(n, path)
  // }
}
