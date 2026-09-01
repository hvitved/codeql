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
private import codeql.unified.internal.NameBinding

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
        or
        kind = 3 and
        tp0 = TUnknownTypeTypeParameter(id1) and
        id2 = 0
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
        condition = c.getNameNode() and
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

  predicate cacheRevRef() { exists(resolveCallTarget(_)) implies any() }

  predicate inferTypeForDefaults = M3::inferType/2;

  class UnknownType = T::UnknownType;

  class BoolType extends BuiltinType {
    BoolType() { this.getName() = "Bool" }
  }

  class AstNode = Unified::AstNode;

  final class Expr = ExprImpl;

  abstract private class ExprImpl extends AstNode { }

  private class ExprExpr extends ExprImpl, Unified::Expr { }

  class Cast extends Expr, TypeCastExpr {
    TypeMention getType() { result = TypeCastExpr.super.getType() }
  }

  class Switch extends Expr, SwitchExpr {
    Expr getExpr() { result = super.getValue() }

    Case getCase(int index) { result = super.getCase(index) }
  }

  class Case extends SwitchCase {
    AstNode getAPattern() { result = super.getPattern() }

    AstNode getBody() { result = super.getBody() }
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
    AssignExpr() { this.getOperator().getValue() = "=" } // todo
  }

  class ParenExpr extends Expr {
    ParenExpr() { none() }

    Expr getExpr() { none() }
  }

  /** Provides declarations with explicit AST node representations. */
  private module AstDeclaration {
    abstract class Declaration extends AstNode {
      abstract TypeMention getDeclaringType();

      abstract TypeMention getType();

      abstract Identifier getNameNode();

      pragma[nomagic]
      predicate isMember(Identifier i, ClassLikeDeclaration cls, string name) {
        exists(NamespaceNode ns |
          ns.isInstanceMemberNamespace(cls) and
          ns.getMember(name).isIdentifier(i) and
          i = this.getNameNode()
        )
      }
    }

    abstract class VariableDeclaration extends Declaration {
      abstract AstNode getPattern();

      abstract AstNode getInitializer();

      predicate isCoercionSite() { none() }

      override TypeMention getDeclaringType() { none() }
    }

    private class OrdinaryVariableDeclaration extends VariableDeclaration instanceof Unified::VariableDeclaration
    {
      override AstNode getPattern() { result = Unified::VariableDeclaration.super.getPattern() }

      override AstNode getInitializer() { result = super.getValue() }

      override TypeMention getType() { result = Unified::VariableDeclaration.super.getType() }

      override Identifier getNameNode() { none() }
    }

    class Field extends OrdinaryVariableDeclaration {
      ClassLikeDeclaration cls;

      Field() { this = cls.getAMember() }

      override TypeMention getDeclaringType() { result = getClassLikeDeclarationTypeMention(cls) }
    }

    class Parameter extends VariableDeclaration instanceof Unified::Parameter {
      override AstNode getInitializer() { none() }

      override AstNode getPattern() { result = Unified::Parameter.super.getPattern() }

      override TypeMention getType() { result = Unified::Parameter.super.getType() }

      override Identifier getNameNode() { none() }
    }

    abstract class Callable extends Declaration instanceof Unified::Callable {
      TypeMention getAdditionalTypeParameterConstraint(TypeParameter tp) { none() }

      abstract TypeParameter getTypeParameter(int pos);

      abstract Parameter getParameter(int i);

      abstract AstNode getBody();
    }

    private class FunctionDeclarationCallable extends Callable instanceof FunctionDeclaration {
      override ClassLikeDeclarationTypeMention getDeclaringType() {
        this = result.getClassLikeDeclaration().getAMember()
      }

      override TypeParameterType getTypeParameter(int pos) {
        result.getTypeParameter() = this.(FunctionDeclaration).getTypeParameter(pos)
      }

      override Parameter getParameter(int i) { result = FunctionDeclaration.super.getParameter(i) }

      override TypeMention getType() { result = super.getReturnType() }

      override AstNode getBody() { result = FunctionDeclaration.super.getBody() }

      override Identifier getNameNode() { result = FunctionDeclaration.super.getNameNode() }
    }

    class ClosureImpl extends Expr, Callable instanceof Unified::FunctionExpr {
      override ClassLikeDeclarationTypeMention getDeclaringType() { none() }

      override TypeParameterType getTypeParameter(int pos) { none() }

      override Parameter getParameter(int i) { result = FunctionExpr.super.getParameter(i) }

      override TypeMention getType() { result = super.getReturnType() }

      override AstNode getBody() { result = FunctionExpr.super.getBody() }

      override Identifier getNameNode() { none() }
    }
  }

  private newtype TDeclaration =
    TExplicitDeclaration(AstDeclaration::Declaration decl) or
    TImplicitParameterDeclaration(LocalVariable v) { v.isImplicitReceiverParameter(_) }

  final class Declaration = DeclarationImpl;

  abstract private class DeclarationImpl extends TDeclaration {
    abstract TypeMention getDeclaringType();

    abstract TypeMention getType();

    abstract Identifier getNameNode();

    abstract string toString();

    abstract Location getLocation();
  }

  additional class ExplicitDeclarationImpl extends DeclarationImpl, TExplicitDeclaration {
    AstDeclaration::Declaration decl;

    ExplicitDeclarationImpl() { this = TExplicitDeclaration(decl) }

    AstDeclaration::Declaration getAstNode() { result = decl }

    override TypeMention getDeclaringType() { result = decl.getDeclaringType() }

    override TypeMention getType() { result = decl.getType() }

    override Identifier getNameNode() { result = decl.getNameNode() }

    override string toString() { result = decl.toString() }

    override Location getLocation() { result = decl.getLocation() }
  }

  class Variable extends LocalNameBindingOutput::Local {
    // Variable() { none() }
    private AstNode getDefiningNode2() { result = this.getDefiningNode() }

    Expr getAnAccess() { result = super.getAnAccess() }
    // string toString() { result = this.getDefiningNode().toString() }
    // Location getLocation() { result = this.getDefiningNode().getLocation() }
  }

  final class VariableDeclaration = VariableDeclarationImpl;

  abstract private class VariableDeclarationImpl extends DeclarationImpl {
    abstract AstNode getPattern();

    abstract AstNode getInitializer();

    predicate preservesInitializerType() { any() }
  }

  private class ExplicitVariableDeclarationImpl extends VariableDeclarationImpl,
    ExplicitDeclarationImpl
  {
    override AstDeclaration::VariableDeclaration decl;

    override AstNode getPattern() { result = decl.getPattern() }

    override AstNode getInitializer() { result = decl.getInitializer() }
  }

  class Field extends ExplicitDeclarationImpl {
    override AstDeclaration::Field decl;
  }

  class FieldAccess extends Expr {
    FieldAccess() { none() }

    Expr getReceiver() { none() }

    Field getField() {
      // mutual recursion; resolving fields requires resolving types and vice versa
      result.getNameNode() = lookupMember(this)
    }
  }

  Type inferFieldAccessReceiverTypeContextual(Expr receiver, TypePath path) {
    result = M3::inferFieldAccessReceiverTypeContextualDefault(_, receiver, path)
  }

  class Return extends ReturnExpr {
    Expr getExpr() { result = this.getValue() }
  }

  final class Parameter = ParameterImpl;

  abstract private class ParameterImpl extends VariableDeclarationImpl { }

  private class ExplicitParameterImpl extends ParameterImpl, ExplicitDeclarationImpl {
    override AstDeclaration::Parameter decl;

    override AstNode getPattern() { result = decl.getPattern() }

    override AstNode getInitializer() { result = decl.getInitializer() }
  }

  private class ImplicitParameterDeclarationImpl extends ParameterImpl,
    TImplicitParameterDeclaration
  {
    LocalVariable v;

    ImplicitParameterDeclarationImpl() { this = TImplicitParameterDeclaration(v) }

    LocalVariable getVariable() { result = v }

    override AstNode getPattern() { none() }

    override AstNode getInitializer() { none() }

    override TypeMention getDeclaringType() { none() }

    override TypeMention getType() {
      result = getClassLikeDeclarationTypeMention(v.getDeclaringCallable().getEnclosingClass())
    }

    override Identifier getNameNode() { none() }

    override string toString() { result = v.toString() }

    override Location getLocation() { result = v.getLocation() }
  }

  predicate implicitParameterDecl(Parameter p, Variable v) {
    v = p.(ImplicitParameterDeclarationImpl).getVariable()
  }

  class Callable extends ExplicitDeclarationImpl {
    override AstDeclaration::Callable decl;

    TypeParameter getTypeParameter(int pos) { result = decl.getTypeParameter(pos) }

    TypeMention getAdditionalTypeParameterConstraint(TypeParameter tp) {
      result = decl.getAdditionalTypeParameterConstraint(tp)
    }

    Parameter getParameter(int i) {
      result = TExplicitDeclaration(decl.getParameter(i - 1))
      or
      i = 0 and
      exists(LocalVariable v |
        result = TImplicitParameterDeclaration(v) and
        v.isImplicitReceiverParameter(decl)
      )
    }

    AstNode getBody() { result = decl.getBody() }
  }

  Callable getEnclosingCallable(AstNode node) {
    result = TExplicitDeclaration(node.getEnclosingCallable())
  }

  class InvocationResolutionContext = Unit;

  final class Invocation = InvocationImpl;

  abstract private class InvocationImpl extends Expr {
    abstract Type getTypeQualifier(TypePath path);

    abstract Type getTypeArgument(int pos, TypePath path);

    abstract Expr getArgument(int i);

    abstract Callable getTarget(InvocationResolutionContext c);

    abstract Callable getATargetForTypeQualifierMatching();
  }

  private class CallExprInvocation extends InvocationImpl instanceof CallExpr {
    Type getImplicitReceiverType(TypePath path) {
      exists(ImplicitParameterDeclarationImpl p, LocalVariable v |
        v = super.getCallee().(UnqualifiedMemberAccess).getImplicitQualifierVariable() and
        v = p.getVariable() and
        result = p.getType().getTypeAt(path)
      )
    }

    override Type getTypeQualifier(TypePath path) {
      result = super.getCallee().(TypeMention).getTypeAt(path)
    }

    override Type getTypeArgument(int pos, TypePath path) { none() }

    override Expr getArgument(int i) {
      i = 0 and
      result = CallExpr.super.getCallee().(MemberAccessExpr).getBase()
      or
      result = CallExpr.super.getArgument(i - 1).getValue()
    }

    override Callable getTarget(InvocationResolutionContext c) {
      result.getNameNode() = resolveCallTarget(this) and
      exists(c)
    }

    override Callable getATargetForTypeQualifierMatching() { none() }
  }

  Type inferInvocationArgumentType(
    Invocation invocation, InvocationResolutionContext ctx, int i, TypePath path
  ) {
    exists(ctx) and
    (
      result = inferType(invocation.getArgument(i), path)
      or
      i = 0 and
      result = invocation.(CallExprInvocation).getImplicitReceiverType(path)
    )
  }

  Type inferInvocationArgumentTypeContextual(Expr arg, TypePath path) {
    result = M3::inferInvocationArgumentTypeContextualDefault(_, _, _, arg, path)
  }

  Type inferInvocationType(Invocation invocation, TypePath path) {
    result = M3::inferInvocationTypeDefault(invocation, _, path)
  }

  class Closure extends Callable, ExplicitDeclarationImpl {
    override AstDeclaration::ClosureImpl decl;

    Expr getDefiningExpr() { result = decl }
  }

  class ClosureParameterPseudoType extends T::ClosureParameterPseudoType {
    Parameter getParameter() { result = TExplicitDeclaration(this.getParam()) }
  }

  pragma[nomagic]
  private Type closureRootType() { result instanceof FunctionType }

  bindingset[c]
  Type getClosureType(Closure c) {
    result = closureRootType() and
    exists(c)
  }

  /** Gets the path to a closure's `index`th parameter type, where the arity is `arity`. */
  pragma[nomagic]
  private TypePath closureParameterPath(int arity, int index) {
    result =
      TypePath::cons(getFunctionArgsTypeParameter(),
        TypePath::singleton(getTupleTypeParameter(arity, index)))
  }

  TypePath getClosureParameterTypePath(Parameter p) {
    exists(FunctionExpr fe, int index |
      p = TExplicitDeclaration(fe.getParameter(index)) and
      result = closureParameterPath(fe.getNumberOfParameters(), index)
    )
  }

  pragma[nomagic]
  private TypePath closureReturnPath() {
    result = TypePath::singleton(getFunctionReturnTypeParameter())
  }

  bindingset[c]
  TypePath getClosureReturnTypePath(Closure c) {
    result = closureReturnPath() and
    exists(c)
  }

  predicate stepLanguageSpecific(AstNode n1, TypePath prefix1, AstNode n2, TypePath prefix2) {
    none()
  }

  Type inferTypeLanguageSpecific(AstNode n, TypePath path) { none() }

  pragma[nomagic]
  Type inferTypeCertainLanguageSpecific(AstNode n, TypePath path) { none() }
}

private module M3 = Make3<Input3>;

predicate inferType = M3::inferType/1;

predicate inferType = M3::inferType/2;

predicate inferTypeCertain = M3::inferTypeCertain/2;

module Consistency = M3::Consistency;

module CachedStage = M3::CachedStage;

pragma[nomagic]
private predicate lookupMember0(MemberAccessExpr mae, ClassLikeDeclaration cls, string name) {
  cls = inferType(mae.getBase()).(ClassLikeDeclarationType).getClassLikeDeclaration() and
  name = mae.getMemberName()
}

cached
NameBinding lookupMember(MemberAccessExpr mae) {
  exists(ClassLikeDeclaration cls, Input3::ExplicitDeclarationImpl decl, string name |
    lookupMember0(mae, cls, name) and
    decl.getAstNode().isMember(result, cls, name)
  )
}

NameBinding resolveCallTarget(CallExpr ce) {
  result = getStaticBindingTarget(ce.getCallee())
  or
  result = lookupMember(ce.getCallee())
}

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
