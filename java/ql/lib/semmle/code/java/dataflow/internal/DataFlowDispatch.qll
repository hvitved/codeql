private import java
private import DataFlowPrivate
private import DataFlowUtil
private import semmle.code.java.dataflow.InstanceAccess
private import semmle.code.java.dataflow.internal.FlowSummaryImpl as Impl
private import semmle.code.java.dispatch.VirtualDispatch as VirtualDispatch
private import semmle.code.java.dataflow.TypeFlow
private import semmle.code.java.dispatch.internal.Unification

private module DispatchImpl {
  private predicate hasHighConfidenceTarget(Call c) {
    exists(Impl::Public::SummarizedCallable sc | sc.getACall() = c and not sc.applyGeneratedModel())
    or
    exists(Impl::Public::NeutralSummaryCallable nc | nc.getACall() = c and nc.hasManualModel())
    or
    exists(Callable srcTgt |
      srcTgt = VirtualDispatch::viableCallable(c) and
      not VirtualDispatch::lowConfidenceDispatchTarget(c, srcTgt)
    )
  }

  private Callable sourceDispatch(Call c) {
    result = VirtualDispatch::viableCallable(c) and
    if VirtualDispatch::lowConfidenceDispatchTarget(c, result)
    then not hasHighConfidenceTarget(c)
    else any()
  }

  /** Gets a viable implementation of the target of the given `Call`. */
  DataFlowCallable viableCallable(DataFlowCall c) {
    result.asCallable() = sourceDispatch(c.asCall())
    or
    result.asSummarizedCallable().getACall() = c.asCall()
  }

  private DataFlowCallable testviableCallable(DataFlowCall c) {
    result = viableCallable(c) and
    result.asCallable().hasName("_getMember")
  }

  private DataFlowCallable viableCallable(DataFlowCall c, int k) {
    result = viableCallable(c) and
    k = strictcount(viableCallable(c))
  }

  /**
   * Holds if the set of viable implementations that can be called by `ma`
   * might be improved by knowing the call context. This is the case if the
   * qualifier is the `i`th parameter of the enclosing callable `c`.
   */
  private predicate mayBenefitFromCallContext(MethodCall ma, Callable c, int i) {
    exists(Parameter p |
      2 <= strictcount(sourceDispatch(ma)) and
      ma.getQualifier().(VarAccess).getVariable() = p and
      p.getPosition() = i and
      c.getAParameter() = p and
      not p.isVarargs() and
      c = ma.getEnclosingCallable()
    )
    or
    exists(OwnInstanceAccess ia |
      2 <= strictcount(sourceDispatch(ma)) and
      (ia.isExplicit(ma.getQualifier()) or ia.isImplicitMethodQualifier(ma)) and
      i = -1 and
      c = ma.getEnclosingCallable()
    )
  }

  /**
   * Holds if the call `ctx` might act as a context that improves the set of
   * dispatch targets of a `MethodCall` that occurs in a viable target of
   * `ctx`.
   */
  pragma[nomagic]
  private predicate relevantContext(Call ctx, int i) {
    exists(Callable c |
      mayBenefitFromCallContext(_, c, i) and
      c = sourceDispatch(ctx)
    )
  }

  private RefType getPreciseType(Expr e) {
    result = e.(FunctionalExpr).getConstructedType()
    or
    not e instanceof FunctionalExpr and result = e.getType()
  }

  /**
   * Holds if the `i`th argument of `ctx` has type `t` and `ctx` is a
   * relevant call context.
   */
  private predicate contextArgHasType(Call ctx, int i, RefType t, boolean exact) {
    relevantContext(ctx, i) and
    exists(RefType srctype |
      exists(Expr arg |
        i = -1 and
        ctx.getQualifier() = arg
        or
        ctx.getArgument(i) = arg
      |
        exprTypeFlow(arg, srctype, exact)
        or
        not exprTypeFlow(arg, _, _) and
        exprUnionTypeFlow(arg, srctype, exact)
        or
        not exprTypeFlow(arg, _, _) and
        not exprUnionTypeFlow(arg, _, _) and
        srctype = getPreciseType(arg) and
        if arg instanceof ClassInstanceExpr then exact = true else exact = false
      )
      or
      exists(Node arg |
        i = -1 and
        not exists(ctx.getQualifier()) and
        getInstanceArgument(ctx) = arg and
        arg.getTypeBound() = srctype and
        if ctx instanceof ClassInstanceExpr then exact = true else exact = false
      )
    |
      t = srctype.(BoundedType).getAnUltimateUpperBoundType()
      or
      t = srctype and not srctype instanceof BoundedType
    )
  }

  /**
   * Holds if the set of viable implementations that can be called by `call`
   * might be improved by knowing the call context. This is the case if the
   * qualifier is a parameter of the enclosing callable of `call`.
   */
  predicate mayBenefitFromCallContext(DataFlowCall call) {
    mayBenefitFromCallContext(call.asCall(), _, _)
  }

  private DataFlowCallable testviableImplInCallContext(DataFlowCall call, DataFlowCall ctx) {
    result = viableImplInCallContext(call, ctx) and
    call.toString() = "getClassName(...)"
  }

  pragma[nomagic]
  private predicate foo(DataFlowCall call, DataFlowCall ctx1, DataFlowCall ctx2) {
    forex(DataFlowCallable c | c = viableImplInCallContext(call, ctx1) |
      c = viableImplInCallContext(call, ctx2)
    )
  }

  private DataFlowCallable testviableImplInCallContext(
    DataFlowCall call, DataFlowCall ctx1, DataFlowCall ctx2
  ) {
    result = viableImplInCallContext(call, ctx1) and
    foo(call, ctx1, ctx2) and
    foo(call, ctx2, ctx1)
  }

  /**
   * Gets a viable dispatch target of `call` in the context `ctx`. This is
   * restricted to those `call`s for which a context might make a difference.
   */
  DataFlowCallable viableImplInCallContext(DataFlowCall call, DataFlowCall ctx) {
    result = viableCallable(call) and
    exists(int i, Callable c, Method def, RefType t, boolean exact, MethodCall ma |
      ma = call.asCall() and
      mayBenefitFromCallContext(ma, c, i) and
      c = viableCallable(ctx).asCallable() and
      contextArgHasType(ctx.asCall(), i, t, exact) and
      ma.getMethod().getSourceDeclaration() = def
    |
      exact = true and
      result.asCallable() = VirtualDispatch::exactMethodImpl(def, t.getSourceDeclaration())
      or
      exact = false and
      exists(RefType t2 |
        result.asCallable() = VirtualDispatch::viableMethodImpl(def, t.getSourceDeclaration(), t2) and
        not Unification::failsUnification(t, t2)
      )
      or
      result.asSummarizedCallable().getACall() = ma
    )
  }

  private predicate unificationTargetLeft(ParameterizedType t1) { contextArgHasType(_, _, t1, _) }

  private predicate unificationTargetRight(ParameterizedType t2) {
    exists(VirtualDispatch::viableMethodImpl(_, _, t2))
  }

  private module Unification = MkUnification<unificationTargetLeft/1, unificationTargetRight/1>;

  private int parameterPosition() { result in [-1, any(Parameter p).getPosition()] }

  /** A parameter position represented by an integer. */
  class ParameterPosition extends int {
    ParameterPosition() { this = parameterPosition() }
  }

  /** An argument position represented by an integer. */
  class ArgumentPosition extends int {
    ArgumentPosition() { this = parameterPosition() }
  }

  /** Holds if arguments at position `apos` match parameters at position `ppos`. */
  pragma[inline]
  predicate parameterMatch(ParameterPosition ppos, ArgumentPosition apos) { ppos = apos }
}

import DispatchImpl
