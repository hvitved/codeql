/** Provides classes and predicates for defining flow summaries. */

import codeql.ruby.AST
private import codeql.ruby.CFG
private import codeql.ruby.typetracking.TypeTracker
import codeql.ruby.DataFlow
private import internal.FlowSummaryImpl as Impl
private import internal.DataFlowDispatch
private import internal.DataFlowImplCommon as DataFlowImplCommon
private import internal.DataFlowPrivate

// import all instances below
private module Summaries {
  private import codeql.ruby.Frameworks
  private import codeql.ruby.frameworks.data.ModelsAsData
}

deprecated class SummaryComponent = Impl::Private::SummaryComponent;

/**
 * DEPRECATED.
 *
 * Provides predicates for constructing summary components.
 */
deprecated module SummaryComponent {
  private import Impl::Private::SummaryComponent as SC

  deprecated predicate parameter = SC::parameter/1;

  deprecated predicate argument = SC::argument/1;

  deprecated predicate content = SC::content/1;

  deprecated predicate withoutContent = SC::withoutContent/1;

  deprecated predicate withContent = SC::withContent/1;

  deprecated class SyntheticGlobal = Impl::Private::SyntheticGlobal;

  /** Gets a summary component that represents a receiver. */
  deprecated SummaryComponent receiver() {
    result = argument(any(ParameterPosition pos | pos.isSelf()))
  }

  /** Gets a summary component that represents a block argument. */
  deprecated SummaryComponent block() {
    result = argument(any(ParameterPosition pos | pos.isBlock()))
  }

  /** Gets a summary component that represents an element in a collection at an unknown index. */
  deprecated SummaryComponent elementUnknown() {
    result = SC::content(TSingletonContent(TUnknownElementContent()))
  }

  /** Gets a summary component that represents an element in a collection at a known index. */
  deprecated SummaryComponent elementKnown(ConstantValue cv) {
    result = SC::content(TSingletonContent(DataFlow::Content::getElementContent(cv)))
  }

  /**
   * Gets a summary component that represents an element in a collection at a specific
   * known index `cv`, or an unknown index.
   */
  deprecated SummaryComponent elementKnownOrUnknown(ConstantValue cv) {
    result = SC::content(TKnownOrUnknownElementContent(TKnownElementContent(cv)))
    or
    not exists(TKnownElementContent(cv)) and
    result = elementUnknown()
  }

  /**
   * Gets a summary component that represents an element in a collection at either an unknown
   * index or known index. This has the same semantics as
   *
   * ```ql
   * elementKnown() or elementUnknown(_)
   * ```
   *
   * but is more efficient, because it is represented by a single value.
   */
  deprecated SummaryComponent elementAny() { result = SC::content(TAnyElementContent()) }

  /**
   * Gets a summary component that represents an element in a collection at known
   * integer index `lower` or above.
   */
  deprecated SummaryComponent elementLowerBound(int lower) {
    result = SC::content(TElementLowerBoundContent(lower, false))
  }

  /**
   * Gets a summary component that represents an element in a collection at known
   * integer index `lower` or above, or possibly at an unknown index.
   */
  deprecated SummaryComponent elementLowerBoundOrUnknown(int lower) {
    result = SC::content(TElementLowerBoundContent(lower, true))
  }

  /** Gets a summary component that represents the return value of a call. */
  deprecated SummaryComponent return() { result = SC::return(any(NormalReturnKind rk)) }
}

deprecated class SummaryComponentStack = Impl::Private::SummaryComponentStack;

/**
 * DEPRECATED.
 *
 * Provides predicates for constructing stacks of summary components.
 */
deprecated module SummaryComponentStack {
  private import Impl::Private::SummaryComponentStack as SCS

  deprecated predicate singleton = SCS::singleton/1;

  deprecated predicate push = SCS::push/2;

  deprecated predicate argument = SCS::argument/1;

  /** Gets a singleton stack representing a receiver. */
  deprecated SummaryComponentStack receiver() { result = singleton(SummaryComponent::receiver()) }

  /** Gets a singleton stack representing a block argument. */
  deprecated SummaryComponentStack block() { result = singleton(SummaryComponent::block()) }

  /** Gets a singleton stack representing the return value of a call. */
  deprecated SummaryComponentStack return() { result = singleton(SummaryComponent::return()) }
}

/** A callable with a flow summary, identified by a unique string. */
abstract class SummarizedCallable extends LibraryCallable, Impl::Public::SummarizedCallable {
  bindingset[this]
  SummarizedCallable() { any() }

  /**
   * DEPRECATED: Use `propagatesFlow` instead.
   */
  pragma[nomagic]
  deprecated predicate propagatesFlowExt(string input, string output, boolean preservesValue) {
    none()
  }

  /**
   * Gets the synthesized parameter that results from an input specification
   * that starts with `Argument[s]` for this library callable.
   */
  DataFlow::ParameterNode getParameter(string s) {
    exists(ParameterPosition pos |
      DataFlowImplCommon::parameterNode(result, TLibraryCallable(this), pos) and
      s = Impl::Input::encodeParameterPosition(pos)
    )
  }
}

/**
 * A callable with a flow summary, identified by a unique string, where all
 * calls to a method with the same name are considered relevant.
 */
abstract class SimpleSummarizedCallable extends SummarizedCallable {
  MethodCall mc;

  bindingset[this]
  SimpleSummarizedCallable() { mc.getMethodName() = this }

  final override MethodCall getACallSimple() { result = mc }
}

deprecated class RequiredSummaryComponentStack = Impl::Private::RequiredSummaryComponentStack;

/**
 * Provides a set of special flow summaries to ensure that callbacks passed into
 * library methods will be passed as `lambda-self` arguments into themselves. That is,
 * we are assuming that callbacks passed into library methods will be called, which is
 * needed for flow through captured variables.
 */
private module LibraryCallbackSummaries {
  private predicate libraryCall(CfgNodes::ExprNodes::CallCfgNode call) {
    not exists(getTarget(call))
  }

  private DataFlow::LocalSourceNode trackLambdaCreation(TypeTracker t) {
    t.start() and
    lambdaCreation(result, TLambdaCallKind(), _)
    or
    exists(TypeTracker t2 | result = trackLambdaCreation(t2).track(t2, t)) and
    not result instanceof DataFlow::SelfParameterNode
  }

  private predicate libraryCallHasLambdaArg(CfgNodes::ExprNodes::CallCfgNode call, int i) {
    exists(CfgNodes::ExprCfgNode arg |
      arg = call.getArgument(i) and
      arg = trackLambdaCreation(TypeTracker::end()).getALocalUse().asExpr() and
      libraryCall(call) and
      not arg instanceof CfgNodes::ExprNodes::BlockArgumentCfgNode
    )
  }

  private class LibraryLambdaMethod extends SummarizedCallable {
    LibraryLambdaMethod() { this = "<library method accepting a callback>" }

    final override MethodCall getACall() {
      libraryCall(result.getAControlFlowNode()) and
      result.hasBlock()
      or
      libraryCallHasLambdaArg(result.getAControlFlowNode(), _)
    }

    override predicate propagatesFlow(string input, string output, boolean preservesValue) {
      (
        input = "Argument[block]" and
        output = "Argument[block].Parameter[lambda-self]"
        or
        exists(int i |
          i in [0 .. 10] and
          input = "Argument[" + i + "]" and
          output = "Argument[" + i + "].Parameter[lambda-self]"
        )
      ) and
      preservesValue = true
    }
  }
}
