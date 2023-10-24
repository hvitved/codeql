/**
 * Provides classes and predicates for defining flow summaries.
 */

private import codeql.dataflow.internal.FlowSummaryImpl
private import codeql.dataflow.internal.AccessPathSyntax as AccessPath
private import codeql.ruby.AST
private import codeql.ruby.dataflow.internal.DataFlowImplSpecific as DataFlowImplSpecific
private import DataFlowImplSpecific::Private
private import DataFlowImplSpecific::Public

module Input implements InputSig<DataFlowImplSpecific::RubyDataFlow> {
  class SummarizedCallableBase = string;

  ArgumentPosition callbackSelfParameterPosition() { result.isLambdaSelf() }

  DataFlowType getContentType(ContentSet c) { result = TUnknownDataFlowType() and exists(c) }

  bindingset[c, pos]
  DataFlowType getParameterType(SummarizedCallableBase c, ParameterPosition pos) {
    result = TUnknownDataFlowType() and exists(c) and exists(pos)
  }

  bindingset[c, rk]
  DataFlowType getReturnType(SummarizedCallableBase c, ReturnKind rk) {
    result = TUnknownDataFlowType() and exists(c) and exists(rk)
  }

  bindingset[t, pos]
  DataFlowType getCallbackParameterType(DataFlowType t, ArgumentPosition pos) {
    result = TUnknownDataFlowType() and exists(t) and exists(pos)
  }

  bindingset[t, rk]
  DataFlowType getCallbackReturnType(DataFlowType t, ReturnKind rk) {
    result = TUnknownDataFlowType() and exists(t) and exists(rk)
  }

  ReturnKind getStandardReturnValueKind() { result instanceof NormalReturnKind }

  string encodeParameterPosition(ParameterPosition pos) {
    exists(int i |
      pos.isPositional(i) and
      result = i.toString()
    )
    or
    exists(int i |
      pos.isPositionalLowerBound(i) and
      result = i + ".."
    )
    or
    exists(string name |
      pos.isKeyword(name) and
      result = name + ":"
    )
    or
    pos.isSelf() and
    result = "self"
    or
    pos.isLambdaSelf() and
    result = "lambda-self"
    or
    pos.isBlock() and
    result = "block"
    or
    pos.isAny() and
    result = "any"
    or
    pos.isAnyNamed() and
    result = "any-named"
    or
    pos.isHashSplat() and
    result = "hash-splat"
    or
    pos.isSplat(0) and
    result = "splat"
  }

  string encodeArgumentPosition(ArgumentPosition pos) {
    pos.isSelf() and result = "self"
    or
    pos.isLambdaSelf() and result = "lambda-self"
    or
    pos.isBlock() and result = "block"
    or
    exists(int i |
      pos.isPositional(i) and
      result = i.toString()
    )
    or
    exists(string name |
      pos.isKeyword(name) and
      result = name + ":"
    )
    or
    pos.isAny() and
    result = "any"
    or
    pos.isAnyNamed() and
    result = "any-named"
  }

  string encodeContent(ContentSet cs, string arg) {
    exists(Content c | cs = TSingletonContent(c) |
      c = TFieldContent(arg) and result = "Field"
      or
      exists(ConstantValue cv |
        c = TKnownElementContent(cv) and
        result = "Element" and
        arg = cv.serialize() + "!"
      )
      or
      c = TUnknownElementContent() and result = "Element" and arg = "?"
    )
    or
    cs = TAnyElementContent() and result = "Element" and arg = "any"
    or
    exists(Content::KnownElementContent kec |
      cs = TKnownOrUnknownElementContent(kec) and
      result = "Element" and
      arg = kec.getIndex().serialize()
    )
    or
    exists(int lower, boolean includeUnknown, string unknown |
      cs = TElementLowerBoundContent(lower, includeUnknown) and
      (if includeUnknown = true then unknown = "" else unknown = "!") and
      result = "Element" and
      arg = lower.toString() + ".." + unknown
    )
  }

  string encodeReturn(ReturnKind rk, string arg) {
    not rk = Input::getStandardReturnValueKind() and
    result = "ReturnValue" and
    arg = rk.toString()
  }

  string encodeWithoutContent(ContentSet c, string arg) {
    result = "Without" + encodeContent(c, arg)
  }

  string encodeWithContent(ContentSet c, string arg) { result = "With" + encodeContent(c, arg) }
}

private import Make<DataFlowImplSpecific::RubyDataFlow, Input> as Impl

private module StepsInput implements Impl::Private::StepsInputSig {
  DataFlowType getSyntheticGlobalType(Private::SyntheticGlobal sg) {
    result = TUnknownDataFlowType() and exists(sg)
  }

  DataFlowCall getACall(Public::SummarizedCallable sc) {
    result.asCall().getAstNode() = sc.(LibraryCallable).getACall()
    or
    result.asCall().getAstNode() = sc.(LibraryCallable).getACallSimple()
  }
}

module Private {
  import Impl::Private

  module Steps = Impl::Private::Steps<StepsInput>;
}

module Public = Impl::Public;

module ParsePositions {
  private import Private

  private predicate isParamBody(string body) {
    body = any(AccessPathToken tok).getAnArgument("Parameter")
  }

  private predicate isArgBody(string body) {
    body = any(AccessPathToken tok).getAnArgument("Argument")
  }

  private predicate isElementBody(string body) {
    body = any(AccessPathToken tok).getAnArgument(["Element", "WithElement", "WithoutElement"])
  }

  predicate isParsedParameterPosition(string c, int i) {
    isParamBody(c) and
    i = AccessPath::parseInt(c)
  }

  predicate isParsedArgumentPosition(string c, int i) {
    isArgBody(c) and
    i = AccessPath::parseInt(c)
  }

  predicate isParsedArgumentLowerBoundPosition(string c, int i) {
    isArgBody(c) and
    i = AccessPath::parseLowerBound(c)
  }

  predicate isParsedKeywordParameterPosition(string c, string paramName) {
    isParamBody(c) and
    c = paramName + ":"
  }

  predicate isParsedKeywordArgumentPosition(string c, string paramName) {
    isArgBody(c) and
    c = paramName + ":"
  }

  bindingset[arg]
  private string adjustElementArgument(string arg, boolean includeUnknown) {
    result = arg.regexpCapture("(.*)!", 1) and
    includeUnknown = false
    or
    result = arg and
    not arg.matches("%!") and
    includeUnknown = true
  }

  predicate isParsedElementLowerBoundPosition(string c, boolean includeUnknown, int lower) {
    isElementBody(c) and
    lower = AccessPath::parseLowerBound(adjustElementArgument(c, includeUnknown))
  }
}
