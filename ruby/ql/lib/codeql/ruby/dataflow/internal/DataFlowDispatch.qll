private import ruby
private import codeql.ruby.CFG
private import DataFlowPrivate
private import codeql.ruby.typetracking.TypeTracker
private import codeql.ruby.ast.internal.Module
private import FlowSummaryImpl as FlowSummaryImpl
private import FlowSummaryImplSpecific as FlowSummaryImplSpecific
private import codeql.ruby.dataflow.FlowSummary

newtype TReturnKind =
  TNormalReturnKind() or
  TBreakReturnKind()

/**
 * Gets a node that can read the value returned from `call` with return kind
 * `kind`.
 */
OutNode getAnOutNode(DataFlowCall call, ReturnKind kind) { call = result.getCall(kind) }

/**
 * A return kind. A return kind describes how a value can be returned
 * from a callable.
 */
abstract class ReturnKind extends TReturnKind {
  /** Gets a textual representation of this position. */
  abstract string toString();
}

/**
 * A value returned from a callable using a `return` statement or an expression
 * body, that is, a "normal" return.
 */
class NormalReturnKind extends ReturnKind, TNormalReturnKind {
  override string toString() { result = "return" }
}

/**
 * A value returned from a callable using a `break` statement.
 */
class BreakReturnKind extends ReturnKind, TBreakReturnKind {
  override string toString() { result = "break" }
}

/** A callable defined in library code, identified by a unique string. */
abstract class LibraryCallable extends string {
  bindingset[this]
  LibraryCallable() { any() }

  /** Gets a call to this library callable. */
  abstract Call getACall();
}

/**
 * A callable. This includes callables from source code, as well as callables
 * defined in library code.
 */
class DataFlowCallable extends TDataFlowCallable {
  /** Gets the underlying source code callable, if any. */
  Callable asCallable() { this = TCfgScope(result) }

  /** Gets the underlying library callable, if any. */
  LibraryCallable asLibraryCallable() { this = TLibraryCallable(result) }

  /** Gets a textual representation of this callable. */
  string toString() { result = [this.asCallable().toString(), this.asLibraryCallable()] }

  /** Gets the location of this callable. */
  Location getLocation() {
    result = this.asCallable().getLocation()
    or
    this instanceof TLibraryCallable and
    result instanceof EmptyLocation
  }
}

/**
 * A call. This includes calls from source code, as well as call(back)s
 * inside library callables with a flow summary.
 */
class DataFlowCall extends TDataFlowCall {
  /** Gets the enclosing callable. */
  DataFlowCallable getEnclosingCallable() { none() }

  /** Gets the underlying source code call, if any. */
  CfgNodes::ExprNodes::CallCfgNode asCall() { none() }

  /** Gets a textual representation of this call. */
  string toString() { none() }

  /** Gets the location of this call. */
  Location getLocation() { none() }

  /**
   * Holds if this element is at the specified location.
   * The location spans column `startcolumn` of line `startline` to
   * column `endcolumn` of line `endline` in file `filepath`.
   * For more information, see
   * [Locations](https://codeql.github.com/docs/writing-codeql-queries/providing-locations-in-codeql-queries).
   */
  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    this.getLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
  }
}

/**
 * A synthesized call inside a callable with a flow summary.
 *
 * For example, in
 * ```rb
 * ints.each do |i|
 *   puts i
 * end
 * ```
 *
 * there is a call to the block argument inside `each`.
 */
class SummaryCall extends DataFlowCall, TSummaryCall {
  private FlowSummaryImpl::Public::SummarizedCallable c;
  private DataFlow::Node receiver;

  SummaryCall() { this = TSummaryCall(c, receiver) }

  /** Gets the data flow node that this call targets. */
  DataFlow::Node getReceiver() { result = receiver }

  override DataFlowCallable getEnclosingCallable() { result.asLibraryCallable() = c }

  override string toString() { result = "[summary] call to " + receiver + " in " + c }

  override EmptyLocation getLocation() { any() }
}

private class NormalCall extends DataFlowCall, TNormalCall {
  private CfgNodes::ExprNodes::CallCfgNode c;

  NormalCall() { this = TNormalCall(c) }

  override CfgNodes::ExprNodes::CallCfgNode asCall() { result = c }

  override DataFlowCallable getEnclosingCallable() { result = TCfgScope(c.getScope()) }

  override string toString() { result = c.toString() }

  override Location getLocation() { result = c.getLocation() }
}

pragma[nomagic]
private predicate methodCall(
  CfgNodes::ExprNodes::CallCfgNode call, DataFlow::LocalSourceNode sourceNode, string method
) {
  exists(DataFlow::Node nodeTo |
    method = call.getExpr().(MethodCall).getMethodName() and
    nodeTo.asExpr() = call.getReceiver() and
    sourceNode.flowsTo(nodeTo)
  )
}

private Block yieldCall(CfgNodes::ExprNodes::CallCfgNode call) {
  call.getExpr() instanceof YieldCall and
  exists(BlockParameterNode node |
    node = trackBlock(result) and
    node.getMethod() = call.getExpr().getEnclosingMethod()
  )
}

pragma[nomagic]
private predicate superCall(CfgNodes::ExprNodes::CallCfgNode call, Module superClass, string method) {
  call.getExpr() instanceof SuperCall and
  exists(Module tp |
    tp = call.getExpr().getEnclosingModule().getModule() and
    superClass = tp.getSuperClass() and
    method = call.getExpr().getEnclosingMethod().getName()
  )
}

pragma[nomagic]
private predicate instanceMethodCall0(
  CfgNodes::ExprNodes::CallCfgNode call, Module tp, boolean exact, string method
) {
  exists(DataFlow::LocalSourceNode sourceNode |
    methodCall(call, sourceNode, method) and
    sourceNode = trackInstance(tp, exact)
  )
}

pragma[nomagic]
private predicate instanceMethodCall(CfgNodes::ExprNodes::CallCfgNode call, Module tp, string method) {
  exists(Module m |
    // When we don't know the exact type, it could be any subclass
    instanceMethodCall0(call, m, false, method) and
    tp.getSuperClass*() = m
  )
  or
  instanceMethodCall0(call, tp, true, method)
}

cached
private module Cached {
  cached
  newtype TDataFlowCallable =
    TCfgScope(CfgScope scope) or
    TLibraryCallable(LibraryCallable callable)

  cached
  newtype TDataFlowCall =
    TNormalCall(CfgNodes::ExprNodes::CallCfgNode c) or
    TSummaryCall(FlowSummaryImpl::Public::SummarizedCallable c, DataFlow::Node receiver) {
      FlowSummaryImpl::Private::summaryCallbackRange(c, receiver)
    }

  cached
  CfgScope getTarget(CfgNodes::ExprNodes::CallCfgNode call) {
    // Temporarily disable operation resolution (due to bad performance)
    // not call.getExpr() instanceof Operation and
    (
      exists(string method |
        exists(Module tp |
          instanceMethodCall(call, tp, method) and
          result = lookupMethod(tp, method) and
          if result.(Method).isPrivate()
          then
            exists(SelfVariableAccess self |
              self = call.getReceiver().getExpr() and
              pragma[only_bind_out](self.getEnclosingModule().getModule().getSuperClass*()) =
                pragma[only_bind_out](result.getEnclosingModule().getModule())
            ) and
            // For now, we restrict the scope of top-level declarations to their file.
            // This may remove some plausible targets, but also removes a lot of
            // implausible targets
            if result.getEnclosingModule() instanceof Toplevel
            then result.getFile() = call.getFile()
            else any()
          else any()
        )
        or
        exists(DataFlow::LocalSourceNode sourceNode |
          methodCall(call, sourceNode, method) and
          sourceNode = trackSingletonMethod(result, method)
        )
      )
      or
      exists(Module superClass, string method |
        superCall(call, superClass, method) and
        result = lookupMethod(superClass, method)
      )
      or
      result = yieldCall(call)
    )
  }

  /** Gets a viable run-time target for the call `call`. */
  cached
  DataFlowCallable viableCallable(DataFlowCall call) {
    result = TCfgScope(getTarget(call.asCall())) and
    not call.asCall().getExpr() instanceof YieldCall // handled by `lambdaCreation`/`lambdaCall`
    or
    exists(LibraryCallable callable |
      result = TLibraryCallable(callable) and
      call.asCall().getExpr() = callable.getACall()
    )
  }

  cached
  newtype TArgumentPosition =
    TSelfArgumentPosition() or
    TBlockArgumentPosition() or
    TPositionalArgumentPosition(int pos) {
      exists(Call c | exists(c.getArgument(pos)))
      or
      FlowSummaryImplSpecific::ParsePositions::isParsedParameterPosition(_, pos)
    } or
    TKeywordArgumentPosition(string name) {
      name = any(KeywordParameter kp).getName()
      or
      exists(any(Call c).getKeywordArgument(name))
      or
      FlowSummaryImplSpecific::ParsePositions::isParsedKeywordParameterPosition(_, name)
    } or
    THashSplatArgumentPosition() or
    TAnyArgumentPosition() or
    TAnyKeywordArgumentPosition()

  cached
  newtype TParameterPosition =
    TSelfParameterPosition() or
    TBlockParameterPosition() or
    TPositionalParameterPosition(int pos) {
      pos = any(Parameter p).getPosition()
      or
      FlowSummaryImplSpecific::ParsePositions::isParsedArgumentPosition(_, pos)
    } or
    TPositionalParameterLowerBoundPosition(int pos) {
      FlowSummaryImplSpecific::ParsePositions::isParsedArgumentLowerBoundPosition(_, pos)
    } or
    TKeywordParameterPosition(string name) {
      name = any(KeywordParameter kp).getName()
      or
      FlowSummaryImplSpecific::ParsePositions::isParsedKeywordArgumentPosition(_, name)
    } or
    THashSplatParameterPosition() or
    TAnyParameterPosition() or
    TAnyKeywordParameterPosition()
}

import Cached

/**
 * Holds if `self` variable has module type `m`.
 *
 * The Boolean `exact` indicates whether `self` has exactly the type `m`
 * (and not possibly a sub class of `m`).
 */
pragma[nomagic]
private predicate resolveSelf(SelfVariable self, boolean exact, Module m) {
  exists(Scope scope | scope = self.getDeclaringScope() |
    // `self` in module
    (
      if scope instanceof Toplevel
      then m = TResolved("Object") and exact = true
      else (
        m = scope.(ModuleBase).getModule() and
        exact = false
      )
    )
    or
    // `self` in method
    exists(ModuleBase encl |
      encl = scope.(MethodBase).getEnclosingModule() and
      exact = false and
      if encl instanceof SingletonClass
      then m = encl.getEnclosingModule().getModule()
      else m = encl.getModule()
    )
  )
}

private predicate resolveSelfNode(SsaSelfDefinitionNode self, boolean exact, Module m) {
  resolveSelf(self.getVariable(), exact, m)
}

/**
 * Holds if `n` refers to module `m`.
 *
 * The Boolean `exact` indicates whether `n` refers to exactly `m` (and not
 * possibly a sub class).
 */
private predicate resolveModule(Expr e, boolean exact, Module m) {
  m = resolveConstantReadAccess(e) and
  exact = true
  or
  resolveSelf(e.(SelfVariableReadAccess).getVariable(), exact, m)
}

private predicate resolveModuleNode(DataFlow::Node n, boolean exact, Module m) {
  m = resolveConstantReadAccess(n.asExpr().getExpr()) and
  exact = true
  or
  resolveSelfNode(n, exact, m)
}

private DataFlow::LocalSourceNode trackInstance(Module tp, boolean exact, TypeTracker t) {
  t.start() and
  (
    result.asExpr().getExpr() instanceof NilLiteral and
    tp = TResolved("NilClass") and
    exact = false
    or
    result.asExpr().getExpr().(BooleanLiteral).isFalse() and
    tp = TResolved("FalseClass") and
    exact = true
    or
    result.asExpr().getExpr().(BooleanLiteral).isTrue() and
    tp = TResolved("TrueClass") and
    exact = true
    or
    result.asExpr().getExpr() instanceof IntegerLiteral and
    tp = TResolved("Integer") and
    exact = true
    or
    result.asExpr().getExpr() instanceof FloatLiteral and
    tp = TResolved("Float") and
    exact = true
    or
    result.asExpr().getExpr() instanceof RationalLiteral and
    tp = TResolved("Rational") and
    exact = true
    or
    result.asExpr().getExpr() instanceof ComplexLiteral and
    tp = TResolved("Complex") and
    exact = true
    or
    result.asExpr().getExpr() instanceof StringlikeLiteral and
    tp = TResolved("String") and
    exact = true
    or
    result.asExpr() instanceof CfgNodes::ExprNodes::ArrayLiteralCfgNode and
    tp = TResolved("Array") and
    exact = true
    or
    result.asExpr() instanceof CfgNodes::ExprNodes::HashLiteralCfgNode and
    tp = TResolved("Hash") and
    exact = true
    or
    result.asExpr().getExpr() instanceof MethodBase and
    tp = TResolved("Symbol") and
    exact = true
    or
    result.asParameter() instanceof BlockParameter and
    tp = TResolved("Proc") and
    exact = true
    or
    result.asExpr().getExpr() instanceof Lambda and
    tp = TResolved("Proc") and
    exact = true
    or
    exists(CfgNodes::ExprNodes::CallCfgNode call, Expr receiver |
      call.getExpr().(MethodCall).getMethodName() = "new" and
      resolveModule(receiver, exact, tp) and
      receiver = call.getReceiver().getExpr() and
      result.asExpr() = call
    )
    or
    // `self` reference in method or top-level (but not in module, where instance
    // methods cannot be called; only singleton methods)
    resolveSelfNode(result, exact, tp) and
    not result.(SsaSelfDefinitionNode).getSelfScope() =
      any(ModuleBase m | not m instanceof Toplevel)
    or
    // needed for built-ins, e.g. `puts`
    exists(Module m |
      resolveModuleNode(result, _, m) and
      not result.(SsaSelfDefinitionNode).getSelfScope() instanceof Toplevel and
      (if m.isClass() then tp = TResolved("Class") else tp = TResolved("Module")) and
      exact = true
    )
  )
  or
  exists(TypeTracker t2, StepSummary summary |
    result = trackInstanceRec(tp, t2, exact, summary) and t = t2.append(summary)
  )
}

/**
 * A restricted version of `StepSummary::step`, where we exclude steps into `self`
 * parameters. For those, we instead rely on the type of the enclosing module, and
 * apply an open-world assumption when determining possible dispatch targets.
 */
pragma[inline]
private predicate step(
  DataFlow::LocalSourceNode nodeFrom, DataFlow::LocalSourceNode nodeTo, StepSummary summary
) {
  StepSummary::step(nodeFrom, nodeTo, summary) and
  not nodeTo instanceof SelfParameterNode
}

pragma[nomagic]
private DataFlow::LocalSourceNode trackInstanceRec(
  Module tp, TypeTracker t, boolean exact, StepSummary summary
) {
  step(trackInstance(tp, exact, t), result, summary)
}

private DataFlow::LocalSourceNode trackInstance(Module tp, boolean exact) {
  result = trackInstance(tp, exact, TypeTracker::end())
}

private DataFlow::LocalSourceNode trackBlock(Block block, TypeTracker t) {
  t.start() and result.asExpr().getExpr() = block
  or
  exists(TypeTracker t2, StepSummary summary |
    result = trackBlockRec(block, t2, summary) and t = t2.append(summary)
  )
}

pragma[nomagic]
private DataFlow::LocalSourceNode trackBlockRec(Block block, TypeTracker t, StepSummary summary) {
  step(trackBlock(block, t), result, summary)
}

private DataFlow::LocalSourceNode trackBlock(Block block) {
  result = trackBlock(block, TypeTracker::end())
}

pragma[nomagic]
predicate singletonMethodOnInstance(MethodBase method, string name, Expr object) {
  name = method.getName() and
  (
    object = method.(SingletonMethod).getObject() and
    not resolveModule(object, _, _)
    or
    exists(SingletonClass cls |
      object = cls.getValue() and
      method instanceof Method and
      method = cls.getAMethod()
    )
  )
}

pragma[nomagic]
private predicate singletonMethodOnModule(MethodBase method, Module m) {
  exists(Expr object |
    object = method.(SingletonMethod).getObject() and
    resolveModule(object, _, m)
  )
}

/**
 * Holds if module `m` is the target of singleton method `method`. For example, in
 *
 * ```rb
 * class C
 *   def self.foo; end
 * end
 * ```
 *
 * the class `C` is the target of the singleton method `foo`.
 */
pragma[nomagic]
private predicate moduleFlowsToSingletonMethodObject(Module m, MethodBase method) {
  exists(DataFlow::Node n |
    resolveModuleNode(n, _, m) and
    // flowsToSingletonMethodObject(n, method) // TODO
    singletonMethodOnModule(method, m)
  )
}

pragma[nomagic]
private DataFlow::LocalSourceNode trackSingletonMethod(MethodBase method, string name, TypeTracker t) {
  t.start() and
  name = method.getName() and
  // singleton method define on an instance
  // flowsToSingletonMethodObject(result, method)
  singletonMethodOnInstance(method, _,
    result.(DataFlow::PostUpdateNode).getPreUpdateNode().asExpr().getExpr())
  or
  exists(TypeTracker t2, StepSummary summary |
    result = trackSingletonMethodRec(method, name, t2, summary) and
    t = t2.append(summary) and
    // do not step over redefinitions
    not singletonMethodOnInstance(_, name,
      result.(DataFlow::PostUpdateNode).getPreUpdateNode().asExpr().getExpr())
  )
}

pragma[nomagic]
private DataFlow::LocalSourceNode trackSingletonMethodRec(
  MethodBase method, string name, TypeTracker t, StepSummary summary
) {
  step(trackSingletonMethod(method, name, t), result, summary)
}

pragma[nomagic]
private DataFlow::LocalSourceNode trackSingletonMethod(MethodBase method, string name) {
  result = trackSingletonMethod(method, name, TypeTracker::end())
  or
  // singleton method defined in a module
  exists(Module m |
    resolveModuleNode(result, _, m) and
    name = method.getName() and
    moduleFlowsToSingletonMethodObject(m, method) // TODO move out
  )
}

/**
 * Holds if the set of viable implementations that can be called by `call`
 * might be improved by knowing the call context. This is the case if the
 * qualifier accesses a parameter of the enclosing callable `c` (including
 * the implicit `self` parameter).
 */
predicate mayBenefitFromCallContext(DataFlowCall call, DataFlowCallable c) { none() }

/**
 * Gets a viable dispatch target of `call` in the context `ctx`. This is
 * restricted to those `call`s for which a context might make a difference.
 */
DataFlowCallable viableImplInCallContext(DataFlowCall call, DataFlowCall ctx) { none() }

predicate exprNodeReturnedFrom = exprNodeReturnedFromCached/2;

/** A parameter position. */
class ParameterPosition extends TParameterPosition {
  /** Holds if this position represents a `self` parameter. */
  predicate isSelf() { this = TSelfParameterPosition() }

  /** Holds if this position represents a block parameter. */
  predicate isBlock() { this = TBlockParameterPosition() }

  /** Holds if this position represents a positional parameter at position `pos`. */
  predicate isPositional(int pos) { this = TPositionalParameterPosition(pos) }

  /** Holds if this position represents any positional parameter starting from position `pos`. */
  predicate isPositionalLowerBound(int pos) { this = TPositionalParameterLowerBoundPosition(pos) }

  /** Holds if this position represents a keyword parameter named `name`. */
  predicate isKeyword(string name) { this = TKeywordParameterPosition(name) }

  /** Holds if this position represents a hash-splat parameter. */
  predicate isHashSplat() { this = THashSplatParameterPosition() }

  /**
   * Holds if this position represents any parameter, except `self` parameters. This
   * includes both positional, named, and block parameters.
   */
  predicate isAny() { this = TAnyParameterPosition() }

  /** Holds if this position represents any positional parameter. */
  predicate isAnyNamed() { this = TAnyKeywordParameterPosition() }

  /** Gets a textual representation of this position. */
  string toString() {
    this.isSelf() and result = "self"
    or
    this.isBlock() and result = "block"
    or
    exists(int pos | this.isPositional(pos) and result = "position " + pos)
    or
    exists(int pos | this.isPositionalLowerBound(pos) and result = "position " + pos + "..")
    or
    exists(string name | this.isKeyword(name) and result = "keyword " + name)
    or
    this.isHashSplat() and result = "**"
    or
    this.isAny() and result = "any"
    or
    this.isAnyNamed() and result = "any-named"
  }
}

/** An argument position. */
class ArgumentPosition extends TArgumentPosition {
  /** Holds if this position represents a `self` argument. */
  predicate isSelf() { this = TSelfArgumentPosition() }

  /** Holds if this position represents a block argument. */
  predicate isBlock() { this = TBlockArgumentPosition() }

  /** Holds if this position represents a positional argument at position `pos`. */
  predicate isPositional(int pos) { this = TPositionalArgumentPosition(pos) }

  /** Holds if this position represents a keyword argument named `name`. */
  predicate isKeyword(string name) { this = TKeywordArgumentPosition(name) }

  /**
   * Holds if this position represents any argument, except `self` arguments. This
   * includes both positional, named, and block arguments.
   */
  predicate isAny() { this = TAnyArgumentPosition() }

  /** Holds if this position represents any positional parameter. */
  predicate isAnyNamed() { this = TAnyKeywordArgumentPosition() }

  /**
   * Holds if this position represents a synthesized argument containing all keyword
   * arguments wrapped in a hash.
   */
  predicate isHashSplat() { this = THashSplatArgumentPosition() }

  /** Gets a textual representation of this position. */
  string toString() {
    this.isSelf() and result = "self"
    or
    this.isBlock() and result = "block"
    or
    exists(int pos | this.isPositional(pos) and result = "position " + pos)
    or
    exists(string name | this.isKeyword(name) and result = "keyword " + name)
    or
    this.isAny() and result = "any"
    or
    this.isAnyNamed() and result = "any-named"
    or
    this.isHashSplat() and result = "**"
  }
}

pragma[nomagic]
private predicate parameterPositionIsNotSelf(ParameterPosition ppos) { not ppos.isSelf() }

pragma[nomagic]
private predicate argumentPositionIsNotSelf(ArgumentPosition apos) { not apos.isSelf() }

/** Holds if arguments at position `apos` match parameters at position `ppos`. */
pragma[nomagic]
predicate parameterMatch(ParameterPosition ppos, ArgumentPosition apos) {
  ppos.isSelf() and apos.isSelf()
  or
  ppos.isBlock() and apos.isBlock()
  or
  exists(int pos | ppos.isPositional(pos) and apos.isPositional(pos))
  or
  exists(int pos1, int pos2 |
    ppos.isPositionalLowerBound(pos1) and apos.isPositional(pos2) and pos2 >= pos1
  )
  or
  exists(string name | ppos.isKeyword(name) and apos.isKeyword(name))
  or
  ppos.isHashSplat() and apos.isHashSplat()
  or
  ppos.isAny() and argumentPositionIsNotSelf(apos)
  or
  apos.isAny() and parameterPositionIsNotSelf(ppos)
  or
  ppos.isAnyNamed() and apos.isKeyword(_)
  or
  apos.isAnyNamed() and ppos.isKeyword(_)
}
