/**
 * Provides a module for synthesizing data-flow nodes and related step relations
 * for supporting flow through captured variables.
 */

private import codeql.util.Boolean
private import codeql.util.Unit
private import codeql.ssa.Ssa as Ssa

signature module InputSig {
  class Location {
    predicate hasLocationInfo(
      string filepath, int startline, int startcolumn, int endline, int endcolumn
    );
  }

  /**
   * A basic block, that is, a maximal straight-line sequence of control flow nodes
   * without branches or joins.
   */
  class BasicBlock {
    /** Gets a textual representation of this basic block. */
    string toString();

    /** Gets the enclosing callable. */
    Callable getEnclosingCallable();

    /** Gets the location of this basic block. */
    Location getLocation();
  }

  /**
   * Gets the basic block that immediately dominates basic block `bb`, if any.
   *
   * That is, all paths reaching `bb` from some entry point basic block must go
   * through the result.
   *
   * Example:
   *
   * ```csharp
   * int M(string s) {
   *   if (s == null)
   *     throw new ArgumentNullException(nameof(s));
   *   return s.Length;
   * }
   * ```
   *
   * The basic block starting on line 2 is an immediate dominator of
   * the basic block on line 4 (all paths from the entry point of `M`
   * to `return s.Length;` must go through the null check.
   */
  BasicBlock getImmediateBasicBlockDominator(BasicBlock bb);

  /** Gets an immediate successor of basic block `bb`, if any. */
  BasicBlock getABasicBlockSuccessor(BasicBlock bb);

  /** Holds if `bb` is a control-flow entry point. */
  default predicate entryBlock(BasicBlock bb) { not exists(getImmediateBasicBlockDominator(bb)) }

  /** Holds if `bb` is a control-flow exit point. */
  default predicate exitBlock(BasicBlock bb) { not exists(getABasicBlockSuccessor(bb)) }

  /** A variable that is captured in a closure. */
  class CapturedVariable {
    /** Gets a textual representation of this variable. */
    string toString();

    /** Gets the callable that defines this variable. */
    Callable getCallable();

    /** Gets the location of this variable. */
    Location getLocation();
  }

  /** A parameter that is captured in a closure. */
  class CapturedParameter extends CapturedVariable;

  /**
   * An expression with a value. That is, we expect these expressions to be
   * represented in the data flow graph.
   */
  class Expr {
    /** Gets a textual representation of this expression. */
    string toString();

    /** Gets the location of this expression. */
    Location getLocation();

    /** Holds if the `i`th node of basic block `bb` evaluates this expression. */
    predicate hasCfgNode(BasicBlock bb, int i);
  }

  /** A write to a captured variable. */
  class VariableWrite {
    /** Gets the variable that is the target of this write. */
    CapturedVariable getVariable();

    /** Gets the expression that is the source of this write. */
    Expr getSource();

    /** Gets the location of this write. */
    Location getLocation();

    /** Holds if the `i`th node of basic block `bb` evaluates this expression. */
    predicate hasCfgNode(BasicBlock bb, int i);
  }

  /** A read of a captured variable. */
  class VariableRead extends Expr {
    /** Gets the variable that this expression reads. */
    CapturedVariable getVariable();
  }

  /**
   * An expression constructing a closure that may capture one or more
   * variables. This can for example be a lambda or a constructor call of a
   * locally defined object.
   */
  class ClosureExpr extends Expr {
    /**
     * Holds if `body` is the callable body of this closure. A lambda expression
     * only has one body, but in general a locally defined object may have
     * multiple such methods and constructors.
     */
    predicate hasBody(Callable body);

    /**
     * Holds if `f` is an expression that may hold the value of the closure and
     * may occur in a position where the value escapes or where the closure may
     * be invoked.
     *
     * For example, if a lambda is assigned to a variable, then references to
     * that variable in return or argument positions should be included.
     */
    predicate hasAliasedAccess(Expr f);
  }

  class Callable {
    /** Gets a textual representation of this callable. */
    string toString();

    /** Gets the location of this callable. */
    Location getLocation();
  }
}

signature module OutputSig<InputSig I> {
  /**
   * A data flow node that we need to reference in the step relations for
   * captured variables.
   */
  class ClosureNode;

  /**
   * A synthesized data flow node representing the storage of a captured
   * variable.
   */
  class SynthesizedCaptureNode extends ClosureNode {
    /** Gets a textual representation of this node. */
    string toString();

    /** Gets the location of this node. */
    I::Location getLocation();

    /** Gets the enclosing callable. */
    I::Callable getEnclosingCallable();

    /** Holds if this node is a synthesized access of `v`. */
    predicate isVariableAccess(I::CapturedVariable v);

    /** Holds if this node is a synthesized instance access. */
    predicate isInstanceAccess();
  }

  /** A data flow node for an expression. */
  class ExprNode extends ClosureNode {
    /** Gets the expression corresponding to this node. */
    I::Expr getExpr();
  }

  /** A data flow node for the `PostUpdateNode` of an expression. */
  class ExprPostUpdateNode extends ClosureNode {
    /** Gets the expression corresponding to this node. */
    I::Expr getExpr();
  }

  /** A data flow node for a parameter. */
  class ParameterNode extends ClosureNode {
    /** Gets the parameter corresponding to this node. */
    I::CapturedParameter getParameter();
  }

  /** A data flow node for an instance parameter. */
  class ThisParameterNode extends ClosureNode {
    /** Gets the callable this instance parameter belongs to. */
    I::Callable getCallable();
  }

  /** Holds if `post` is a `PostUpdateNode` for `pre`. */
  predicate capturePostUpdateNode(SynthesizedCaptureNode post, SynthesizedCaptureNode pre);

  /** Holds if there is a local flow step from `node1` to `node2`. */
  predicate localFlowStep(ClosureNode node1, ClosureNode node2);

  /** Holds if there is a store step from `node1` to `node2`. */
  predicate storeStep(ClosureNode node1, I::CapturedVariable v, ClosureNode node2);

  /** Holds if there is a read step from `node1` to `node2`. */
  predicate readStep(ClosureNode node1, I::CapturedVariable v, ClosureNode node2);

  /**
   * Holds if `v` is available in `c` through capture. This can either be due to
   * an explicit variable reference or through the construction of a closure
   * that has a nested capture.
   */
  predicate captureAccess(I::CapturedVariable v, I::Callable c);

  /** Holds if this-to-this summaries are expected for `c`. */
  predicate heuristicAllowInstanceParameterReturnInSelf(I::Callable c);
}

/**
 * Constructs the type `ClosureNode` and associated step relations, which are
 * intended to be included in the data-flow node and step relations.
 */
module Flow<InputSig Input> implements OutputSig<Input> {
  private import Input

  additional module ConsistencyChecks {
    private predicate relevantExpr(Expr e) {
      e instanceof VariableRead or
      any(VariableWrite vw).getSource() = e or
      e instanceof ClosureExpr or
      any(ClosureExpr ce).hasAliasedAccess(e)
    }

    private predicate relevantBasicBlock(BasicBlock bb) {
      exists(Expr e | relevantExpr(e) and e.hasCfgNode(bb, _))
      or
      exists(VariableWrite vw | vw.hasCfgNode(bb, _))
    }

    private predicate relevantCallable(Callable c) {
      exists(BasicBlock bb | relevantBasicBlock(bb) and bb.getEnclosingCallable() = c)
      or
      exists(CapturedVariable v | v.getCallable() = c)
      or
      exists(ClosureExpr ce | ce.hasBody(c))
    }

    query predicate uniqueToString(string msg, int n) {
      exists(string elem |
        n = strictcount(BasicBlock bb | relevantBasicBlock(bb) and not exists(bb.toString())) and
        elem = "BasicBlock"
        or
        n = strictcount(CapturedVariable v | not exists(v.toString())) and elem = "CapturedVariable"
        or
        n = strictcount(Expr e | relevantExpr(e) and not exists(e.toString())) and elem = "Expr"
        or
        n = strictcount(Callable c | relevantCallable(c) and not exists(c.toString())) and
        elem = "Callable"
      |
        msg = n + " " + elem + "(s) are missing toString"
      )
      or
      exists(string elem |
        n = strictcount(BasicBlock bb | relevantBasicBlock(bb) and 2 <= strictcount(bb.toString())) and
        elem = "BasicBlock"
        or
        n = strictcount(CapturedVariable v | 2 <= strictcount(v.toString())) and
        elem = "CapturedVariable"
        or
        n = strictcount(Expr e | relevantExpr(e) and 2 <= strictcount(e.toString())) and
        elem = "Expr"
        or
        n = strictcount(Callable c | relevantCallable(c) and 2 <= strictcount(c.toString())) and
        elem = "Callable"
      |
        msg = n + " " + elem + "(s) have multiple toStrings"
      )
    }

    query predicate uniqueEnclosingCallable(BasicBlock bb, string msg) {
      relevantBasicBlock(bb) and
      (
        msg = "BasicBlock has no enclosing callable" and not exists(bb.getEnclosingCallable())
        or
        msg = "BasicBlock has multiple enclosing callables" and
        2 <= strictcount(bb.getEnclosingCallable())
      )
    }

    query predicate uniqueDominator(BasicBlock bb, string msg) {
      relevantBasicBlock(bb) and
      msg = "BasicBlock has multiple immediate dominators" and
      2 <= strictcount(getImmediateBasicBlockDominator(bb))
    }

    query predicate localDominator(BasicBlock bb, string msg) {
      relevantBasicBlock(bb) and
      msg = "BasicBlock has non-local dominator" and
      bb.getEnclosingCallable() != getImmediateBasicBlockDominator(bb).getEnclosingCallable()
    }

    query predicate localSuccessor(BasicBlock bb, string msg) {
      relevantBasicBlock(bb) and
      msg = "BasicBlock has non-local successor" and
      bb.getEnclosingCallable() != getABasicBlockSuccessor(bb).getEnclosingCallable()
    }

    query predicate uniqueDefiningScope(CapturedVariable v, string msg) {
      msg = "CapturedVariable has no defining callable" and not exists(v.getCallable())
      or
      msg = "CapturedVariable has multiple defining callables" and 2 <= strictcount(v.getCallable())
    }

    query predicate variableIsCaptured(CapturedVariable v, string msg) {
      msg = "CapturedVariable is not captured" and
      not captureAccess(v, _)
    }

    query predicate uniqueLocation(Expr e, string msg) {
      relevantExpr(e) and
      (
        msg = "Expr has no location" and not exists(e.getLocation())
        or
        msg = "Expr has multiple locations" and 2 <= strictcount(e.getLocation())
      )
    }

    query predicate uniqueCfgNode(Expr e, string msg) {
      relevantExpr(e) and
      (
        msg = "Expr has no cfg node" and not e.hasCfgNode(_, _)
        or
        msg = "Expr has multiple cfg nodes" and
        2 <= strictcount(BasicBlock bb, int i | e.hasCfgNode(bb, i))
      )
    }

    private predicate uniqueWriteTarget(VariableWrite vw, string msg) {
      msg = "VariableWrite has no target variable" and not exists(vw.getVariable())
      or
      msg = "VariableWrite has multiple target variables" and 2 <= strictcount(vw.getVariable())
    }

    query predicate uniqueWriteTarget(string msg) { uniqueWriteTarget(_, msg) }

    private predicate uniqueWriteSource(VariableWrite vw, string msg) {
      msg = "VariableWrite has no source expression" and not exists(vw.getSource())
      or
      msg = "VariableWrite has multiple source expressions" and 2 <= strictcount(vw.getSource())
    }

    query predicate uniqueWriteSource(string msg) { uniqueWriteSource(_, msg) }

    private predicate uniqueWriteCfgNode(VariableWrite vw, string msg) {
      msg = "VariableWrite has no cfg node" and not vw.hasCfgNode(_, _)
      or
      msg = "VariableWrite has multiple cfg nodes" and
      2 <= strictcount(BasicBlock bb, int i | vw.hasCfgNode(bb, i))
    }

    query predicate uniqueWriteCfgNode(string msg) { uniqueWriteCfgNode(_, msg) }

    private predicate localWriteStep(VariableWrite vw, string msg) {
      exists(BasicBlock bb |
        vw.hasCfgNode(bb, _) and
        bb.getEnclosingCallable() != vw.getVariable().getCallable() and
        msg = "VariableWrite is not a local step"
      )
    }

    query predicate localWriteStep(string msg) { localWriteStep(_, msg) }

    query predicate uniqueReadVariable(VariableRead vr, string msg) {
      msg = "VariableRead has no source variable" and not exists(vr.getVariable())
      or
      msg = "VariableRead has multiple source variables" and 2 <= strictcount(vr.getVariable())
    }

    query predicate closureMustHaveBody(ClosureExpr ce, string msg) {
      msg = "ClosureExpr has no body" and not ce.hasBody(_)
    }

    query predicate closureAliasMustBeLocal(ClosureExpr ce, Expr access, string msg) {
      exists(BasicBlock bb1, BasicBlock bb2 |
        ce.hasAliasedAccess(access) and
        ce.hasCfgNode(bb1, _) and
        access.hasCfgNode(bb2, _) and
        bb1.getEnclosingCallable() != bb2.getEnclosingCallable() and
        msg = "ClosureExpr has non-local alias - these are ignored"
      )
    }

    private predicate astClosureParent(Callable closure, Callable parent) {
      exists(ClosureExpr ce, BasicBlock bb |
        ce.hasBody(closure) and ce.hasCfgNode(bb, _) and parent = bb.getEnclosingCallable()
      )
    }

    query predicate variableAccessAstNesting(CapturedVariable v, Callable c, string msg) {
      exists(BasicBlock bb, Callable parent |
        captureRead(v, bb, _, false, _) or captureWrite(v, bb, _, false, _)
      |
        bb.getEnclosingCallable() = c and
        v.getCallable() = parent and
        not astClosureParent+(c, parent) and
        msg = "CapturedVariable access is not nested in the defining callable"
      )
    }

    query predicate uniqueCallableLocation(Callable c, string msg) {
      relevantCallable(c) and
      (
        msg = "Callable has no location" and not exists(c.getLocation())
        or
        msg = "Callable has multiple locations" and 2 <= strictcount(c.getLocation())
      )
    }

    query predicate consistencyOverview(string msg, int n) {
      uniqueToString(msg, n) or
      n = strictcount(BasicBlock bb | uniqueEnclosingCallable(bb, msg)) or
      n = strictcount(BasicBlock bb | uniqueDominator(bb, msg)) or
      n = strictcount(BasicBlock bb | localDominator(bb, msg)) or
      n = strictcount(BasicBlock bb | localSuccessor(bb, msg)) or
      n = strictcount(CapturedVariable v | uniqueDefiningScope(v, msg)) or
      n = strictcount(CapturedVariable v | variableIsCaptured(v, msg)) or
      n = strictcount(Expr e | uniqueLocation(e, msg)) or
      n = strictcount(Expr e | uniqueCfgNode(e, msg)) or
      n = strictcount(VariableWrite vw | uniqueWriteTarget(vw, msg)) or
      n = strictcount(VariableWrite vw | uniqueWriteSource(vw, msg)) or
      n = strictcount(VariableWrite vw | uniqueWriteCfgNode(vw, msg)) or
      n = strictcount(VariableWrite vw | localWriteStep(vw, msg)) or
      n = strictcount(VariableRead vr | uniqueReadVariable(vr, msg)) or
      n = strictcount(ClosureExpr ce | closureMustHaveBody(ce, msg)) or
      n = strictcount(ClosureExpr ce, Expr access | closureAliasMustBeLocal(ce, access, msg)) or
      n = strictcount(CapturedVariable v, Callable c | variableAccessAstNesting(v, c, msg)) or
      n = strictcount(Callable c | uniqueCallableLocation(c, msg))
    }
  }

  /*
   * Flow through captured variables is handled by making each captured variable
   * a field on the closures that capture them.
   *
   * For each closure creation we add a store step from the captured variable to
   * the closure, and inside the closures we access the captured variables with
   * a `this.` qualifier. This allows capture flow into closures.
   *
   * It also means that we get several aliased versions of a captured variable
   * so proper care must be taken to be able to observe side-effects or flow out
   * of closures. E.g. if two closures `l1` and `l2` capture `x` then we'll have
   * three names, `x`, `l1.x`, and `l2.x`, plus any potential aliasing of the
   * closures.
   *
   * To handle this, we select a primary name for a captured variable in each of
   * its scopes, keep that name updated, and update the other names from the
   * primary name.
   *
   * In the defining scope of a captured variable, we use the local variable
   * itself as the primary storage location, and in the capturing scopes we use
   * the synthesized field. For each relevant reference to a closure object we
   * then update its field from the primary storage location, and we read the
   * field back from the post-update of the closure object reference and back
   * into the primary storage location.
   *
   * If we include references to a closure object that may lead to a call as
   * relevant, then this means that we'll be able to observe the side-effects of
   * such calls in the primary storage location.
   *
   * Details:
   * For a reference to a closure `f` that captures `x` we synthesize a read of
   * `x` at the same control-flow node. We then add a store step from `x` to `f`
   * and a read step from `postupdate(f)` to `postupdate(x)`.
   * ```
   * SsaRead(x) --store[x]--> f
   * postupdate(f) --read[x]--> postupdate(SsaRead(x))
   * ```
   * In a closure scope with a nested closure `g` that also captures `x` the
   * steps instead look like this:
   * ```
   * SsaRead(this) --read[x]--> this.x --store[x]--> g
   * postupdate(g) --read[x]--> postupdate(this.x)
   * ```
   * The final store from `postupdate(this.x)` to `postupdate(this)` is
   * introduced automatically as a reverse read by the data flow library.
   */

  /**
   * Holds if `vr` is a read of `v` in the `i`th node of `bb`.
   * `topScope` is true if the read is in the defining callable of `v`.
   */
  private predicate captureRead(
    CapturedVariable v, BasicBlock bb, int i, boolean topScope, VariableRead vr
  ) {
    vr.getVariable() = v and
    vr.hasCfgNode(bb, i) and
    if v.getCallable() != bb.getEnclosingCallable() then topScope = false else topScope = true
  }

  /**
   * Holds if `vw` is a write of `v` in the `i`th node of `bb`.
   * `topScope` is true if the write is in the defining callable of `v`.
   */
  private predicate captureWrite(
    CapturedVariable v, BasicBlock bb, int i, boolean topScope, VariableWrite vw
  ) {
    vw.getVariable() = v and
    vw.hasCfgNode(bb, i) and
    if v.getCallable() != bb.getEnclosingCallable() then topScope = false else topScope = true
  }

  /** Gets the enclosing callable of `ce`. */
  private Callable closureExprGetCallable(ClosureExpr ce) {
    exists(BasicBlock bb | ce.hasCfgNode(bb, _) and result = bb.getEnclosingCallable())
  }

  predicate captureAccess(CapturedVariable v, Callable c) {
    exists(BasicBlock bb | captureRead(v, bb, _, _, _) or captureWrite(v, bb, _, _, _) |
      c = bb.getEnclosingCallable() and
      c != v.getCallable()
    )
    or
    exists(ClosureExpr ce |
      c = closureExprGetCallable(ce) and
      closureCaptures(ce, v) and
      c != v.getCallable()
    )
  }

  /** Holds if the closure defined by `ce` captures `v`. */
  private predicate closureCaptures(ClosureExpr ce, CapturedVariable v) {
    exists(Callable c | ce.hasBody(c) and captureAccess(v, c))
  }

  predicate heuristicAllowInstanceParameterReturnInSelf(Callable c) {
    // If multiple variables are captured, then we should allow flow from one to
    // another, which entails a this-to-this summary.
    2 <= strictcount(CapturedVariable v | captureAccess(v, c))
  }

  /**
   * Holds if `access` is a reference to `ce` evaluated in the `i`th node of `bb`.
   * The reference is restricted to be in the same callable as `ce` as a
   * precaution, even though this is expected to hold for all the given aliased
   * accesses.
   */
  private predicate localClosureAccess(ClosureExpr ce, Expr access, BasicBlock bb, int i) {
    ce.hasAliasedAccess(access) and
    access.hasCfgNode(bb, i) and
    pragma[only_bind_out](bb.getEnclosingCallable()) =
      pragma[only_bind_out](closureExprGetCallable(ce))
  }

  /**
   * Holds if we need an additional read of `v` in the `i`th node of `bb` in
   * order to synchronize the value stored on `closure`.
   * `topScope` is true if the read is in the defining callable of `v`.
   *
   * Side-effects of potentially calling `closure` at this point will be
   * observed in a similarly synthesized post-update node for this read of `v`.
   */
  private predicate synthRead(
    CapturedVariable v, BasicBlock bb, int i, boolean topScope, Expr closure
  ) {
    exists(ClosureExpr ce | closureCaptures(ce, v) |
      ce.hasCfgNode(bb, i) and ce = closure
      or
      localClosureAccess(ce, closure, bb, i)
    ) and
    if v.getCallable() != bb.getEnclosingCallable() then topScope = false else topScope = true
  }

  /**
   * Holds if there is an access of a captured variable inside a closure in the
   * `i`th node of `bb`, such that we need to synthesize a `this.` qualifier.
   */
  private predicate synthThisQualifier(BasicBlock bb, int i) {
    synthRead(_, bb, i, false, _) or
    captureRead(_, bb, i, false, _) or
    captureWrite(_, bb, i, false, _)
  }

  private newtype TCaptureContainer =
    TVariable(CapturedVariable v) or
    TThis(Callable c) { captureAccess(_, c) }

  /**
   * A storage location for a captured variable in a specific callable. This is
   * either the variable itself (in its defining scope) or an instance variable
   * `this` (in a capturing scope).
   */
  private class CaptureContainer extends TCaptureContainer {
    string toString() {
      exists(CapturedVariable v | this = TVariable(v) and result = v.toString())
      or
      result = "this" and this = TThis(_)
    }
  }

  /** Holds if `cc` needs a definition at the entry of its callable scope. */
  private predicate entryDef(CaptureContainer cc, BasicBlock bb, int i) {
    exists(Callable c |
      entryBlock(bb) and
      pragma[only_bind_out](bb.getEnclosingCallable()) = c and
      i =
        -1 +
          min(int j |
            j = 1 or
            captureRead(_, bb, j, _, _) or
            captureWrite(_, bb, j, _, _) or
            synthRead(_, bb, j, _, _)
          )
    |
      cc = TThis(c)
      or
      exists(CapturedParameter p | cc = TVariable(p) and p.getCallable() = c)
    )
  }

  private module CaptureSsaInput implements Ssa::InputSig {
    class BasicBlock instanceof Input::BasicBlock {
      string toString() { result = super.toString() }
    }

    BasicBlock getImmediateBasicBlockDominator(BasicBlock bb) {
      result = Input::getImmediateBasicBlockDominator(bb)
    }

    BasicBlock getABasicBlockSuccessor(BasicBlock bb) {
      result = Input::getABasicBlockSuccessor(bb)
    }

    class ExitBasicBlock extends BasicBlock {
      ExitBasicBlock() { exitBlock(this) }
    }

    class SourceVariable = CaptureContainer;

    predicate variableWrite(BasicBlock bb, int i, SourceVariable cc, boolean certain) {
      (
        exists(CapturedVariable v | cc = TVariable(v) and captureWrite(v, bb, i, true, _))
        or
        entryDef(cc, bb, i)
      ) and
      certain = true
    }

    predicate variableRead(BasicBlock bb, int i, SourceVariable cc, boolean certain) {
      (
        synthThisQualifier(bb, i) and cc = TThis(bb.(Input::BasicBlock).getEnclosingCallable())
        or
        exists(CapturedVariable v | cc = TVariable(v) |
          captureRead(v, bb, i, true, _) or synthRead(v, bb, i, true, _)
        )
      ) and
      certain = true
    }
  }

  private module CaptureSsa = Ssa::Make<CaptureSsaInput>;

  private newtype TClosureNode =
    TSynthRead(CapturedVariable v, BasicBlock bb, int i, Boolean isPost) {
      synthRead(v, bb, i, _, _)
    } or
    TSynthThisQualifier(BasicBlock bb, int i, Boolean isPost) { synthThisQualifier(bb, i) } or
    TSynthPhi(CaptureSsa::DefinitionExt phi) {
      phi instanceof CaptureSsa::PhiNode or phi instanceof CaptureSsa::PhiReadNode
    } or
    TExprNode(Expr expr, boolean isPost) {
      expr instanceof VariableRead and isPost = [false, true]
      or
      exists(VariableWrite vw | expr = vw.getSource() and isPost = false)
      or
      synthRead(_, _, _, _, expr) and isPost = [false, true]
    } or
    TParamNode(CapturedParameter p) or
    TThisParamNode(Callable c) { captureAccess(_, c) }

  class ClosureNode extends TClosureNode {
    /** Gets a textual representation of this node. */
    string toString() {
      exists(CapturedVariable v | this = TSynthRead(v, _, _, _) and result = v.toString())
      or
      result = "this" and this = TSynthThisQualifier(_, _, _)
      or
      exists(CaptureSsa::DefinitionExt phi, CaptureContainer cc |
        this = TSynthPhi(phi) and
        phi.definesAt(cc, _, _, _) and
        result = "phi(" + cc.toString() + ")"
      )
      or
      exists(Expr expr, boolean isPost | this = TExprNode(expr, isPost) |
        isPost = false and result = expr.toString()
        or
        isPost = true and result = expr.toString() + " [postupdate]"
      )
      or
      exists(CapturedParameter p | this = TParamNode(p) and result = p.toString())
      or
      result = "this" and this = TThisParamNode(_)
    }

    /** Gets the location of this node. */
    Location getLocation() {
      exists(CapturedVariable v, BasicBlock bb, int i, Expr closure |
        this = TSynthRead(v, bb, i, _) and
        synthRead(v, bb, i, _, closure) and
        result = closure.getLocation()
      )
      or
      exists(BasicBlock bb, int i | this = TSynthThisQualifier(bb, i, _) |
        synthRead(_, bb, i, false, any(Expr closure | result = closure.getLocation())) or
        captureRead(_, bb, i, false, any(VariableRead vr | result = vr.getLocation())) or
        captureWrite(_, bb, i, false, any(VariableWrite vw | result = vw.getLocation()))
      )
      or
      exists(CaptureSsa::DefinitionExt phi, BasicBlock bb |
        this = TSynthPhi(phi) and phi.definesAt(_, bb, _, _) and result = bb.getLocation()
      )
      or
      exists(Expr expr | this = TExprNode(expr, _) and result = expr.getLocation())
      or
      exists(CapturedParameter p | this = TParamNode(p) and result = p.getCallable().getLocation())
      or
      exists(Callable c | this = TThisParamNode(c) and result = c.getLocation())
    }
  }

  private class TSynthesizedCaptureNode = TSynthRead or TSynthThisQualifier or TSynthPhi;

  class SynthesizedCaptureNode extends ClosureNode, TSynthesizedCaptureNode {
    Callable getEnclosingCallable() {
      exists(BasicBlock bb | this = TSynthRead(_, bb, _, _) and result = bb.getEnclosingCallable())
      or
      exists(BasicBlock bb |
        this = TSynthThisQualifier(bb, _, _) and result = bb.getEnclosingCallable()
      )
      or
      exists(CaptureSsa::DefinitionExt phi, BasicBlock bb |
        this = TSynthPhi(phi) and phi.definesAt(_, bb, _, _) and result = bb.getEnclosingCallable()
      )
    }

    predicate isVariableAccess(CapturedVariable v) {
      this = TSynthRead(v, _, _, _)
      or
      exists(CaptureSsa::DefinitionExt phi |
        this = TSynthPhi(phi) and phi.definesAt(TVariable(v), _, _, _)
      )
    }

    predicate isInstanceAccess() {
      this instanceof TSynthThisQualifier
      or
      exists(CaptureSsa::DefinitionExt phi |
        this = TSynthPhi(phi) and phi.definesAt(TThis(_), _, _, _)
      )
    }
  }

  class ExprNode extends ClosureNode, TExprNode {
    ExprNode() { this = TExprNode(_, false) }

    Expr getExpr() { this = TExprNode(result, _) }
  }

  class ExprPostUpdateNode extends ClosureNode, TExprNode {
    ExprPostUpdateNode() { this = TExprNode(_, true) }

    Expr getExpr() { this = TExprNode(result, _) }
  }

  class ParameterNode extends ClosureNode, TParamNode {
    CapturedParameter getParameter() { this = TParamNode(result) }
  }

  class ThisParameterNode extends ClosureNode, TThisParamNode {
    Callable getCallable() { this = TThisParamNode(result) }
  }

  predicate capturePostUpdateNode(SynthesizedCaptureNode post, SynthesizedCaptureNode pre) {
    exists(CapturedVariable v, BasicBlock bb, int i |
      pre = TSynthRead(v, bb, i, false) and post = TSynthRead(v, bb, i, true)
    )
    or
    exists(BasicBlock bb, int i |
      pre = TSynthThisQualifier(bb, i, false) and post = TSynthThisQualifier(bb, i, true)
    )
  }

  private predicate step(CaptureContainer cc, BasicBlock bb1, int i1, BasicBlock bb2, int i2) {
    CaptureSsa::adjacentDefReadExt(_, cc, bb1, i1, bb2, i2)
  }

  private predicate stepToPhi(CaptureContainer cc, BasicBlock bb, int i, TSynthPhi phi) {
    exists(CaptureSsa::DefinitionExt next |
      CaptureSsa::lastRefRedefExt(_, cc, bb, i, next) and
      phi = TSynthPhi(next)
    )
  }

  private predicate ssaAccessAt(
    ClosureNode n, CaptureContainer cc, boolean isPost, BasicBlock bb, int i
  ) {
    exists(CapturedVariable v |
      synthRead(v, bb, i, true, _) and
      n = TSynthRead(v, bb, i, isPost) and
      cc = TVariable(v)
    )
    or
    n = TSynthThisQualifier(bb, i, isPost) and cc = TThis(bb.getEnclosingCallable())
    or
    exists(CaptureSsa::DefinitionExt phi |
      n = TSynthPhi(phi) and phi.definesAt(cc, bb, i, _) and isPost = false
    )
    or
    exists(VariableRead vr, CapturedVariable v |
      captureRead(v, bb, i, true, vr) and
      n = TExprNode(vr, isPost) and
      cc = TVariable(v)
    )
    or
    exists(VariableWrite vw, CapturedVariable v |
      captureWrite(v, bb, i, true, vw) and
      n = TExprNode(vw.getSource(), false) and
      isPost = false and
      cc = TVariable(v)
    )
    or
    exists(CapturedParameter p |
      entryDef(cc, bb, i) and
      cc = TVariable(p) and
      n = TParamNode(p) and
      isPost = false
    )
    or
    exists(Callable c |
      entryDef(cc, bb, i) and
      cc = TThis(c) and
      n = TThisParamNode(c) and
      isPost = false
    )
  }

  predicate localFlowStep(ClosureNode node1, ClosureNode node2) {
    exists(CaptureContainer cc, BasicBlock bb1, int i1, BasicBlock bb2, int i2 |
      step(cc, bb1, i1, bb2, i2) and
      ssaAccessAt(node1, pragma[only_bind_into](cc), _, bb1, i1) and
      ssaAccessAt(node2, pragma[only_bind_into](cc), false, bb2, i2)
    )
    or
    exists(CaptureContainer cc, BasicBlock bb, int i |
      stepToPhi(cc, bb, i, node2) and
      ssaAccessAt(node1, cc, _, bb, i)
    )
  }

  predicate storeStep(ClosureNode node1, CapturedVariable v, ClosureNode node2) {
    // store v in the closure
    exists(BasicBlock bb, int i, Expr closure |
      synthRead(v, bb, i, _, closure) and
      node1 = TSynthRead(v, bb, i, false) and
      node2 = TExprNode(closure, false)
    )
    or
    // write to v inside the closure body
    exists(BasicBlock bb, int i, VariableWrite vw |
      captureWrite(v, bb, i, false, vw) and
      node1 = TExprNode(vw.getSource(), false) and
      node2 = TSynthThisQualifier(bb, i, true)
    )
  }

  predicate readStep(ClosureNode node1, CapturedVariable v, ClosureNode node2) {
    // read v from the closure post-update to observe side-effects
    exists(BasicBlock bb, int i, Expr closure |
      synthRead(v, bb, i, _, closure) and
      node1 = TExprNode(closure, true) and
      node2 = TSynthRead(v, bb, i, true)
    )
    or
    // read v from the closure inside the closure body
    exists(BasicBlock bb, int i | node1 = TSynthThisQualifier(bb, i, false) |
      synthRead(v, bb, i, false, _) and
      node2 = TSynthRead(v, bb, i, false)
      or
      exists(VariableRead vr |
        captureRead(v, bb, i, false, vr) and
        node2 = TExprNode(vr, false)
      )
    )
  }
}
