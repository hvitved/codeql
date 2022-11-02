/**
 * Defines a graph for reasoning about dependencies between different predicates,
 * that is, whether one would force evaluation of another (unless magic).
 */

private import codeql_ql.ast.Ast

newtype TPathNode =
  MkAstNode(AstNode node) or
  MkTypeNode(Type type) { not type instanceof DontCareType }

class PathNode extends TPathNode {
  AstNode asAstNode() { this = MkAstNode(result) }

  Type asType() { this = MkTypeNode(result) }

  private string getOverrideToString() {
    exists(Predicate p | this.asAstNode() = p |
      result = p.(ClassPredicate).getDeclaringType().getName() + "." + p.getName()
      or
      result = p.(ClasslessPredicate).getName()
    )
    or
    result = this.asAstNode().(TopLevel).getFile().getRelativePath()
  }

  string toString() {
    result = this.getOverrideToString()
    or
    not exists(this.getOverrideToString()) and
    (
      result = this.asAstNode().toString()
      or
      result = this.asType().toString()
    )
  }

  /**
   * Tries to provide a more helpful location, if possible.
   */
  private Location getOverrideLocation() {
    result = this.asType().(ClassCharType).getDeclaration().getCharPred().getLocation()
  }

  predicate hasLocationInfo(
    string filepath, int startline, int startcolumn, int endline, int endcolumn
  ) {
    this.getOverrideLocation().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    or
    not exists(this.getOverrideLocation()) and
    (
      this.asType().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
      or
      this.asAstNode().hasLocationInfo(filepath, startline, startcolumn, endline, endcolumn)
    )
  }
}

private Predicate getAnOverriddenPredicate(Predicate p) { predOverrides(p, result) }

private predicate isRootDef(Predicate p) { not exists(getAnOverriddenPredicate(p)) }

private Predicate getARootDef(Predicate p) {
  result = getAnOverriddenPredicate*(p) and
  isRootDef(result)
}

private TypeExpr getABaseType(Class cls, boolean abstractExtension) {
  result = cls.getASuperType() and
  if result.getResolvedType().(ClassType).getDeclaration().isAbstract()
  then abstractExtension = true
  else abstractExtension = false
  or
  result = cls.getAnInstanceofType() and
  abstractExtension = false
}

pragma[nomagic]
predicate rawEdge(PathNode pred, PathNode succ) {
  exists(Predicate predicat | pred.asAstNode() = predicat |
    succ.asAstNode().getEnclosingPredicate() = predicat
    or
    getAnOverriddenPredicate(succ.asAstNode()) = predicat
    or
    succ.asType() = predicat.(ClassPredicate).getDeclaringType()
  )
  or
  exists(Call call |
    pred.asAstNode() = call and
    succ.asAstNode() = getARootDef(call.getTarget())
  )
  or
  exists(TypeExpr t | pred.asAstNode() = t |
    if t = getABaseType(_, true)
    then
      // When extending an abstract class, the typename in the 'extends' clause is considered to target
      // only the ClassCharType. The ClassType represents the union of concrete subtypes.
      succ.asType().(ClassCharType).getClassType() = t.getResolvedType()
    else succ.asType() = t.getResolvedType()
  )
  or
  exists(ClassType classType | pred.asType() = classType |
    // Always add an edge from ClassType to ClassCharType. For abstract class this makes the path shorter
    // and more obvious than going through an arbitrary subclass.
    succ.asType().(ClassCharType).getClassType() = classType
    or
    classType.getDeclaration().isAbstract() and
    succ.asType().(ClassType).getDeclaration().getASuperType().getResolvedType() = classType
  )
  or
  exists(ClassCharType charType, Class cls |
    pred.asType() = charType and
    cls = charType.getClassType().getDeclaration()
  |
    succ.asAstNode() = cls.getCharPred()
    or
    succ.asAstNode() = cls.getAField().getVarDecl().getTypeExpr()
    or
    succ.asAstNode() = getABaseType(cls, _)
  )
  or
  exists(UnionType t |
    pred.asType() = t and
    succ.asAstNode() = t.getDeclaration().getUnionMember()
  )
  or
  exists(NewTypeType t |
    pred.asType() = t and
    succ.asType() = t.getABranch()
  )
  or
  exists(NewTypeBranchType t |
    pred.asType() = t and
    succ.asAstNode() = t.getDeclaration() // map to the Predicate AST node
  )
  or
  exists(TopLevel top |
    pred.asAstNode() = top and
    succ.asAstNode().getFile() = top.getFile()
  )
}

private PathNode getAPredecessor(PathNode node) { rawEdge(result, node) }

private PathNode getASuccessor(PathNode node) { rawEdge(node, result) }

signature module DependencyConfig {
  /**
   * Holds if we should explore the transitive dependencies of `source`.
   */
  predicate isSource(PathNode source);

  /**
   * Holds if a transitive dependency from a source to `sink` should be reported.
   */
  predicate isSink(PathNode sink);
}

module PathGraph<DependencyConfig C> {
  private PathNode reachableFromSource() {
    C::isSource(result)
    or
    result = getASuccessor(reachableFromSource())
  }

  private PathNode reachableSink() {
    C::isSink(result) and
    result = reachableFromSource()
  }

  private PathNode relevantNode() {
    result = reachableSink()
    or
    result = getAPredecessor(relevantNode()) and
    result = reachableFromSource()
  }

  query predicate edges(PathNode pred, PathNode succ) {
    pred = relevantNode() and
    succ = relevantNode() and
    rawEdge(pred, succ)
  }

  query predicate nodes(PathNode node) { node = relevantNode() }

  predicate hasFlowPath(PathNode source, PathNode sink) {
    C::isSource(source) and
    C::isSink(sink) and
    edges+(source, sink)
  }
}
