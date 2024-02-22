/**
 * @name Print CFG
 * @description Produces a representation of a file's Control Flow Graph.
 *              This query is used by the VS Code extension.
 * @id cs/print-cfg
 * @kind graph
 * @tags ide-contextual-queries/print-cfg
 */

private import semmle.code.csharp.controlflow.internal.ControlFlowGraphImpl
private import TestOutput
private import IDEContextual

external string selectedSourceFile();

external string selectedSourceLine();

external string selectedSourceColumn();

private predicate cfgScopeSpan(
  CfgScope scope, File file, int startLine, int startColumn, int endLine, int endColumn
) {
  file = scope.getFile() and
  scope.getLocation().getStartLine() = startLine and
  scope.getLocation().getStartColumn() = startColumn and
  exists(Location loc |
    loc.getEndLine() = endLine and
    loc.getEndColumn() = endColumn
  |
    loc = scope.(Callable).getBody().getLocation()
    or
    loc = scope.(Field).getInitializer().getLocation()
    or
    loc = scope.(Property).getInitializer().getLocation()
  )
}

bindingset[file, line, column]
private CfgScope smallestEnclosingScope(File file, int line, int column) {
  result =
    min(CfgScope scope, int startLine, int startColumn, int endLine, int endColumn |
      cfgScopeSpan(scope, file, startLine, startColumn, endLine, endColumn) and
      (
        startLine < line
        or
        startLine = line and startColumn <= column
      ) and
      (
        endLine > line
        or
        endLine = line and endColumn >= column
      )
    |
      scope order by startLine desc, startColumn desc, endLine, endColumn
    )
}

class MyRelevantNode extends RelevantNode {
  MyRelevantNode() {
    this.getScope() =
      smallestEnclosingScope(getFileBySourceArchiveName(selectedSourceFile()),
        selectedSourceLine().toInt(), selectedSourceColumn().toInt())
  }
}
