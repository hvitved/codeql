/**
 * @kind table
 * @id py/lsp-comparison/jump-to-definition
 */

import python
import codeql.util.internal.LspComparison
import analysis.DefinitionTracking
import Extensions

private predicate jumpToDefQl(
  string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
  int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
  int endLineTarget, int endColumnTarget
) {
  exists(Expr e, Definition def |
    preferred_jump_to_defn(e, def) and
    exists(Location loc |
      loc = e.getLocation() and
      loc.hasLocationInfo(_, startLineSource, startColumnSource, endLineSource, endColumnSource) and
      relativePathSource = e.getLocation().getFile().getRelativePath()
    ) and
    exists(Location loc |
      loc = def.getLocation() and
      loc.hasLocationInfo(_, startLineTarget, startColumnTarget, endLineTarget, endColumnTarget) and
      relativePathTarget = def.getLocation().getFile().getRelativePath()
    )
  )
}

private predicate extracted(string relativePath) { relativePath = any(File f).getRelativePath() }

bindingset[relativePath, startLine, startColumn, endLine, endColumn]
predicate exclude(string relativePath, int startLine, int startColumn, int endLine, int endColumn) {
  not extracted(relativePath) and
  exists(startLine) and
  exists(startColumn) and
  exists(endLine) and
  exists(endColumn)
  or
  not jumpToDef(relativePath, _, _, _, _, _, _, _, _, _) and
  not jumpToDef(_, _, _, _, _, relativePath, _, _, _, _)
}

predicate jumpToDefLsp(
  string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
  int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
  int endLineTarget, int endColumnTarget
) {
  jumpToDef(relativePathSource, startLineSource, startColumnSource, endLineSource, endColumnSource,
    relativePathTarget, startLineTarget, startColumnTarget, endLineTarget, endColumnTarget) and
  not exists(AstNode n |
    relativePathSource = n.getLocation().getFile().getRelativePath() and
    n.getLocation()
        .hasLocationInfo(_, startLineSource, startColumnSource, endLineSource, endColumnSource - 1)
  |
    // The Python LSP server generates jump-to-refs for parameters and variables, exclude them
    n instanceof Parameter
    or
    n = any(AssignStmt a).getATarget()
  )
}

import LspComparison<sourceLocationPrefix/1, exclude/5, jumpToDefLsp/10, jumpToDefQl/10>
