/**
 * @kind table
 * @id js/lsp-comparison/jump-to-definition
 */

import javascript
import codeql.util.internal.LspComparison
import definitions
import Extensions

private predicate jumpToDefQl(
  string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
  int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
  int endLineTarget, int endColumnTarget
) {
  exists(Locatable e, AstNode def |
    def = definitionOf(e, _) and
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
  not extracted(relativePath)
  or
  not jumpToDef(relativePath, _, _, _, _, _, _, _, _, _) and
  not jumpToDef(_, _, _, _, _, relativePath, _, _, _, _)
  or
  exists(Token t |
    t.getValue() = ["function", "this", "module", "exports", "return"] and
    relativePath = t.getFile().getRelativePath() and
    t.getLocation().hasLocationInfo(_, startLine, startColumn, endLine, endColumn)
  )
  or
  exists(TopLevel tl |
    tl.isMinified() and
    relativePath = tl.getFile().getRelativePath()
  )
}

import LspComparison<sourceLocationPrefix/1, exclude/5, jumpToDef/10, jumpToDefQl/10>
