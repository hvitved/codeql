signature predicate hasSourceLocationPrefixSig(string prefix);

bindingset[relativePath, startLine, startColumn, endLine, endColumn]
signature predicate excludeSig(
  string relativePath, int startLine, int startColumn, int endLine, int endColumn
);

signature predicate diffSig(
  string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
  int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
  int endLineTarget, int endColumnTarget
);

module LspComparison<
  hasSourceLocationPrefixSig/1 hasSourceLocationPrefix, excludeSig/5 exclude, diffSig/10 lsp,
  diffSig/10 ql>
{
  private predicate lspAdj(
    string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
    int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
    int endLineTarget, int endColumnTarget
  ) {
    // adjust column endings
    lsp(relativePathSource, startLineSource, startColumnSource, endLineSource, endColumnSource + 1,
      relativePathTarget, startLineTarget, startColumnTarget, endLineTarget, endColumnTarget + 1)
  }

  private newtype TDiffEntity =
    MkDiffEntity(string relativePath, int startLine, int startColumn, int endLine, int endColumn) {
      not exclude(relativePath, startLine, startColumn, endLine, endColumn) and
      (
        lspAdj(relativePath, startLine, startColumn, endLine, endColumn, _, _, _, _, _)
        or
        lspAdj(_, _, _, _, _, relativePath, startLine, startColumn, endLine, endColumn)
        or
        ql(relativePath, startLine, startColumn, endLine, endColumn, _, _, _, _, _)
        or
        ql(_, _, _, _, _, relativePath, startLine, startColumn, endLine, endColumn)
      )
    }

  class DiffEntity extends MkDiffEntity {
    string toString() {
      exists(string relativePath, int startLine, int startColumn, int endLine, int endColumn |
        this = MkDiffEntity(relativePath, startLine, startColumn, endLine, endColumn) and
        result =
          relativePath + ":" + startLine + ":" + startColumn + "-" + endLine + ":" + endColumn
      )
    }

    predicate hasLocationInfo(
      string filepath, int startLine, int startColumn, int endLine, int endColumn
    ) {
      exists(string relativePath, string prefix |
        this = MkDiffEntity(relativePath, startLine, startColumn, endLine, endColumn) and
        hasSourceLocationPrefix(prefix) and
        filepath = prefix + "/" + relativePath
      )
    }

    DiffEntity getOnSameLine() {
      exists(string relativePath, int startLine, int startColumn, int endLine, int endColumn |
        this = MkDiffEntity(relativePath, startLine, startColumn, endLine, endColumn) and
        result = MkDiffEntity(relativePath, startLine, _, endLine, _)
      )
    }
  }

  private newtype TDiffEntityModColumns =
    MkDiffEntityModColumns(string relativePath, int startLine, int endLine) {
      exists(MkDiffEntity(relativePath, startLine, _, endLine, _))
    }

  class DiffEntityModColumns extends MkDiffEntityModColumns {
    string toString() {
      exists(string relativePath, int startLine, int endLine |
        this = MkDiffEntityModColumns(relativePath, startLine, endLine) and
        result = relativePath + ":" + startLine + "-" + endLine
      )
    }

    predicate hasLocationInfo(
      string filepath, int startLine, int startColumn, int endLine, int endColumn
    ) {
      exists(string relativePath, string prefix |
        this = MkDiffEntityModColumns(relativePath, startLine, endLine) and
        hasSourceLocationPrefix(prefix) and
        filepath = prefix + "/" + relativePath and
        startColumn = min(int c | MkDiffEntity(_, _, c, _, _) = this.getADiffEntity()) and
        endColumn = max(int c | MkDiffEntity(_, _, _, _, c) = this.getADiffEntity())
      )
    }

    DiffEntity getADiffEntity() {
      exists(string relativePath, int startLine, int endLine |
        this = MkDiffEntityModColumns(relativePath, startLine, endLine) and
        result = MkDiffEntity(relativePath, startLine, _, endLine, _)
      )
    }
  }

  private predicate lsp(DiffEntity source, DiffEntity target) {
    exists(
      string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
      int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
      int endLineTarget, int endColumnTarget
    |
      lspAdj(relativePathSource, startLineSource, startColumnSource, endLineSource, endColumnSource,
        relativePathTarget, startLineTarget, startColumnTarget, endLineTarget, endColumnTarget) and
      source =
        MkDiffEntity(relativePathSource, startLineSource, startColumnSource, endLineSource,
          endColumnSource) and
      target =
        MkDiffEntity(relativePathTarget, startLineTarget, startColumnTarget, endLineTarget,
          endColumnTarget) and
      not target = source.getOnSameLine()
    )
  }

  private predicate lspModColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    lsp(source.getADiffEntity(), target.getADiffEntity())
  }

  private predicate ql(DiffEntity source, DiffEntity target) {
    exists(
      string relativePathSource, int startLineSource, int startColumnSource, int endLineSource,
      int endColumnSource, string relativePathTarget, int startLineTarget, int startColumnTarget,
      int endLineTarget, int endColumnTarget
    |
      ql(relativePathSource, startLineSource, startColumnSource, endLineSource, endColumnSource,
        relativePathTarget, startLineTarget, startColumnTarget, endLineTarget, endColumnTarget) and
      source =
        MkDiffEntity(relativePathSource, startLineSource, startColumnSource, endLineSource,
          endColumnSource) and
      target =
        MkDiffEntity(relativePathTarget, startLineTarget, startColumnTarget, endLineTarget,
          endColumnTarget) and
      not target = source.getOnSameLine()
    )
  }

  private predicate qlModColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    ql(source.getADiffEntity(), target.getADiffEntity())
  }

  query predicate both(DiffEntity source, DiffEntity target) {
    lsp(source, target) and
    ql(source, target)
  }

  query predicate bothModuloColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    lspModColumns(source, target) and
    qlModColumns(source, target)
  }

  query predicate onlyLsp(DiffEntity source, DiffEntity target) {
    lsp(source, target) and
    not ql(source, target)
  }

  query predicate onlyLspModuloColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    lspModColumns(source, target) and
    not qlModColumns(source, target)
  }

  query predicate uniqueLsp(DiffEntity source, DiffEntity target) {
    lsp(source, target) and
    not ql(source, _)
  }

  query predicate uniqueLspModuloColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    lspModColumns(source, target) and
    not qlModColumns(source, _)
  }

  query predicate onlyQl(DiffEntity source, DiffEntity target) {
    not lsp(source, target) and
    ql(source, target)
  }

  query predicate onlyQlModuloColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    not lspModColumns(source, target) and
    qlModColumns(source, target)
  }

  query predicate uniqueQl(DiffEntity source, DiffEntity target) {
    not lsp(source, _) and
    ql(source, target)
  }

  query predicate uniqueQlModuloColumns(DiffEntityModColumns source, DiffEntityModColumns target) {
    not lspModColumns(source, _) and
    qlModColumns(source, target)
  }

  query predicate diffCount(string cat, int c) {
    cat = "both" and
    c = count(DiffEntity source, DiffEntity target | both(source, target))
    or
    cat = "both (modulo columns)" and
    c =
      count(DiffEntityModColumns source, DiffEntityModColumns target |
        bothModuloColumns(source, target)
      )
    or
    cat = "only LSP" and
    c = count(DiffEntity source, DiffEntity target | onlyLsp(source, target))
    or
    cat = "only LSP (modulo columns)" and
    c =
      count(DiffEntityModColumns source, DiffEntityModColumns target |
        onlyLspModuloColumns(source, target)
      )
    or
    cat = "unique LSP" and
    c = count(DiffEntity source, DiffEntity target | uniqueLsp(source, target))
    or
    cat = "unique LSP (modulo columns)" and
    c =
      count(DiffEntityModColumns source, DiffEntityModColumns target |
        uniqueLspModuloColumns(source, target)
      )
    or
    cat = "only QL" and
    c = count(DiffEntity source, DiffEntity target | onlyQl(source, target))
    or
    cat = "only QL (modulo columns)" and
    c =
      count(DiffEntityModColumns source, DiffEntityModColumns target |
        onlyQlModuloColumns(source, target)
      )
    or
    cat = "unique QL" and
    c = count(DiffEntity source, DiffEntity target | uniqueQl(source, target))
    or
    cat = "unique QL (modulo columns)" and
    c =
      count(DiffEntityModColumns source, DiffEntityModColumns target |
        uniqueQlModuloColumns(source, target)
      )
  }
}
