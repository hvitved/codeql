private import semmle.code.csharp.dataflow.internal.FlowSummaryImpl as FlowSummaryImpl
private import semmle.code.csharp.dataflow.internal.ExternalFlow
import shared.FlowSummaries

private class IncludeAllSummarizedCallable extends IncludeSummarizedCallable {
  IncludeAllSummarizedCallable() { exists(this) }

  private predicate sdfs(
    string s, SummaryComponentStack input, SummaryComponentStack output, boolean preservesValue
  ) {
    this.getQualifiedName() = "Microsoft.AspNetCore.Connections.ConnectionItems.Add" and
    s = this.getCallableCsv() and
    this.propagatesFlow(input, output, preservesValue)
  }

  private predicate sdfs2(string s) {
    this.getQualifiedName() = "Microsoft.AspNetCore.Connections.ConnectionItems.Add" and
    s = this.getCallableCsv()
  }
  // namespace = "Microsoft.AspNetCore.Connections" and
  //   type = "ConnectionItems" and
  //   name = "Add" and
}

private class IncludeNeutralSummarizedCallable extends RelevantNeutralCallable instanceof FlowSummaryImpl::Public::NeutralSummaryCallable
{
  /** Gets a string representing the callable in semi-colon separated format for use in flow summaries. */
  final override string getCallableCsv() { result = asPartialNeutralModel(this) }
}
