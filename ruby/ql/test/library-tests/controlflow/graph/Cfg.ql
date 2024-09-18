import codeql.ruby.CFG

class MyRelevantNode extends CfgNode {
  string getOrderDisambiguation() { none() }
}

import codeql.ruby.controlflow.internal.ControlFlowGraphImpl::TestOutput<MyRelevantNode>
