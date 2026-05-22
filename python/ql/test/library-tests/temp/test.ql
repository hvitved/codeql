/**
 * @kind path-problem
 * @id broken-python-kwargs
 */

import python
import semmle.python.ApiGraphs
import semmle.python.Concepts
import semmle.python.dataflow.new.TaintTracking

module KwArgsFlow implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {
    exists(Call call, Name name |
      // call is to source
      call.getFunc() = name and
      name.getId() = "source" and
      // node is the returned value
      call = node.asExpr()
    )
  }

  predicate isSink(DataFlow::Node node) {
    exists(Call call, Name name |
      // call is to a sink
      call.getFunc() = name and
      name.getId() in ["sink", "sink2"] and
      // node is an arg or kwarg
      (
        call.getAnArg() = node.asExpr() or
        call.getKwargs() = node.asExpr()
      )
    )
  }
}

module Flow = TaintTracking::Global<KwArgsFlow>;

import Flow::PathGraph

from Flow::PathNode input, Flow::PathNode output
where Flow::flowPath(input, output)
select output.getNode(), input, output, "This does not work"
