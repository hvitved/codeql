/**
 * @name Missing XML validation
 * @description User input should not be processed as XML without validating it against a known
 *              schema.
 * @kind path-problem
 * @problem.severity recommendation
 * @security-severity 4.3
 * @precision high
 * @id cs/xml/missing-validation
 * @tags security
 *       external/cwe/cwe-112
 */

import csharp
import semmle.code.csharp.security.dataflow.MissingXMLValidationQuery
import MissingXmlValidation::PathGraph

predicate stageStats = MissingXmlValidation::stageStats/10;

predicate results(string s, int i) {
  s = "edges" and
  i =
    strictcount(MissingXmlValidation::PathNode n1, MissingXmlValidation::PathNode n2 |
      edges(n1, n2, _, _)
    )
  or
  s = "subpaths" and
  i =
    strictcount(MissingXmlValidation::PathNode n1, MissingXmlValidation::PathNode n2,
      MissingXmlValidation::PathNode n3, MissingXmlValidation::PathNode n4 |
      subpaths(n1, n2, n3, n4)
    )
}

from MissingXmlValidation::PathNode source, MissingXmlValidation::PathNode sink
where MissingXmlValidation::flowPath(source, sink)
select sink.getNode(), source, sink,
  "This XML processing depends on a $@ without validation because " +
    sink.getNode().(Sink).getReason(), source.getNode(), "user-provided value"
