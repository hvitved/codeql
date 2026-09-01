import utils.test.InlineExpectationsTest
import utils.test.TestUtils
import codeql.unified.internal.typeinference.Type
import codeql.unified.internal.typeinference.TypeInference as TypeInference
import codeql.unified.internal.StaticNameBinding
import TypeInference

private predicate relevantNode(AstNode n) { n.fromSource() }

query predicate inferCertainType(AstNode n, TypePath path, Type t) {
  t = TypeInference::inferTypeCertain(n, path) and
  not t instanceof PseudoType and
  relevantNode(n)
}

query predicate inferType(AstNode n, TypePath path, Type t) {
  t = TypeInference::inferType(n, path) and
  not t instanceof PseudoType and
  relevantNode(n)
}

module ResolveTest implements TestSig {
  string getARelevantTag() { result = "target" }

  predicate hasActualResult(Location location, string element, string tag, string value) {
    exists(NameBinding b, CallExpr access |
      b = resolveCallTarget(access) and
      location = access.getLocation() and
      element = access.toString() and
      nameBinding(b, value) and
      tag = "target"
    )
  }
}

import MakeTest<MergeTests<ResolveTest, TypeInference::TypeTest>>
