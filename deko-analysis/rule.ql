/**
 * @name Deko IFC Violation detection
 * @description Tracks sensitive data flow to public sinks without sanitization.
 * @kind path-problem
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import semmle.code.cpp.dataflow.new.TaintTracking

module DekoIFCConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node source) {
    exists(FunctionCall call |
      call.getTarget().getName() = "read_sensitive" and
      source.asExpr() = call
    )
  }

  predicate isSink(DataFlow::Node sink) {
    exists(FunctionCall call |
      call.getTarget().getName() = "network_send" and
      sink.asExpr() = call.getArgument(1)
    )
  }
}

module DekoFlow = TaintTracking::Global<DekoIFCConfig>;

from DekoFlow::PathNode source, DekoFlow::PathNode sink
where DekoFlow::flowPath(source, sink)
select sink.getNode(), source, sink, "Found a flow from source to sink."
