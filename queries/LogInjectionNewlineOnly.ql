/**
 * @name Log injection: only newline characters removed
 * @description Untrusted data reaches a log call after a replacement that removes
 *              only `\n`. Carriage returns (`\r`) survive, so a log entry can still
 *              be split or forged wherever `\r` acts as a line break. The standard
 *              query treats this replacement as a complete sanitizer and stays silent.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id thesis/log-injection-newline-only
 * @tags security
 *       external/cwe/cwe-117
 */

import javascript
import semmle.javascript.security.dataflow.LogInjectionQuery as Std

/**
 * A replacement that the standard query accepts as a full sanitizer
 * but that does not also remove `\r`.
 */
class NewlineOnlyReplace extends Std::StringReplaceSanitizer {
  NewlineOnlyReplace() { not this.(StringReplaceCall).getAReplacedString() = "\r" }
}

/** Untrusted data that reaches the receiver of a newline-only replacement. */
module ReachesReplaceConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node n) { n instanceof Std::Source }

  predicate isSink(DataFlow::Node n) {
    n = any(NewlineOnlyReplace r).(DataFlow::MethodCallNode).getReceiver()
  }

  predicate isBarrier(DataFlow::Node n) { n instanceof Std::Sanitizer }
}

module ReachesReplace = TaintTracking::Global<ReachesReplaceConfig>;

/** Data that leaves a newline-only replacement and reaches a log sink. */
module AfterReplaceConfig implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node n) {
    n instanceof NewlineOnlyReplace and
    ReachesReplace::flow(_, n.(DataFlow::MethodCallNode).getReceiver())
  }

  predicate isSink(DataFlow::Node n) { n instanceof Std::Sink }

  predicate isBarrier(DataFlow::Node n) {
    // any other standard sanitizer, or a later replacement that also removes \r
    n instanceof Std::Sanitizer and not n instanceof NewlineOnlyReplace
    or
    n.(StringReplaceCall).getAReplacedString() = "\r"
  }
}

module AfterReplace = TaintTracking::Global<AfterReplaceConfig>;

from DataFlow::Node replace, DataFlow::Node sink
where AfterReplace::flow(replace, sink)
select sink,
  "Log entry built from $@ that has had only newline characters removed; carriage returns can still forge log lines.",
  replace, "this replacement"
