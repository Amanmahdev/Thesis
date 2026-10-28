/**
 * @name Prototype pollution: property key sanitized by deleting a substring
 * @description A property key is "sanitized" by deleting `__proto__` (or a similar
 *              route key) with `replace`. Deletion is not recursive, so input such as
 *              `__pro__proto__to__` rebuilds the dangerous key, and the other routes
 *              (`constructor.prototype`) are not handled at all. The standard
 *              prototype pollution queries report nothing for this pattern.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id thesis/prototype-pollution-key-removal
 * @tags security
 *       external/cwe/cwe-1321
 */

import javascript

from DataFlow::PropWrite write, StringReplaceCall rep, string dangerous
where
  dangerous = ["__proto__", "constructor", "prototype"] and
  rep.getAReplacedString() = dangerous and
  rep.getRawReplacement().getStringValue() = "" and
  rep.flowsTo(write.getPropertyNameExpr().flow())
select rep,
  "Property key is sanitized by deleting '" + dangerous +
    "'; deletion is not recursive and does not close the other prototype routes, " +
    "so the key written $@ can still reach Object.prototype.", write, "here"
