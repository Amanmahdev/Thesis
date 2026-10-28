/**
 * @name Prototype pollution: deny-list guard closes only one route
 * @description A dynamic property write is protected by a deny-list that names some
 *              of `__proto__`, `constructor` and `prototype`, but not enough to close
 *              both routes to Object.prototype. A complete guard needs `__proto__`
 *              plus either `constructor` or `prototype`. Recognises equality tests,
 *              array `includes`/`indexOf`, string `includes`/`indexOf`, and regular
 *              expression `test`/`match`. Intended as the guard-adequacy check for
 *              labelling; it adds no recall over the standard query for equality guards.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id thesis/prototype-pollution-denylist-incomplete
 * @tags security
 *       external/cwe/cwe-1321
 */

import javascript

/** Holds if `e` tests variable `v` against the string `lit` as a deny-list entry. */
predicate denyListEntry(Variable v, string lit, Expr e) {
  // v === "lit", v == "lit", in either order
  exists(EqualityTest t |
    e = t and
    t.getAnOperand().(VarAccess).getVariable() = v and
    t.getAnOperand().getStringValue() = lit
  )
  or
  // ["lit", ...].includes(v) / .indexOf(v)
  exists(MethodCallExpr c |
    e = c and
    c.getMethodName() = ["includes", "indexOf"] and
    c.getArgument(0).(VarAccess).getVariable() = v and
    c.getReceiver().(ArrayExpr).getAnElement().getStringValue() = lit
  )
  or
  // v.includes("lit") / v.indexOf("lit")
  exists(MethodCallExpr c |
    e = c and
    c.getMethodName() = ["includes", "indexOf"] and
    c.getReceiver().(VarAccess).getVariable() = v and
    c.getArgument(0).getStringValue() = lit
  )
  or
  // /re/.test(v)
  exists(MethodCallExpr c |
    e = c and
    c.getMethodName() = "test" and
    c.getArgument(0).(VarAccess).getVariable() = v and
    c.getReceiver().(RegExpLiteral).getRoot().getAChild*().(RegExpConstant).getValue() = lit
  )
  or
  // v.match(/re/)
  exists(MethodCallExpr c |
    e = c and
    c.getMethodName() = "match" and
    c.getReceiver().(VarAccess).getVariable() = v and
    c.getArgument(0).(RegExpLiteral).getRoot().getAChild*().(RegExpConstant).getValue() = lit
  )
}

/** Holds if function `f` deny-lists `lit` for key variable `v`. */
predicate covers(Function f, Variable v, string lit) {
  exists(Expr e | denyListEntry(v, lit, e) and e.getEnclosingFunction() = f)
}

from DataFlow::PropWrite write, Function f, Variable v, Expr guard, string lit
where
  write.getPropertyNameExpr().(VarAccess).getVariable() = v and
  write.getContainer() = f and
  lit = ["__proto__", "constructor", "prototype"] and
  denyListEntry(v, lit, guard) and
  guard.getEnclosingFunction() = f and
  not (covers(f, v, "__proto__") and (covers(f, v, "constructor") or covers(f, v, "prototype")))
select guard,
  "Deny-list for property key '" + v.getName() +
    "' names '" + lit + "' but does not close both routes to Object.prototype (needs '__proto__' plus 'constructor' or 'prototype'); key is written $@.",
  write, "here"
