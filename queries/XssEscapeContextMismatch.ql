/**
 * @name XSS: HTML escaping that does not protect the output context
 * @description A value is HTML-escaped by hand (replace chain or helper function) and then
 *              placed in a context that the escaping does not protect: an attribute whose
 *              delimiting quote is not escaped, or a URL attribute (`href`, `src`, `action`)
 *              where escaping cannot stop `javascript:` URLs. The standard XSS queries treat
 *              any global replacement of `<`, `'` or `"` as a full sanitizer for every context,
 *              so they stay silent. Escaping done by a known library (for example `escape-html`)
 *              is assumed complete and is not reported.
 * @kind problem
 * @problem.severity warning
 * @precision medium
 * @id thesis/xss-escape-context-mismatch
 * @tags security
 *       external/cwe/cwe-079
 */

import javascript

/** A replace call in the chain of replacements that ends at `top`. */
StringReplaceCall chainMember(StringReplaceCall top) {
  result = top
  or
  result = chainMember(top).getReceiver().getALocalSource()
}

/**
 * Holds if the character `c` is replaced by an escaping step whose result flows into `n`,
 * either directly or through the return value of a helper function.
 */
predicate escapes(DataFlow::Node n, string c) {
  exists(StringReplaceCall top |
    top.flowsTo(n) and
    c = chainMember(top).getAReplacedString()
  )
  or
  exists(DataFlow::CallNode call, Function f, StringReplaceCall top |
    call.flowsTo(n) and
    f = call.getACallee() and
    top.flowsToExpr(f.getAReturnedExpr()) and
    c = chainMember(top).getAReplacedString()
  )
}

/** Holds if `n` has been through some HTML-escaping step. */
predicate htmlEscaped(DataFlow::Node n) { escapes(n, ["<", ">", "&", "\"", "'"]) }

/** Gets the quote character of the attribute value that `n` is placed in, if any. */
string attributeQuote(StringOps::ConcatenationLeaf n) {
  exists(string prev | prev = n.getPreviousLeaf().getStringValue() |
    prev.regexpMatch("(?s).*=\\s*\"") and result = "\""
    or
    prev.regexpMatch("(?s).*=\\s*'") and result = "'"
  )
}

/** Holds if `n` is placed in a URL-valued attribute. */
predicate inUrlAttribute(StringOps::ConcatenationLeaf n) {
  n.getPreviousLeaf()
      .getStringValue()
      .regexpMatch("(?s).*\\b(href|src|action|formaction)\\s*=\\s*[\"']")
}

/** Holds if code in `c` checks a URL scheme, host or format before use. */
predicate hasUrlCheck(StmtContainer c) {
  exists(StringOps::StartsWith sw | sw.getContainer() = c)
  or
  exists(MethodCallExpr m |
    m.getContainer() = c and
    m.getMethodName() = "test" and
    m.getReceiver() instanceof RegExpLiteral
  )
  or
  exists(NewExpr ne | ne.getContainer() = c and ne.getCallee().(VarAccess).getName() = "URL")
}

from StringOps::ConcatenationLeaf n, string msg
where
  htmlEscaped(n) and
  (
    exists(string q |
      q = attributeQuote(n) and
      not escapes(n, q) and
      msg =
        "Value is HTML-escaped but the escaping does not replace the " + q +
          " character that delimits the attribute it is placed in."
    )
    or
    inUrlAttribute(n) and
    not hasUrlCheck(n.getContainer()) and
    msg =
      "Value is HTML-escaped and placed in a URL attribute; escaping does not block javascript: URLs and no scheme check was found."
  )
select n, msg
