; examples/rewriting/compound-recognizer.lisp
;
; What it shows: a :compound-recognizer rule tells type reasoning which
; primitive types a recognizer implies, so that assuming (smallp x) gives
; (integerp x) for relieving a hypothesis.  The tau system can derive the same
; fact on its own, so the demonstration turns tau off; with tau on, the
; failing form below succeeds even without the rule (as does the :doc
; compound-recognizer example with NATP-COMPOUND-RECOGNIZER disabled, on ACL2
; 8.7).
;
; Cited by humans/02-rewriting-theories-books.md, ":compound-recognizer" and
; "The tau system".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun smallp (x) (and (natp x) (< x 10)))
(defun dbl (x) (* 2 x))

(defthm dbl-preserves-integerp
  (implies (integerp x) (integerp (dbl x))))

(in-theory (disable smallp dbl))

; With tau off and no compound-recognizer rule, (integerp x) is not known from
; (smallp x), and DBL-PRESERVES-INTEGERP cannot fire.
(local
 (must-fail
  (thm (implies (smallp x) (integerp (dbl x)))
       :hints (("Goal" :in-theory (disable (tau-system)))))))

; With tau on (the default) the same goal proves without any rule about SMALLP.
(defthm dbl-of-smallp-by-tau
  (implies (smallp x) (integerp (dbl x)))
  :rule-classes nil)

(defthm smallp-compound-recognizer
  (implies (smallp x)
           (and (integerp x) (<= 0 x)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable smallp))))

; And with tau off, the compound recognizer does the job.
(defthm dbl-of-smallp-by-type-reasoning
  (implies (smallp x) (integerp (dbl x)))
  :hints (("Goal" :in-theory (disable (tau-system))))
  :rule-classes nil)
