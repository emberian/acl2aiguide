; examples/rewriting/forward-chaining.lisp
;
; What it shows: the :doc forward-chaining example made certifiable.  A rule
; (implies (q1 x) (q2 y)) has the free variable X; as a rewrite rule nothing
; binds it.  Stating (implies (q0 x) (q1 x)) as a :rewrite rule does not help
; (the rewriter is never asked about (q1 x) for a specific x), but as a
; :forward-chaining rule it puts (q1 x) into the context, where the free
; variable search finds it.
;
; Cited by humans/02-rewriting-theories-books.md, ":forward-chaining".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  (((q0 *) => *) ((q1 *) => *) ((q2 *) => *))
  (local (defun q0 (x) (declare (ignore x)) t))
  (local (defun q1 (x) (declare (ignore x)) t))
  (local (defun q2 (x) (declare (ignore x)) t))
  (defthm q0-implies-q1
    (implies (q0 x) (q1 x))
    :rule-classes nil)
  (defthm q1-implies-q2
    (implies (q1 x) (q2 y))))

; As a rewrite rule, Q0->Q1 is never triggered: no (q1 ...) term is rewritten.
(defthm q0-implies-q1-rewrite
  (implies (q0 x) (q1 x))
  :hints (("Goal" :use q0-implies-q1)))

(local
 (must-fail
  (thm (implies (q0 x) (q2 y)))))

(in-theory (disable q0-implies-q1-rewrite))

; As a forward-chaining rule, (q0 x) in the hypotheses adds (q1 x) to the
; context before rewriting begins.
(defthm q0-implies-q1-forward
  (implies (q0 x) (q1 x))
  :rule-classes :forward-chaining
  :hints (("Goal" :use q0-implies-q1)))

(defthm q0-implies-q2
  (implies (q0 x) (q2 y))
  :rule-classes nil)
