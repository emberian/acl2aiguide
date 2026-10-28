; examples/prover/rule-classes-nil-use.lisp
;
; What it shows: a theorem stored with :rule-classes nil generates no rule,
; so it changes no later proof by itself; it is cited by name in a :use hint
; exactly where it is wanted.  This is fn's convention for guard-proof
; equalities (fn docs/proof-style.md section 3).
;
; Cited by humans/01-logic-and-prover.md, "The hints: :use" and
; humans/02-rewriting-theories-books.md, ":rule-classes nil".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun mag (x) (if (< x 0) (- x) x))
(in-theory (disable mag))

(defthm mag-bound
  (implies (rationalp x) (<= 0 (mag x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mag))))

; No rule: the database does not know MAG-BOUND.
(local
 (must-fail
  (thm (implies (rationalp y) (<= 0 (+ (mag y) (mag y)))))))

; Named where needed, instantiated to the variable of this goal.
(defthm twice-mag-non-negative
  (implies (rationalp y) (<= 0 (+ (mag y) (mag y))))
  :hints (("Goal" :use ((:instance mag-bound (x y))))))
