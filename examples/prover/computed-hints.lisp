; examples/prover/computed-hints.lisp
;
; What it shows: a computed hint that fires only once a goal is stable under
; simplification (:doc computed-hints), and the same hint installed for every
; later proof in the book with set-default-hints, which is local to the book
; (:doc set-default-hints).
;
; Cited by humans/01-logic-and-prover.md, "The hints: computed hints".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun mag (x) (if (< x 0) (- x) x))
(in-theory (disable mag))

(local
 (must-fail
  (thm (implies (rationalp x) (<= 0 (mag x))))))

; The hint is a term over the variables the prover binds (ID, CLAUSE, WORLD,
; STABLE-UNDER-SIMPLIFICATIONP, ...).  It returns NIL until the goal has
; settled, then a keyword/value list as if typed.
(defthm mag-non-negative
  (implies (rationalp x) (<= 0 (mag x)))
  :hints ((and stable-under-simplificationp
               '(:in-theory (enable mag)))))

; Every subsequent defthm in this book gets the hint appended to its own.
(set-default-hints '((and stable-under-simplificationp
                          '(:in-theory (enable mag)))))

(defthm mag-of-negative-input
  (implies (and (rationalp x) (< x 0))
           (equal (mag x) (- x))))
