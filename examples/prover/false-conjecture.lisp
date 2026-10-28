; examples/prover/false-conjecture.lisp
;
; What it shows: a failed proof whose key checkpoint is not a theorem, so the
; conjecture is false; ground evaluation finds the counterexample in one form;
; the corrected statement proves without hints.
;
; Cited by humans/01-logic-and-prover.md, "When the goal is false".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun tk (n x)
  (if (zp n)
      nil
    (cons (car x) (tk (1- n) (cdr x)))))

; The intended theorem: taking N of the first M is taking (min N M).  It fails,
; and among its key checkpoints is
;   (IMPLIES (AND (INTEGERP N) (<= 0 N) (NOT (INTEGERP M)))
;            (NOT (TK N NIL)))
; which is false for N = 1: (tk 1 nil) is (nil).
(local
 (must-fail
  (with-prover-step-limit 200000
    (thm (equal (tk n (tk m x))
                (tk (min (nfix n) (nfix m)) x))))))

; Ground evaluation confirms the counterexample before any more proof work:
; TK pads with NIL when the list runs out, so taking more than was taken is not
; a no-op.
(assert-event (equal (tk 2 (tk 0 '(a b))) '(nil nil)))
(assert-event (not (equal (tk 2 (tk 0 '(a b)))
                          (tk (min 2 0) '(a b)))))

; The corrected statement restricts N to at most M, and proves without hints.
(defthm tk-of-tk-when-not-longer
  (implies (and (natp n) (natp m) (<= n m))
           (equal (tk n (tk m x))
                  (tk n x))))
