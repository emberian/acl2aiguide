; examples/books/defattach-exec.lisp
;
; What it shows: a constrained function cannot be evaluated; defattach
; attaches an executable function that satisfies its constraint, after which
; calls evaluate (outside proofs) through the attachment.  Proofs still see
; only the constraint: ground terms are not evaluated with attachments during
; proofs (:doc defattach).
;
; Cited by humans/02-rewriting-theories-books.md, "encapsulate, constrained
; functions, defattach".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  (((better * *) => *))
  (local (defun better (x y) (declare (ignore x y)) t))
  (defthm booleanp-of-better
    (booleanp (better x y))
    :rule-classes :type-prescription))

; A generic "best element" over the constrained order.
(defun best (x)
  (cond ((atom x) nil)
        ((atom (cdr x)) (car x))
        (t (let ((b (best (cdr x))))
             (if (better (car x) b) (car x) b)))))

; Generic theorem, from the constraint: the best element is a member.
(defthm member-of-best
  (implies (consp x)
           (member-equal (best x) x)))

; Before an attachment, evaluation stops at the constrained call.
(local
 (must-fail
  (assert-event (equal (best '(3 1 2)) 3))
  :expected :any))

(defun greater-rationalp (x y)
  (declare (xargs :guard t))
  (and (rationalp x) (rationalp y) (> x y)))

; The proof obligation is the constraint: GREATER-RATIONALP is Boolean.
(defattach better greater-rationalp)

(assert-event (equal (best '(3 1 2)) 3))

; In a proof the attachment is not used: this ground fact is not provable.
(local
 (must-fail
  (thm (equal (best '(3 1 2)) 3))))
