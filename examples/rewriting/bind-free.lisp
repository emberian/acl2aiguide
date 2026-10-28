; examples/rewriting/bind-free.lisp
;
; What it shows: a free variable that no search can bind (the fact that would
; bind it is a rewrite rule with variables on its left-hand side, not a fact
; in the context), and the repair: a bind-free hypothesis that proposes
; candidate bindings computed from the term (:doc bind-free, adapted from its
; "list of alists" example).
;
; Cited by humans/02-rewriting-theories-books.md, "Free variables".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  (((hi *) => *)
   ((lo * *) => *))
  (local (defun hi (x) (declare (ignore x)) t))
  (local (defun lo (x y) (equal y (cons x 4))))
  (defthm lo-implies-hi
    (implies (lo x y) (hi x)))
  (defthm lo-of-cons-4
    (lo v (cons v 4))))

; LO-IMPLIES-HI needs some Y with (lo a y).  The context is empty, and
; LO-OF-CONS-4 is not a ground fact, so Y is never bound.
(local
 (must-fail
  (thm (hi a))))

; Candidate bindings for Y, as terms.  BIND-FREE tries each alist in turn.
(defun lo-candidates (x)
  (declare (xargs :guard t))
  (list (list (cons 'y (list 'cons x ''3)))
        (list (cons 'y (list 'cons x ''4)))))

(defthm lo-implies-hi-with-candidates
  (implies (and (bind-free (lo-candidates x) (y))
                (lo x y))
           (hi x)))

; Y = (cons a 3) fails, Y = (cons a 4) is relieved by LO-OF-CONS-4.
(defthm hi-of-anything
  (hi a)
  :rule-classes nil)
