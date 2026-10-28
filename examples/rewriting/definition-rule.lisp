; examples/rewriting/definition-rule.lisp
;
; What it shows: a :definition rule, an alternative definition proved as a
; theorem and used the way definitions are used (opened under the expansion
; heuristics).  With the original definition disabled, the rule opens CNT2
; two elements at a time (:doc definition).
;
; Cited by humans/02-rewriting-theories-books.md, ":definition".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun cnt2 (x)
  (if (consp x) (+ 1 (cnt2 (cdr x))) 0))

(defthm cnt2-by-twos
  (equal (cnt2 x)
         (if (consp x)
             (if (consp (cdr x))
                 (+ 2 (cnt2 (cddr x)))
               1)
           0))
  :rule-classes :definition)

(in-theory (disable (:definition cnt2)))

(defthm cnt2-of-two-or-more
  (implies (and (consp x) (consp (cdr x)))
           (equal (cnt2 x) (+ 2 (cnt2 (cddr x)))))
  :rule-classes nil)

; With both definitions disabled nothing opens CNT2.
(local
 (must-fail
  (thm (implies (and (consp x) (consp (cdr x)))
                (equal (cnt2 x) (+ 2 (cnt2 (cddr x)))))
       :hints (("Goal" :in-theory (disable cnt2-by-twos))))))
