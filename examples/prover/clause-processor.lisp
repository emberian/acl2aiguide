; examples/prover/clause-processor.lisp
;
; What it shows: a verified clause processor (the :doc clause-processor
; example): a function that replaces a goal by two goals, the goal with a
; chosen fact added as a hypothesis and the fact itself.  Its correctness
; theorem, stored as a :clause-processor rule, is what lets a :clause-processor
; hint use it.  The hint's term must be a translated term.
;
; Cited by humans/01-logic-and-prover.md, "The hints: :clause-processor".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun mag (x) (if (< x 0) (- x) x))
(in-theory (disable mag))

(local
 (must-fail
  (thm (implies (rationalp y) (<= 0 (+ (mag y) (mag y)))))))

(defun note-fact-clause-processor (cl term)
  (declare (xargs :guard t))
  (list (cons (list 'not term) cl)
        (list term)))

(defevaluator evl0 evl0-list
  ((not x) (if x y z)))

(defthm correctness-of-note-fact-clause-processor
  (implies (and (pseudo-term-listp cl)
                (alistp a)
                (evl0 (conjoin-clauses
                       (note-fact-clause-processor cl term))
                      a))
           (evl0 (disjoin cl) a))
  :rule-classes :clause-processor)

; '(not (< (mag y) '0)) is the translated form of (<= 0 (mag y)).  The second
; goal, the fact itself, needs MAG open, which the second hint gives it.
(defthm twice-mag-non-negative
  (implies (rationalp y) (<= 0 (+ (mag y) (mag y))))
  :hints (("Goal" :clause-processor
                  (note-fact-clause-processor clause '(not (< (mag y) '0))))
          ("Subgoal 1" :in-theory (enable mag))))
