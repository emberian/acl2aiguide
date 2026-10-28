; examples/prover/subgoal-theory.lisp
;
; What it shows: an :in-theory hint is evaluated against the current logical
; world, not against the theory of the parent goal (:doc hints, :in-theory).
; A "Goal" hint disables F; a subgoal hint that only says (enable gg) puts F
; back, because (enable gg) means "the global theory plus GG".
;
; Cited by humans/01-logic-and-prover.md, "A Goal :in-theory does not survive
; a subgoal that has its own" (fn docs/proof-style.md section 9.3).

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun f (x) (if (natp x) (+ 1 x) 1))
(defun gg (x) (* 2 (nfix x)))

; With F's definition and executable counterpart disabled, neither case
; produced by :cases can be proved: the Goal hint's theory is inherited by both
; subgoals.
(local
 (must-fail
  (thm (implies (natp x) (equal (f x) (+ 1 x)))
       :hints (("Goal" :in-theory (disable f (:e f))
                       :cases ((equal x 0)))))))

; The same proof with an innocent-looking (enable gg) at each subgoal
; succeeds.  Nothing here mentions F; (enable gg) is computed from the global
; theory, in which F is enabled, so the Goal's (disable f (:e f)) is gone at
; both subgoals.
(defthm f-of-natp
  (implies (natp x) (equal (f x) (+ 1 x)))
  :hints (("Goal" :in-theory (disable f (:e f))
                  :cases ((equal x 0)))
          ("Subgoal 2" :in-theory (enable gg))
          ("Subgoal 1" :in-theory (enable gg)))
  :rule-classes nil)

; To keep a Goal-level disable under a subgoal hint, spell the whole theory
; again at the subgoal: (e/d (gg) (f (:e f))).  Here that makes the proof fail,
; as it should, which shows the disable now holds.
(local
 (must-fail
  (thm (implies (natp x) (equal (f x) (+ 1 x)))
       :hints (("Goal" :in-theory (disable f (:e f))
                       :cases ((equal x 0)))
               ("Subgoal 2" :in-theory (e/d (gg) (f (:e f))))
               ("Subgoal 1" :in-theory (e/d (gg) (f (:e f))))))))
