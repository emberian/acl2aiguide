; examples/rewriting/force.lisp
;
; What it shows: a FORCEd hypothesis.  When the rewriter cannot relieve it,
; the rule fires anyway and the hypothesis is proved later, in a forcing
; round.  The forcing round succeeds when the hypothesis really holds in the
; goal's context and fails, with the whole proof, when it does not
; (:doc force, :doc forcing-round).
;
; Cited by humans/02-rewriting-theories-books.md, "force and case-split".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun my-statep (x)
  (and (true-listp x) (equal (len x) 2)))

(encapsulate
  (((gget *) => *))
  (local (defun gget (s) (declare (ignore s)) 0))
  (defthm gget-zero
    (implies (my-statep s) (equal (gget s) 0))
    :rule-classes nil))

(defthm gget-zero-forced
  (implies (force (my-statep s))
           (equal (gget s) 0))
  :hints (("Goal" :use gget-zero)))

; The hypothesis holds here (after MY-STATEP opens), so the forcing round, if
; any, proves it.
(defthm gget-zero-in-context
  (implies (and (true-listp s) (equal (len s) 2))
           (equal (+ 1 (gget s)) 1))
  :rule-classes nil)

; Here nothing says S is a state.  The rule still fires ("q.e.d. (given one
; forced hypothesis)") and Forcing Round 1 then fails on (MY-STATEP S).
(local
 (must-fail
  (thm (equal (+ 1 (gget s)) 1))))
