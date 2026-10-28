; examples/rewriting/loop-pair.lisp
;
; What it shows: two rewrite rules that rewrite each other's left-hand sides,
; the rewriter loop they cause (stopped by the call-depth limit, reported as a
; HARD ACL2 ERROR naming (cw-gstack)), and two repairs: keep only one direction
; enabled, and record the incompatibility as a theory invariant so the loop
; cannot be re-enabled by accident.
;
; Cited by humans/02-rewriting-theories-books.md, "Loops".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun f1 (x) (cons x 1))
(defun f2 (x) (cons x 1))

; The CONSP hypotheses keep these from being "simple" abbreviation rules, so
; the loop happens in the rewriter proper rather than in preprocessing.
(defthm f1-is-f2
  (implies (consp x) (equal (f1 x) (f2 x))))

(in-theory (disable f1 f2))

(defthm f2-is-f1
  (implies (consp x) (equal (f2 x) (f1 x)))
  :hints (("Goal" :in-theory (enable f1 f2))))

; Both enabled: (f1 a) -> (f2 a) -> (f1 a) -> ... until the call depth limit
; of 1000.  The step limit is a second fence; this loop hits the depth limit
; first.
(local
 (must-fail
  (with-prover-step-limit 100000
    (thm (implies (consp a) (equal (car (f1 a)) a))))))

; Repair 1: choose a normal form.  Here F1 terms become F2 terms; F2's
; definition is the place the proof opens.
(in-theory (disable f2-is-f1))

(defthm car-of-f1
  (implies (consp a) (equal (car (f1 a)) a))
  :hints (("Goal" :in-theory (enable f2))))

; Repair 2: record that the two directions are incompatible.  Any later theory
; that enables both is now an error (:doc theory-invariant).
(theory-invariant (incompatible (:rewrite f1-is-f2) (:rewrite f2-is-f1))
                  :key f1-f2-direction)

(local
 (must-fail
  (in-theory (enable f2-is-f1))))
