; examples/shapes/teeth.lisp
;
; Shapes: a keystone with its teeth.  The statement is written once as two
; macros so the witnesses evaluate the term the theorem states; a satisfiable
; witness where the conclusion fires; a concrete violating value for the
; hypothesis (assert-event); a mutant conclusion refuted by a value and, as a
; labelled prover refusal, by must-fail; and make-event checks that run at
; certification time.  No general negated must-fail: a prover's failure to
; find a proof is not a counterexample.
;
; Cited by ai/01-form-shapes.md, "make-event, assert-event, must-fail".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun clamp (x lo hi)
  (declare (xargs :guard (and (rationalp x) (rationalp lo) (rationalp hi))))
  (if (< x lo) lo (if (< hi x) hi x)))

(defmacro clamp-hyps (lo hi) `(<= ,lo ,hi))
(defmacro clamp-concl (x lo hi)
  `(and (<= ,lo (clamp ,x ,lo ,hi)) (<= (clamp ,x ,lo ,hi) ,hi)))

; Satisfiable: the hypothesis holds and the conclusion fires (clamping
; actually happens).
(assert-event (let ((x 9) (lo 1) (hi 5))
                (and (clamp-hyps lo hi)
                     (equal (clamp x lo hi) 5)
                     (clamp-concl x lo hi))))

; Teeth for the hypothesis: drop it and a concrete value breaks the
; conclusion.
(assert-event (let ((x 3) (lo 5) (hi 1))
                (and (not (clamp-hyps lo hi))
                     (not (clamp-concl x lo hi)))))

; The keystone.  (No RATIONALP hypotheses: no violating value exists for
; them, so they are not part of the statement.)
(defthm clamp-within-bounds
  (implies (clamp-hyps lo hi) (clamp-concl x lo hi)))

; A mutant conclusion ("strictly below HI"), refuted by a value ...
(assert-event (let ((x 9) (lo 1) (hi 5))
                (and (clamp-hyps lo hi)
                     (not (< (clamp x lo hi) hi)))))

; teeth: prover-refusal  ... and refused by the prover, beside the value.
(local
 (must-fail
  (defthm clamp-strictly-below-mutant
    (implies (clamp-hyps lo hi) (< (clamp x lo hi) hi)))))

; make-event: compute at certification time, refuse to certify if a check
; fails, and record the result as an ordinary event.
(make-event
 (if (equal (clamp 9 1 5) 5)
     '(value-triple :clamp-check-ok)
   (er hard 'teeth "clamp check failed")))

(make-event
 `(defconst *clamped-samples*
    ',(list (clamp 0 1 5) (clamp 3 1 5) (clamp 9 1 5))))

(assert-event (equal *clamped-samples* '(1 3 5)))
