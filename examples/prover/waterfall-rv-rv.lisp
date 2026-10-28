; examples/prover/waterfall-rv-rv.lisp
;
; What it shows: one proof that passes through every waterfall process:
; simplification, destructor elimination, cross-fertilization,
; generalization, elimination of irrelevance, and induction (twice).  Run the
; DEFTHM below after (set-gag-mode nil) to read the narration;
; humans/01-logic-and-prover.md reproduces it.
;
; Cited by humans/01-logic-and-prover.md, "The waterfall".

(in-package "ACL2")

(defun rv (x)
  (if (consp x)
      (append (rv (cdr x)) (list (car x)))
    nil))

; No lemma about RV of APPEND is supplied; the prover invents the needed
; generalization itself and proves it by a second induction.
(defthm rv-rv
  (implies (true-listp x)
           (equal (rv (rv x)) x)))
