; examples/prover/step-limits.lisp
;
; What it shows: the cheap ways to make a probe stop, and what a stopped probe
; does and does not tell you.  :do-not-induct t fails at the first goal that
; would need induction; with-prover-step-limit aborts a proof after N steps.
; A step-limit abort says only "not within N steps" (fn docs/proof-style.md
; section 9.2): the theorem below is true and is proved after the abort.
;
; Cited by humans/01-logic-and-prover.md, "Step limits and time limits".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun rv (x)
  (if (consp x) (append (rv (cdr x)) (list (car x))) nil))

(defun rva (x acc)
  (if (consp x) (rva (cdr x) (cons (car x) acc)) acc))

; Fails fast: the goal is pushed for induction and induction is forbidden.
(local
 (must-fail
  (thm (equal (rva x acc) (append (rv x) acc))
       :hints (("Goal" :do-not-induct t)))))

; Aborts: 100 steps is not enough for this (true) theorem.
(local
 (must-fail
  (with-prover-step-limit 100
    (thm (equal (rva x acc) (append (rv x) acc))))))

; Unlimited, it proves.  The aborted probe above measured nothing about it.
(defthm rva-is-rv-append
  (equal (rva x acc) (append (rv x) acc)))
