; examples/prover/induction-lemma-first.lisp
;
; What it shows: a conjecture that ACL2 attacks by induction and fails on,
; although no induction is needed once the right lemma is in the database.
; The induction it picks is plausible; the missing piece is a rewrite rule.
;
; Cited by humans/01-logic-and-prover.md, "Why proofs fail: the missing lemma".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun drop (n x)
  (if (zp n)
      x
    (drop (1- n) (cdr x))))

; Without a lemma about nested DROP, ACL2 merges the schemes suggested by the
; four DROP calls, inducts on I, and fails in sub-inductions.
(local
 (must-fail
  (with-prover-step-limit 200000
    (thm (implies (and (natp i) (natp j))
                  (equal (drop i (drop j x))
                         (drop j (drop i x))))))))

; The lemma: nested DROP is one DROP.  ACL2 proves it by induction on J.
(defthm drop-of-drop
  (implies (and (natp i) (natp j))
           (equal (drop i (drop j x))
                  (drop (+ i j) x))))

; With the lemma both sides rewrite to (drop (+ i j) x), and commutativity of
; + finishes: no induction.
(defthm drop-commutes
  (implies (and (natp i) (natp j))
           (equal (drop i (drop j x))
                  (drop j (drop i x)))))
