; examples/rewriting/loop-stopper.lisp
;
; What it shows: a permutative rule (commutativity) does not loop, because
; ACL2 computes a loop-stopper for it and only lets it move a smaller term
; leftward (:doc loop-stopper).  The same rule with :loop-stopper nil loops.
;
; Cited by humans/02-rewriting-theories-books.md, "Loops" and ":rewrite".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun op (x y) (+ (fix x) (fix y)))

; The stored rule has Loop-stopper ((X Y OP)), as :pr op-comm shows.
(defthm op-comm
  (equal (op x y) (op y x)))

(in-theory (disable op))

; Terminates: (op b a) is permuted to (op a b) and then left alone.
(defthm op-b-a
  (equal (op b a) (op a b))
  :rule-classes nil)

; With the loop-stopper removed the rule fires on its own output forever.
; OP-COMM is disabled first so that the unstopped rule is the only one.
(in-theory (disable op-comm))

(defthm op-comm-unstopped
  (equal (op x y) (op y x))
  :rule-classes ((:rewrite :loop-stopper nil))
  :hints (("Goal" :in-theory (enable op))))

(local
 (must-fail
  (with-prover-step-limit 100000
    (thm (equal (op b a) (op a b))))))

(in-theory (e/d (op-comm) (op-comm-unstopped)))
