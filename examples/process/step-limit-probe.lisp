; acl2aiguide example: what a step-limited probe says and does not say, and
; the time limit an agent puts around every form it sends a live session.
;
; Cited by humans/06-process.md, sections "Sizing proofs" and "Running ACL2
; from an agent".
;
; What it shows:
;   - the same theorem under a small step limit is refused ("did not finish
;     inside N steps"), and without the limit it is proved: the refusal was
;     a statement about N, never about the theorem (fn docs/proof-style.md
;     section 9.2, "A probe that aborts on a step limit measures nothing");
;   - the step count of a form is the cost measure that does not move with
;     the machine's load (the Summary's "Prover steps counted"), so it is the
;     one to ratchet (fn docs/proofs.md, the proof_cost ratchet);
;   - with-prover-time-limit around an event, the shape fn's proof_repl.py
;     puts on every form it sends, so a search that stops returning costs a
;     bounded time and not the session.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun app (x y)
  (declare (xargs :guard (true-listp x)))
  (if (endp x) y (cons (car x) (app (cdr x) y))))

; The probe with a limit of 20 steps: refused.
(must-fail
 (with-prover-step-limit 20
   (defthm app-assoc-probe
     (equal (app (app x y) z) (app x (app y z))))))

; The same statement, no limit, under a wall-clock bound instead: proved.
(with-prover-time-limit 30
  (defthm app-assoc
    (equal (app (app x y) z) (app x (app y z)))))

; A tighter step limit that is enough is a "yes": evidence that it closes
; within that many steps.  (The Summary of app-assoc in this book's
; .cert.out prints the count the limit is chosen above.)
(with-prover-step-limit 2000
  (defthm app-assoc-again
    (equal (app (app x y) z) (app x (app y z)))
    :rule-classes nil))
