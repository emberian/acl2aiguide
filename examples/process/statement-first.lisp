; acl2aiguide example: a keystone written statement-first.  The statement is
; fixed before any proof work, and in the book it comes first: its premise is
; shown satisfiable at a concrete witness, every hypothesis is shown
; necessary by a concrete value that violates the conclusion without it, a
; mutant of the conclusion is refuted by a concrete value, and only then is
; the theorem proved.
;
; Cited by humans/06-process.md, sections "Statement first" and "Teeth".
;
; What it shows:
;   - one definition of the claim, as two macros (hypotheses, conclusion), so
;     the witnesses and the theorem are the same term and cannot drift apart
;     (the macro trick of fn's fn-proto-text: the admitted term is the
;     expansion);
;   - teeth as assert-events on concrete values, evaluated under the guards;
;   - a must-fail of the mutant, labelled as what it is: the prover's
;     refusal, which is weaker than the concrete counterexample beside it
;     (fn docs/proof-style.md section 5);
;   - the order: statement, witness, teeth, refusal, proof.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/lists/append" :dir :system)

; --- The subject: a bounded queue's admit. -----------------------------------

(defun enqueue (x q cap)
  (declare (xargs :guard (and (true-listp q) (natp cap))))
  (if (< (len q) cap)
      (mv :ok (append q (list x)))
    (mv :full q)))

; --- 1. The statement, before any proof. ------------------------------------
; Keystone: an admitted queue never exceeds its capacity.

(defmacro enqueue-claim-hyps (q cap)
  `(and (true-listp ,q)          ; H1: a queue
        (natp ,cap)              ; H2: a capacity
        (<= (len ,q) ,cap)))     ; H3: the queue is within it already

; The conclusion reads the second value through mv-list: an assert-event
; cannot evaluate (mv-nth 1 (enqueue ...)), a multiply valued call in an
; argument position, while mv-list is definitionally the identity, so the
; theorem and the witnesses state one term (fn's defkeystone does the same
; rewrapping at expansion: books/defkeystone.lisp, "WITNESS MODES").
(defmacro enqueue-claim-concl (x q cap)
  `(<= (len (mv-nth 1 (mv-list 2 (enqueue ,x ,q ,cap)))) ,cap))

; The first draft of a witness, without mv-list, kept as a record: refused
; at translation ("It is illegal to invoke ENQUEUE ...").
(local
 (must-fail
  (assert-event (let ((x 'c) (q '(a b)) (cap 3))
                  (<= (len (mv-nth 1 (enqueue x q cap))) cap)))))

; --- 2. The premise is satisfiable, and the conclusion fires there. ----------
; A non-degenerate witness: room left, and the insert happens.

(assert-event (let ((x 'c) (q '(a b)) (cap 3))
                (and (enqueue-claim-hyps q cap)
                     (equal (car (mv-list 2 (enqueue x q cap))) :ok)
                     (enqueue-claim-concl x q cap))))

; A boundary witness: full, refused, still within the capacity.
(assert-event (let ((x 'd) (q '(a b c)) (cap 3))
                (and (enqueue-claim-hyps q cap)
                     (equal (car (mv-list 2 (enqueue x q cap))) :full)
                     (enqueue-claim-concl x q cap))))

; --- 3. Teeth: each hypothesis is necessary. -------------------------------
; Remove H3: a queue already over its capacity stays over it.
(assert-event (let ((x 'z) (q '(a b c d e)) (cap 3))
                (and (true-listp q) (natp cap)          ; H1, H2 hold
                     (not (<= (len q) cap))             ; H3 fails
                     (not (enqueue-claim-concl x q cap)))))

; Remove H2: with a negative "capacity" nothing is within it.  H2 is also a
; conjunct of enqueue's guard, so its violating value is outside the guard
; domain and can only be evaluated logically, with guard checking off; fn's
; defteeth makes such an entry say `:logical "why"' and counts it apart.
; logical: cap = -1 violates enqueue's guard (natp cap).
(assert-event (with-guard-checking
               :none
               (let ((x 'z) (q nil) (cap -1))
                 (and (true-listp q)                    ; H1 holds
                      (not (natp cap))                  ; H2 fails
                      (not (enqueue-claim-concl x q cap))))))

; H1 has no violating value: the search for one fails, and the theorem
; without H1 is proved below (enqueue-stays-within-capacity-without-h1).
; fn's rule (docs/proof-style.md section 5): a hypothesis with no violating
; value is unnecessary; delete it or record why it stays.  It stays in the
; keystone because it is the guard of enqueue, and the theorem is about the
; guarded calls the program makes; the H1-free theorem is the record.
; logical: q = not-a-list violates enqueue's guard (true-listp q).
(assert-event (with-guard-checking
               :none
               (let ((x 'z) (q 'not-a-list) (cap 0))
                 (and (not (true-listp q))
                      (natp cap)
                      (<= (len q) cap)
                      (enqueue-claim-concl x q cap)))))

; --- 4. A mutant conclusion, refuted by a concrete value. ---------------------
; Mutant: "strictly below the capacity".  The insert that fills the queue
; violates it.
(assert-event (let ((x 'c) (q '(a b)) (cap 3))
                (and (enqueue-claim-hyps q cap)
                     (not (< (len (mv-nth 1 (mv-list 2 (enqueue x q cap)))) cap)))))

; teeth: prover-refusal  The same mutant, as a theorem the prover refuses.
; This only says the prover found no proof; the assert-event above is the
; counterexample.
(must-fail
 (defthm enqueue-mutant-strict
   (implies (enqueue-claim-hyps q cap)
            (< (len (mv-nth 1 (enqueue x q cap))) cap))))

; --- 5. Only now, the proof. -------------------------------------------------

(defthm enqueue-stays-within-capacity
  (implies (enqueue-claim-hyps q cap)
           (enqueue-claim-concl x q cap)))

; The record that H1 is unnecessary.
(defthm enqueue-stays-within-capacity-without-h1
  (implies (and (natp cap) (<= (len q) cap))
           (enqueue-claim-concl x q cap)))
