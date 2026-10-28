; examples/systems/step-invariant.lisp
;
; A state machine in the shape fn's proofs take (fn docs/proofs.md "Shape of
; the claims"): a total step over every event, typed outcomes (accepted,
; refused, uncertain), inv(s) /\ permitted(s,e) => inv(step(s,e)),
; refusals that leave the state unchanged, and trace induction lifting the
; one-step theorem to every finite run.  Then its teeth (fn docs/proof-style.md
; section 5): a reachable positive witness, one violating value per
; hypothesis, and a mutation of the step that the keystone would catch.
;
; The machine is a bounded outbox: PUT queues a message if there is room;
; SYNC hands the queue to storage, whose answer is :ok (flushed), :fail
; (refused, nothing changes) or :timeout (UNCERTAIN: the queue may or may
; not be durable, so it is kept and marked).
;
; Cited by humans/04-modelling-systems.md, "State machines and step
; functions" and "Teeth".

(in-package "ACL2")

; ---------------------------------------------------------------------------
; State: (list queue flushed doubtful cap).

(defun ob (q flushed doubtful cap) (list q flushed doubtful cap))
(defun ob-q (s) (nth 0 s))
(defun ob-flushed (s) (nth 1 s))
(defun ob-doubtful (s) (nth 2 s))
(defun ob-cap (s) (nth 3 s))

(defun msg-listp (x)
  (if (atom x) (null x) (and (stringp (car x)) (msg-listp (cdr x)))))

(defthm len-of-append
  (equal (len (append x y)) (+ (len x) (len y))))

(defthm msg-listp-of-append
  (implies (msg-listp x)
           (equal (msg-listp (append x y)) (msg-listp y))))

(defun ob-invp (s)
  (and (true-listp s) (equal (len s) 4)
       (msg-listp (ob-q s))
       (natp (ob-flushed s))
       (booleanp (ob-doubtful s))
       (posp (ob-cap s))
       (<= (len (ob-q s)) (ob-cap s))))

; ---------------------------------------------------------------------------
; The step.  Total: every event, well-formed or not, gets an outcome.

(defun ob-step (s e)
  ; returns (list outcome new-state)
  (cond ((and (consp e) (eq (car e) :put) (stringp (cadr e)))
         (if (< (len (ob-q s)) (ob-cap s))
             (list :accepted (ob (append (ob-q s) (list (cadr e)))
                                 (ob-flushed s) (ob-doubtful s) (ob-cap s)))
           (list :refused s)))
        ((and (consp e) (eq (car e) :sync))
         (case (cadr e)
           (:ok (list :accepted
                      (ob nil (+ (ob-flushed s) (len (ob-q s))) nil (ob-cap s))))
           (:timeout (list :uncertain
                           (ob (ob-q s) (ob-flushed s) t (ob-cap s))))
           (otherwise (list :refused s))))
        (t (list :refused s))))

(defun outcome (r) (car r))
(defun next (r) (cadr r))

; Every step answers one of the three outcomes; nothing else reads as success.
(defthm ob-step-outcome-is-typed
  (member-equal (outcome (ob-step s e)) '(:accepted :refused :uncertain)))

; A refusal changes nothing.
(defthm ob-step-refusal-is-no-op
  (implies (equal (outcome (ob-step s e)) :refused)
           (equal (next (ob-step s e)) s)))

; KEYSTONE (one step): the invariant is preserved by every event.  The
; "permitted" premise of the general shape is empty here because the step
; refuses what it does not permit.
(defthm ob-step-preserves-invp
  (implies (ob-invp s)
           (ob-invp (next (ob-step s e)))))

; An uncertain outcome keeps the queue: nothing the caller handed over is
; lost because the storage did not answer.
(defthm ob-step-uncertain-keeps-queue
  (implies (equal (outcome (ob-step s e)) :uncertain)
           (equal (ob-q (next (ob-step s e))) (ob-q s))))

; ---------------------------------------------------------------------------
; Trace induction.

(defun ob-run (s es)
  (if (atom es) s (ob-run (next (ob-step s (car es))) (cdr es))))

(defthm ob-run-preserves-invp
  (implies (ob-invp s) (ob-invp (ob-run s es))))

; Flushed counts only grow, over any trace.
(defthm ob-step-flushed-monotone
  (implies (ob-invp s)
           (<= (ob-flushed s) (ob-flushed (next (ob-step s e)))))
  :rule-classes :linear)

(defthm ob-run-flushed-monotone
  (implies (ob-invp s)
           (<= (ob-flushed s) (ob-flushed (ob-run s es))))
  :rule-classes :linear)

; This is safety.  Nothing here says a PUT is ever flushed: a trace of
; :timeout answers keeps every message queued forever, and that trace is
; admitted.  Progress needs a premise about the environment.
(defconst *s0* (ob nil 0 nil 2))
(assert-event
 (let ((s (ob-run *s0* '((:put "a") (:sync :timeout) (:sync :timeout)))))
   (and (equal (ob-q s) '("a")) (equal (ob-flushed s) 0))))

; ---------------------------------------------------------------------------
; Teeth for ob-step-preserves-invp.

; Positive witness: a reachable state satisfying the hypothesis, and the
; conclusion holding after a step that changes it.
(assert-event
 (let ((s (ob-run *s0* '((:put "a")))))
   (and (ob-invp s) (ob-invp (next (ob-step s '(:put "b")))))))

; Removal witness for the one hypothesis: a state that is not ob-invp
; (queue over capacity) whose successor is not ob-invp either.
(assert-event
 (let ((bad (ob '("a" "b" "c") 0 nil 2)))
   (and (not (ob-invp bad))
        (not (ob-invp (next (ob-step bad '(:sync :timeout))))))))

; Mutation: a step that forgets the capacity check.  At this witness the
; hypothesis holds and the mutated conclusion fails, so a keystone stated
; about the mutant would be refuted by evaluation.
(defun ob-step-mutant (s e)
  (if (and (consp e) (eq (car e) :put) (stringp (cadr e)))
      (list :accepted (ob (append (ob-q s) (list (cadr e)))
                          (ob-flushed s) (ob-doubtful s) (ob-cap s)))
    (ob-step s e)))

(assert-event
 (let ((s (ob '("a" "b") 0 nil 2)))
   (and (ob-invp s)
        (not (ob-invp (next (ob-step-mutant s '(:put "c"))))))))

(in-theory (disable ob-step ob-invp))
