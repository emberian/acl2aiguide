; examples/systems/refinement.lisp
;
; A recovery refinement in the shape of fn's
; fn-owner-recover-from-checkpoint-equals-full-recover (fn
; books/owner-checkpoint-open.lisp:104): the state installed from a
; checkpoint of ANY prefix, extended over ANY suffix, is the state a full
; replay of prefix ++ suffix installs.  No hypothesis.  Then one rung down:
; the checkpoint is stored ENCODED, and recovery from the decoded bytes is
; still the full replay, because every replayed state satisfies the
; recognizer under which decode inverts encode.
;
; The functions are guard-verified and executable; the host would run
; these definitions, not a separately written recovery.
;
; Cited by humans/04-modelling-systems.md, "Refinement".

(in-package "ACL2")

; ---------------------------------------------------------------------------
; The machine: balances by account, events credit or debit.

(defun balancesp (x)
  (declare (xargs :guard t))
  (if (atom x)
      (null x)
    (and (consp (car x)) (symbolp (car (car x))) (natp (cdr (car x)))
         (balancesp (cdr x)))))

(defun bal-of (a s)
  (declare (xargs :guard (and (symbolp a) (balancesp s))))
  (nfix (cdr (assoc-eq a s))))

(defun apply-event (s e)
  (declare (xargs :guard (balancesp s)))
  (if (and (true-listp e) (equal (len e) 3)
           (symbolp (cadr e)) (natp (caddr e)))
      (let ((a (cadr e)) (n (caddr e)))
        (case (car e)
          (:credit (acons a (+ (bal-of a s) n) s))
          (:debit (if (<= n (bal-of a s)) (acons a (- (bal-of a s) n) s) s))
          (otherwise s)))
    s))

(defthm balancesp-of-apply-event
  (implies (balancesp s) (balancesp (apply-event s e))))

(defun replay-from (s events)
  (declare (xargs :guard (and (balancesp s) (true-listp events))))
  (if (atom events) s (replay-from (apply-event s (car events)) (cdr events))))

(defun replay (events)
  (declare (xargs :guard (true-listp events)))
  (replay-from nil events))

; ---------------------------------------------------------------------------
; Rung 1: checkpoint = the state after the prefix; recovery = replay from it.

(defun capture (prefix)
  (declare (xargs :guard (true-listp prefix)))
  (replay prefix))

(defun recover (ckpt suffix)
  (declare (xargs :guard (and (balancesp ckpt) (true-listp suffix))))
  (replay-from ckpt suffix))

(defthm replay-from-of-append
  (equal (replay-from s (append xs ys))
         (replay-from (replay-from s xs) ys)))

; KEYSTONE: no hypothesis.
(defthm recover-from-checkpoint-equals-full-replay
  (equal (recover (capture prefix) suffix)
         (replay (append prefix suffix))))

; ---------------------------------------------------------------------------
; Rung 2: the checkpoint on disk is a flat list; decode inverts encode on
; every BALANCESP value, and every replayed state is one.

(defun encode (s)
  (declare (xargs :guard (balancesp s)))
  (if (atom s) nil (list* (car (car s)) (cdr (car s)) (encode (cdr s)))))

(defun decode (xs)
  (declare (xargs :guard t))
  (if (and (consp xs) (consp (cdr xs)))
      (if (and (symbolp (car xs)) (natp (cadr xs)))
          (let ((rest (decode (cddr xs))))
            (if (eq rest :bad) :bad (cons (cons (car xs) (cadr xs)) rest)))
        :bad)
    (if (null xs) nil :bad)))

(defthm decode-of-encode
  (implies (balancesp s) (equal (decode (encode s)) s)))

(defthm balancesp-of-replay-from
  (implies (balancesp s) (balancesp (replay-from s events))))

(defun recover-encoded (bytes suffix)
  (declare (xargs :guard (true-listp suffix)))
  (let ((ckpt (decode bytes)))
    (if (balancesp ckpt) (recover ckpt suffix) :refused)))

(defthm recover-encoded-equals-full-replay
  (equal (recover-encoded (encode (capture prefix)) suffix)
         (replay (append prefix suffix))))

; A checkpoint that does not decode is refused, never misread as a state.
(defthm recover-encoded-refuses-garbage
  (implies (not (balancesp (decode bytes)))
           (equal (recover-encoded bytes suffix) :refused)))

; ---------------------------------------------------------------------------
; Teeth: a reachable witness for the keystone, and a mutation (a recovery
; that skips the checkpoint) that the keystone would refute.

(defconst *pre* '((:credit alice 10) (:debit alice 3)))
(defconst *suf* '((:credit bob 5) (:debit alice 2)))

(assert-event
 (and (equal (recover (capture *pre*) *suf*) (replay (append *pre* *suf*)))
      (equal (bal-of 'alice (replay (append *pre* *suf*))) 5)))

(defun recover-mutant (ckpt suffix)
  (declare (ignore ckpt))
  (replay suffix))

(assert-event
 (not (equal (recover-mutant (capture *pre*) *suf*)
             (replay (append *pre* *suf*)))))

(assert-event
 (equal (recover-encoded '(alice not-a-number) *suf*) :refused))
