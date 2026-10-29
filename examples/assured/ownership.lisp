; examples/assured/ownership.lisp
;
; What it shows: ownership states as a declared enum column with a
; generation beside it, and the three ownership rules stated as theorems
; over the generated accessors, in the shape of fn2's byte pool
; (fn2/books/pool.lisp @127f7b877; its owed rows FN2-POOL-STALE,
; FN2-POOL-NO-REUSE and FN2-POOL-GENERATION in fn2/docs/OWED.md).
;
; A handle is (slot, generation).  States: :free, :leased (owned by one
; machine), :borrowed (lent out, for example to the host while a send is in
; flight), :retired (generation exhausted; never reused).
;
;   - Stale first: every handle-taking operation refuses a mismatched
;     generation before any other decision, and changes nothing.
;   - No reuse while borrowed: a borrowed slot cannot be freed; FREE answers
;     :borrowed and changes nothing.
;   - Generations only grow; a slot at the generation limit retires instead
;     of wrapping into an identity that was already handed out.
;
; The theorems are proved here for this small pool; in fn2 the same three
; are owed (stated, teeth evaluated, not yet proved), which
; assured/humans/07-honest-costs.md counts.
;
; Cited by assured/humans/01-rules-as-declarations.md and
; assured/ai/01-rules-as-declarations.md.

(in-package "ACL2")
(include-book "columns")

(defconst *gen-limit* (- (expt 2 60) 1))

(defun slot-okp (i slots)
  (declare (xargs :stobjs slots))
  (and (slots-wfp slots) (natp i) (< i (slots-rows slots))))

(defun slot-lease (i slots)
  (declare (xargs :stobjs slots :guard (slot-okp i slots)))
  (if (equal (slots-phase i slots) *slot-phase-free*)
      (let ((slots (slots-set-phase i *slot-phase-leased* slots)))
        (mv :ok slots))
    (mv :busy slots)))

(defun slot-borrow (i g slots)
  (declare (xargs :stobjs slots :guard (slot-okp i slots)))
  (cond ((not (equal g (slots-gen i slots))) (mv :stale slots))
        ((not (equal (slots-phase i slots) *slot-phase-leased*)) (mv :state slots))
        (t (let ((slots (slots-set-phase i *slot-phase-borrowed* slots)))
             (mv :ok slots)))))

(defun slot-return (i g slots)
  (declare (xargs :stobjs slots :guard (slot-okp i slots)))
  (cond ((not (equal g (slots-gen i slots))) (mv :stale slots))
        ((not (equal (slots-phase i slots) *slot-phase-borrowed*)) (mv :state slots))
        (t (let ((slots (slots-set-phase i *slot-phase-leased* slots)))
             (mv :ok slots)))))

(defun slot-free (i g slots)
  (declare (xargs :stobjs slots :guard (slot-okp i slots)))
  (cond ((not (equal g (slots-gen i slots))) (mv :stale slots))
        ((equal (slots-phase i slots) *slot-phase-borrowed*) (mv :borrowed slots))
        ((not (equal (slots-phase i slots) *slot-phase-leased*)) (mv :state slots))
        ((<= *gen-limit* (slots-gen i slots))
         (let ((slots (slots-set-phase i *slot-phase-retired* slots)))
           (mv :retired slots)))
        (t (let* ((slots (slots-set-gen i (+ 1 (slots-gen i slots)) slots))
                  (slots (slots-set-phase i *slot-phase-free* slots)))
             (mv :ok slots)))))

; Each operation keeps the declared shape (the generated setter theorems
; do the work; nothing here reopens the table recognizer).
(defthm slot-free-preserves-shape
  (implies (slot-okp i slots)
           (and (slots-wfp (mv-nth 1 (slot-free i g slots)))
                (equal (slots-rows (mv-nth 1 (slot-free i g slots)))
                       (slots-rows slots)))))

; Stale first: a mismatched generation is refused and nothing changes.
(defthm slot-free-stale
  (implies (not (equal g (slots-gen i slots)))
           (and (equal (mv-nth 0 (slot-free i g slots)) :stale)
                (equal (mv-nth 1 (slot-free i g slots)) slots))))

(defthm slot-borrow-stale
  (implies (not (equal g (slots-gen i slots)))
           (and (equal (mv-nth 0 (slot-borrow i g slots)) :stale)
                (equal (mv-nth 1 (slot-borrow i g slots)) slots))))

; No reuse while borrowed.
(defthm slot-free-refuses-borrowed
  (implies (equal (slots-phase i slots) *slot-phase-borrowed*)
           (equal (mv-nth 1 (slot-free i g slots)) slots)))

; Generations only grow, at the freed slot.
(defthm slot-free-generation-monotone
  (implies (slot-okp i slots)
           (<= (slots-gen i slots)
               (slots-gen i (mv-nth 1 (slot-free i g slots)))))
  :hints (("Goal" :in-theory (enable slots-gen slots-set-gen slots-set-phase
                                     slots-wfp)))
  :rule-classes :linear)

; A successful free changes the generation, so every old handle is stale.
(defthm slot-free-ok-invalidates-handle
  (implies (and (slot-okp i slots)
                (equal (mv-nth 0 (slot-free i g slots)) :ok))
           (not (equal g (slots-gen i (mv-nth 1 (slot-free i g slots))))))
  :hints (("Goal" :in-theory (enable slots-gen slots-set-gen slots-set-phase
                                     slots-wfp))))

; Teeth: a lease, a borrow, a refused free while borrowed, a return, a free
; that bumps the generation, and the old handle refused as stale.
(defun ownership-demo ()
  (declare (xargs :guard t))
  (with-local-stobj slots
    (mv-let (answer slots)
      (let ((slots (slots-init 4 slots)))
        (mv-let (c1 slots) (slot-lease 2 slots)
          (mv-let (c2 slots) (slot-borrow 2 0 slots)
            (mv-let (c3 slots) (slot-free 2 0 slots)
              (mv-let (c4 slots) (slot-return 2 0 slots)
                (mv-let (c5 slots) (slot-free 2 0 slots)
                  (mv-let (c6 slots) (slot-borrow 2 0 slots)
                    (mv (list c1 c2 c3 c4 c5 c6 (slots-gen 2 slots))
                        slots))))))))
      answer)))

(assert-event (equal (ownership-demo) '(:ok :ok :borrowed :ok :ok :stale 1)))
