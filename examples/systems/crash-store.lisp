; examples/systems/crash-store.lisp
;
; A tiny crash model in the shape of fn's byte store (fn books/byte-store.lisp):
; one file of blocks, a DURABLE copy and an ordered list of PENDING block
; writes the process has issued and no fence has drained.  The process sees
; the VIEW (durable with every pending write applied).  fsync drains the
; pending list.  A crash keeps the durable copy and lands an arbitrary
; subsequence of the pending writes, each landing as written, as zero, or
; as garbage; afterwards nothing is pending.  A failed fsync lands a torn
; selection and DISCARDS the rest, so a retry fences nothing (fsyncgate).
;
; Theorems: a fence makes the view durable against every crash; a crash
; changes no block that no pending write names; the two-fsync commit
; protocol (data, fsync, marker) never shows the marker without the data,
; at every cut and every crash choice; the one-fsync variant does, by a
; concrete crash (teeth).
;
; Cited by humans/04-modelling-systems.md, "Crash models".

(in-package "ACL2")

; ---------------------------------------------------------------------------
; State: (list durable pending).  durable: a list of blocks; pending: a list
; of (index . value) writes in issue order.

(defun st (durable pending) (list durable pending))
(defun st-durable (s) (car s))
(defun st-pending (s) (cadr s))

(defun apply-writes (blocks ws)
  (if (atom ws)
      blocks
    (apply-writes (update-nth (nfix (car (car ws))) (cdr (car ws)) blocks)
                  (cdr ws))))

(defthm apply-writes-of-append
  (equal (apply-writes blocks (append ws1 ws2))
         (apply-writes (apply-writes blocks ws1) ws2)))

(defun view (s) (apply-writes (st-durable s) (st-pending s)))

; The process's write: pending, never durable.
(defun bwrite (i v s)
  (st (st-durable s) (append (st-pending s) (list (cons i v)))))

; fsync that succeeds: everything pending becomes durable.
(defun fsync-ok (s) (st (view s) nil))

; ---------------------------------------------------------------------------
; Crash.  One choice per pending write: :drop, :new, :zero, or
; (:garble . value).  A missing choice is :drop (conservative loss).

(defun land (ws choices)
  (if (atom ws)
      nil
    (let ((w (car ws)) (c (if (consp choices) (car choices) :drop)))
      (cond ((eq c :new) (cons w (land (cdr ws) (cdr choices))))
            ((eq c :zero) (cons (cons (car w) 0) (land (cdr ws) (cdr choices))))
            ((and (consp c) (eq (car c) :garble))
             (cons (cons (car w) (cdr c)) (land (cdr ws) (cdr choices))))
            (t (land (cdr ws) (cdr choices)))))))

(defun crash (s choices)
  (st (apply-writes (st-durable s) (land (st-pending s) choices)) nil))

; fsync that FAILS: the platform lands the torn selection CHOICES and marks
; the rest clean, i.e. drops them (Rebello et al. 2020).  Nothing remains
; pending for a retry to write.
(defun fsync-fail (s choices)
  (st (apply-writes (st-durable s) (land (st-pending s) choices)) nil))

; ---------------------------------------------------------------------------
; Contracts about the model.

; A fence makes the view durable against every crash.
(defthm crash-after-fsync-is-the-view
  (equal (st-durable (crash (fsync-ok s) choices)) (view s)))

; A crash changes no block that no pending write names.
(defun names-index-p (i ws)
  (if (atom ws)
      nil
    (or (equal (nfix (car (car ws))) i) (names-index-p i (cdr ws)))))

(defthm land-names-subset
  (implies (not (names-index-p i ws))
           (not (names-index-p i (land ws choices)))))

(defthm apply-writes-untouched
  (implies (and (natp i) (not (names-index-p i ws)))
           (equal (nth i (apply-writes blocks ws)) (nth i blocks))))

(defthm crash-keeps-unnamed-blocks
  (implies (and (natp i) (not (names-index-p i (st-pending s))))
           (equal (nth i (st-durable (crash s choices)))
                  (nth i (st-durable s)))))

; fsyncgate: after a failed fsync, a successful retry adds nothing durable.
(defthm fsync-retry-after-failure-adds-nothing
  (equal (st-durable (fsync-ok (fsync-fail s choices)))
         (st-durable (fsync-fail s choices))))

; ---------------------------------------------------------------------------
; Programs and cuts.  A program is a list of operations; a crash may happen
; after any prefix of it, with any choices.

(defun op-step (s op)
  (case (car op)
    (:write (bwrite (cadr op) (caddr op) s))
    (:fsync (fsync-ok s))
    (otherwise s)))

(defun run (s ops)
  (if (atom ops) s (run (op-step s (car ops)) (cdr ops))))

(defun crash-at (s ops k choices) (crash (run s (take k ops)) choices))

; The commit protocol: block 1 holds the data, block 0 the commit marker.
(defun commit-program (v)
  (list (list :write 1 v) (list :fsync) (list :write 0 1)))

(defun committedp (img) (equal (nth 0 (st-durable img)) 1))

; Keep block reads as NTH and writes as UPDATE-NTH (fn's catalog-paged.lisp
; does the same for its stobj fields).  Open, NTH 0 and NTH 1 become CAR and
; CADR of UPDATE-NTH terms, which nothing simplifies, and the keystone below
; stops at (EQUAL (CADR (UPDATE-NTH 1 V (CAR S))) V); closed, the built-in
; NTH-UPDATE-NTH decides every read.
(local (in-theory (disable nth update-nth)))

; KEYSTONE.  From a quiet state whose marker is not set, every crash at
; every cut of the program that shows the marker shows the data.
(defthm commit-program-marker-implies-data
  (implies (and (null (st-pending s))
                (not (equal (nth 0 (st-durable s)) 1))
                (member-equal k '(0 1 2 3))
                (committedp (crash-at s (commit-program v) k choices)))
           (equal (nth 1 (st-durable (crash-at s (commit-program v) k choices)))
                  v))
  :hints (("Goal" :in-theory (enable take))))

; ---------------------------------------------------------------------------
; Teeth: concrete values.

; Positive witness: the full program, every write lands; the image is
; committed and holds the data.
(defconst *s0* (st '(0 7) nil))
(assert-event
 (let ((img (crash-at *s0* (commit-program 42) 3 '(:new))))
   (and (committedp img) (equal (nth 1 (st-durable img)) 42))))

; Without the hypothesis "marker not set": an initial marker of 1 shows the
; marker over old data at cut 0.
(assert-event
 (let ((img (crash-at (st '(1 7) nil) (commit-program 42) 0 nil)))
   (and (committedp img) (not (equal (nth 1 (st-durable img)) 42)))))

; Without "quiet": a pending garbage write to the marker can set it.
(assert-event
 (let ((img (crash-at (st '(0 7) (list (cons 0 5))) (commit-program 42) 0
                      '((:garble . 1)))))
   (and (committedp img) (not (equal (nth 1 (st-durable img)) 42)))))

; Mutation: drop the fsync between data and marker.  A crash that lands the
; marker and drops the data shows the marker over the old data.
(defun commit-program-no-fence (v)
  (list (list :write 1 v) (list :write 0 1)))

(assert-event
 (let ((img (crash-at *s0* (commit-program-no-fence 42) 2 '(:drop :new))))
   (and (committedp img) (equal (nth 1 (st-durable img)) 7))))

; The cut matters: cut 4 is not a cut of a three-step program (the
; hypothesis lists the cuts), and naming it would be vacuous, not wrong.
