; examples/systems/assumption-instance.lisp
;
; A named platform assumption as an encapsulate, a theorem that takes it,
; and a qualification by functional instance: the shape of fn's
; A-DURABILITY (fn books/assumptions.lisp; docs/proofs.md "Qualifying a
; platform against A-DURABILITY").  The assumption constrains an unknown
; PLATFORM-CRASH to do what the crash model of crash-store.lisp guarantees:
; a fenced view survives, and no block a pending write does not name
; changes.  The local witness (lose everything pending) proves the
; assumption satisfiable.  The durability theorem is proved from the
; constraints alone; the model's own CRASH then discharges them, so the
; theorem holds of the model by :functional-instance, checked by ACL2.  A
; "platform" that zeroes the disk does not, and is refused.
;
; Cited by humans/04-modelling-systems.md, "Discharging an assumption by
; functional instance".

(in-package "ACL2")
(include-book "crash-store")

(local (in-theory (disable nth update-nth)))

; Keep the record and the fence closed (the opaque discipline of
; examples/modelling/opaque-record.lisp).  The assumption is stated about
; (ST-DURABLE (PLATFORM-CRASH (FSYNC-OK S) ...)); with FSYNC-OK open the
; run's final fence becomes a CONS, and with ST-DURABLE open the read
; becomes CAR, and in either case the constraint never matches (the
; checkpoints show (PLATFORM-CRASH (CONS (UPDATE-NTH 0 1 ...) '(NIL))
; ORACLE) and then (CAR (PLATFORM-CRASH (FSYNC-OK ...) ORACLE))).
(defthm st-durable-of-st (equal (st-durable (st d p)) d))
(defthm st-pending-of-st (equal (st-pending (st d p)) p))
(defthm st-durable-of-fsync-ok (equal (st-durable (fsync-ok s)) (view s)))
(defthm st-pending-of-fsync-ok (equal (st-pending (fsync-ok s)) nil))
(local (in-theory (disable st st-durable st-pending fsync-ok)))

; A-DURABILITY for this store.  ORACLE is the platform's freedom: power
; timing, drive cache, scheduler.
(encapsulate
  (((platform-crash * *) => *))
  (local (defun platform-crash (s oracle)
           (declare (ignore oracle))
           (crash s nil)))                    ; the lose-everything image
  (defthm platform-crash-keeps-fenced-view
    (equal (st-durable (platform-crash (fsync-ok s) oracle)) (view s)))
  (defthm platform-crash-keeps-unnamed-blocks
    (implies (and (natp i) (not (names-index-p i (st-pending s))))
             (equal (nth i (st-durable (platform-crash s oracle)))
                    (nth i (st-durable s))))))

; The acknowledged commit: data, fsync, marker, fsync.  The caller is told
; "committed" only after the second fsync returns.
(defun acked-commit-program (v)
  (list (list :write 1 v) (list :fsync) (list :write 0 1) (list :fsync)))

; Under the assumption, every platform crash after the acknowledgement shows
; the marker and the data.
(defthm acked-commit-survives-platform-crash
  (let ((img (platform-crash (run s (acked-commit-program v)) oracle)))
    (and (equal (nth 0 (st-durable img)) 1)
         (equal (nth 1 (st-durable img)) v))))

; Qualification: the crash model satisfies the assumption, so the theorem
; holds of it.  The obligations are the two constraints with PLATFORM-CRASH
; := CRASH, which crash-store.lisp proved as crash-after-fsync-is-the-view
; and crash-keeps-unnamed-blocks.
(defthm acked-commit-survives-model-crash
  (let ((img (crash (run s (acked-commit-program v)) choices)))
    (and (equal (nth 0 (st-durable img)) 1)
         (equal (nth 1 (st-durable img)) v)))
  :hints (("Goal" :use ((:functional-instance
                         acked-commit-survives-platform-crash
                         (platform-crash (lambda (s oracle) (crash s oracle))))))))

; A platform that zeroes block 1 on every crash violates the assumption; the
; functional instance's obligation is false, so the transfer is refused.
(include-book "std/testing/must-fail" :dir :system)

(defun zeroing-crash (s oracle)
  (declare (ignore oracle))
  (st (update-nth 1 0 (st-durable (crash s nil))) nil))

(must-fail
 (defthm acked-commit-survives-zeroing-crash
   (let ((img (zeroing-crash (run s (acked-commit-program v)) oracle)))
     (equal (nth 1 (st-durable img)) v))
   :hints (("Goal" :use ((:functional-instance
                          acked-commit-survives-platform-crash
                          (platform-crash zeroing-crash)))))))
