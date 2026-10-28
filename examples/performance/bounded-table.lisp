; acl2aiguide example: a fixed-size stobj (:resizable nil) with a bounded
; insert that answers a typed refusal when the table is full.
;
; Cited by humans/05-high-performance.md, sections "Static allocation:
; fixed-size stobjs" and "TigerStyle in ACL2".
;
; What it shows:
;   - the capacity is a defconst, used as the array length, in the guards and
;     in the theorems; the one place a literal must repeat it (a type-spec
;     bound) is tied back to the constant by an assert-event, which is the
;     ACL2 form of TigerStyle's "assert the relationships of compile-time
;     constants";
;   - the insert never allocates and never grows: when the table is full it
;     answers :full and returns the stobj unchanged, and that is a theorem,
;     not a comment;
;   - what :resizable nil means in the logic: the resize function exists, is
;     guard-verified with guard (tblp tbl), and is logically the identity on
;     the stobj; executing it is a hard error.  Guard verification does not
;     keep you from calling it, so the code must not;
;   - with-local-stobj as scratch space in a test, with its return shape: the
;     mv-let binds the stobj, the body returns the other values only.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defconst *table-cap* 64)

(defstobj tbl
  (keys :type (array (unsigned-byte 61) (*table-cap*)) :initially 0 :resizable nil)
  (used :type (integer 0 64) :initially 0)
  :inline t)

; The type-spec of USED repeats the capacity as a literal; tie it back.
(assert-event (equal *table-cap* 64))

; The answer words, one recognizer.
(defun tbl-wordp (x)
  (declare (xargs :guard t))
  (or (eq x :ok) (eq x :full)))

(defun tbl-insert (k tbl)
  (declare (xargs :stobjs tbl
                  :guard (unsigned-byte-p 61 k)))
  (let ((n (used tbl)))
    (if (>= n *table-cap*)
        (mv :full tbl)
      (let* ((tbl (update-keysi n k tbl))
             (tbl (update-used (+ 1 n) tbl)))
        (mv :ok tbl)))))

(defthm tbl-insert-answers-a-word
  (tbl-wordp (mv-nth 0 (tbl-insert k tbl))))

(defthm tbl-insert-full-is-a-refusal-and-a-no-op
  (implies (and (tblp tbl)
                (<= *table-cap* (used tbl)))
           (and (equal (mv-nth 0 (tbl-insert k tbl)) :full)
                (equal (mv-nth 1 (tbl-insert k tbl)) tbl))))

(defthm tbl-insert-ok-stores-the-key
  (implies (and (tblp tbl)
                (< (used tbl) *table-cap*))
           (and (equal (mv-nth 0 (tbl-insert k tbl)) :ok)
                (equal (used (mv-nth 1 (tbl-insert k tbl))) (+ 1 (used tbl)))
                (equal (keysi (used tbl) (mv-nth 1 (tbl-insert k tbl))) k))))

; The array-field facts the preservation proof needs (fn writes the same
; pair for every stobj array: books/msgid-linear-exec.lisp section 1).
(defthm keysp-of-update-nth
  (implies (and (keysp l) (natp i) (< i (len l)) (unsigned-byte-p 61 v))
           (keysp (update-nth i v l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm tbl-len-of-update-nth
  (implies (and (natp i) (< i (len l)))
           (equal (len (update-nth i v l)) (len l)))
  :hints (("Goal" :in-theory (enable update-nth))))

(defthm tbl-insert-preserves-tblp
  (implies (and (tblp tbl) (unsigned-byte-p 61 k))
           (tblp (mv-nth 1 (tbl-insert k tbl)))))

(defthm tbl-insert-never-exceeds-the-cap
  (implies (tblp tbl)
           (<= (used (mv-nth 1 (tbl-insert k tbl))) *table-cap*))
  :rule-classes :linear)

; A test driver: N inserts into a fresh local table; the answer is the list
; of words, so the test can see where the refusals start.
(defun tbl-insert-n (n tbl)
  (declare (xargs :stobjs tbl :guard (unsigned-byte-p 61 n)))
  (if (zp n)
      (mv nil tbl)
    (mv-let (word tbl)
      (tbl-insert n tbl)
      (mv-let (rest tbl)
        (tbl-insert-n (- n 1) tbl)
        (mv (cons word rest) tbl)))))

(defun tbl-trial (n)
  (declare (xargs :guard (unsigned-byte-p 61 n)))
  (with-local-stobj tbl
    (mv-let (words tbl)
      (tbl-insert-n n tbl)
      words)))

(defun count-word (w l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) 0)
        ((equal w (car l)) (+ 1 (count-word w (cdr l))))
        (t (count-word w (cdr l)))))

; Teeth by evaluation: the table holds exactly its capacity; the 65th insert
; and every one after it is refused.
(assert-event (equal (count-word :ok (tbl-trial 64)) 64))
(assert-event (equal (count-word :ok (tbl-trial 100)) 64))
(assert-event (equal (count-word :full (tbl-trial 100)) 36))

; :resizable nil, in the logic and in execution.
(defun tbl-grow (n tbl)
  (declare (xargs :stobjs tbl :guard (natp n)))
  (resize-keys n tbl))

; Logically the identity: the theorem prover sees no growth at all.
(defthm tbl-grow-is-the-identity-in-the-logic
  (equal (tbl-grow n tbl) tbl))

(defun tbl-try-grow (n)
  (declare (xargs :guard (natp n)))
  (with-local-stobj tbl
    (mv-let (len tbl)
      (let ((tbl (tbl-grow n tbl)))
        (mv (keys-length tbl) tbl))
      len)))

; Guard-verified, and still an error when it runs.
(assert-event (eq (symbol-class 'tbl-try-grow (w state)) :common-lisp-compliant))
(must-fail (value-triple (tbl-try-grow 128)))
