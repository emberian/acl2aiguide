; examples/stobjs/local-stobj.lisp
;
; with-local-stobj: a pure function that uses a scratch stobj internally.
; The mv-let inside binds the stobj among its variables and the body
; returns ONLY the ordinary values, never the stobj (:DOC with-local-stobj:
; the body "does not even reference stobj-name").  A stobj argument is
; always a variable, never a call: bind with let first.
;
; Cited by humans/03-modelling-data.md, "Local stobjs".

(in-package "ACL2")

; A scratch histogram of byte values, :non-executable so that no global
; instance is allocated (:DOC defstobj, "Specifying Non-executable Stobjs").
(defstobj hist
  (bins :type (array (unsigned-byte 60) (256)) :initially 0)
  :inline t
  :non-executable t)

(defun byte-listp (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (unsigned-byte-p 8 (car xs)) (byte-listp (cdr xs)))))

; The guard proofs over an array field need the list facts about its
; recognizer: a read is in type, and an in-type write keeps the type.
; Stated as a type fact and a linear fact: a rewrite rule concluding
; (UNSIGNED-BYTE-P 60 (NTH I L)) never fires, because UNSIGNED-BYTE-P is
; enabled and the goal shows (< (NTH I L) 1152921504606846976) instead.
(defthm binsp-nth-natp
  (implies (and (binsp l) (natp i) (< i (len l)))
           (natp (nth i l)))
  :rule-classes :type-prescription)

(defthm binsp-nth-bound
  (implies (and (binsp l) (natp i) (< i (len l)))
           (< (nth i l) 1152921504606846976))
  :rule-classes :linear)

(defthm binsp-of-update-nth
  (implies (and (binsp l) (natp i) (< i (len l)) (unsigned-byte-p 60 v))
           (binsp (update-nth i v l))))

(defun count-bytes (xs hist)
  (declare (xargs :stobjs hist
                  :guard (byte-listp xs)))
  (if (atom xs)
      hist
    (let* ((b (car xs))
           (old (binsi b hist))
           (hist (update-binsi b (if (< old (1- (expt 2 60))) (+ 1 old) old)
                               hist)))
      (count-bytes (cdr xs) hist))))

; Callers of count-bytes need its result to satisfy the stobj recognizer.
(defthm histp-of-count-bytes
  (implies (and (histp hist) (byte-listp xs))
           (histp (count-bytes xs hist))))

; The answer AND a second value come out of the local stobj.  Note the
; shape: the mv-let binds (top n hist), the body is (mv top n).
(defun most-common-byte-loop (i best best-n hist)
  (declare (xargs :stobjs hist
                  :guard (and (natp i) (<= i 256) (natp best) (natp best-n))
                  :measure (nfix (- 256 i))))
  (if (or (not (natp i)) (>= i 256))
      (mv best best-n)
    (let ((c (binsi i hist)))
      (if (> c best-n)
          (most-common-byte-loop (+ 1 i) i c hist)
        (most-common-byte-loop (+ 1 i) best best-n hist)))))

(defun most-common-byte (xs)
  (declare (xargs :guard (byte-listp xs)))
  (with-local-stobj
   hist
   (mv-let (top n hist)
     (let ((hist (count-bytes xs hist)))
       (mv-let (top n)
         (most-common-byte-loop 0 0 0 hist)
         (mv top n hist)))
     (mv top n))))

; Two values come back, so the check reads them with MV-LIST.
(assert-event
 (equal (mv-list 2 (most-common-byte '(1 2 2 3 2 9 1)))
        '(2 3)))

; The two shapes that do NOT work, recorded as must-fail so the book
; demonstrates them.  The first returns the local stobj from the body; the
; second passes a call where the stobj variable must appear.
(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (defun bad-returns-stobj (xs)
   (with-local-stobj
    hist
    (mv-let (top n hist)
      (let ((hist (count-bytes xs hist)))
        (mv-let (top n) (most-common-byte-loop 0 0 0 hist)
          (mv top n hist)))
      (mv top n hist)))))

(must-fail
 (defun bad-stobj-call-argument (xs)
   (with-local-stobj
    hist
    (mv-let (top n hist)
      (mv-let (top n) (most-common-byte-loop 0 0 0 (count-bytes xs hist))
        (mv top n hist))
      (mv top n)))))

; The logical meaning is available to proofs: the function is total and
; its value is a two-element list.
(defthm most-common-byte-shape
  (true-listp (most-common-byte xs))
  :rule-classes :type-prescription)
