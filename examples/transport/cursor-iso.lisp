; examples/transport/cursor-iso.lisp
;
; What it shows: the users' theorems of cursor-v1.lisp carried to a second
; representation by APT's propagate-iso (Experiment B).  v2 splits the u60
; position into (:epoch . e) (:seq . s) with position = e * 2^32 + s.  The
; author writes, by hand, the v2 base functions, the two maps, the DEFISO,
; and for each base function its two correspondence theorems (old in terms
; of new, new in terms of old); propagate-iso writes everything else: the
; v2 users CUR2-ADVANCE and CUR2-ACCEPTS-TOKEN, the v2 versions of every v1
; theorem in the event range, and the correspondence theorems for each new
; function (:doc apt::propagate-iso; the form follows
; kestrel/apt/propagate-iso-test-1.lisp).
;
; CUR2-P restricts the epoch to e < 2^28, so that the image of CUR1->CUR2
; is exactly CUR2-P.  cursor-wide.lisp shows the unrestricted predicate
; refused.
;
; Cited by examples/transport/README.md, "Experiment B".

(in-package "ACL2")
(include-book "cursor-v1")
(include-book "kestrel/apt/propagate-iso" :dir :system)
(include-book "std/system/theorem-namep" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

; ===========================================================================
; HAND-WRITTEN: from here to the PROPAGATE-ISO form.

(defun cur2-p (x)
  (declare (xargs :guard t))
  (case-match x
    (((':registration . r) (':epoch . e) (':seq . s) (':generation . g))
     (and (unsigned-byte-p 32 r) (unsigned-byte-p 28 e) (unsigned-byte-p 32 s)
          (unsigned-byte-p 60 g)))
    (& nil)))

(defun cur2-make (reg epoch seq gen)
  (declare (xargs :guard t))
  (list (cons :registration reg) (cons :epoch epoch) (cons :seq seq)
        (cons :generation gen)))

(defun cur2-position (row)
  (declare (xargs :guard (cur2-p row)))
  (+ (* (cdr (assoc-equal :epoch row)) (expt 2 32))
     (cdr (assoc-equal :seq row))))

(defun cur2-generation (row)
  (declare (xargs :guard (cur2-p row)))
  (cdr (assoc-equal :generation row)))

(defun cur2-with-position (row p)
  (declare (xargs :guard (cur2-p row)))
  (if (unsigned-byte-p 60 p)
      (cur2-make (cdr (assoc-equal :registration row))
                 (floor p (expt 2 32)) (mod p (expt 2 32))
                 (cur2-generation row))
    row))

(defun cur1->cur2 (row)
  (declare (xargs :guard (cur1-p row)))
  (cur2-make (cdr (assoc-equal :registration row))
             (floor (cur1-position row) (expt 2 32))
             (mod (cur1-position row) (expt 2 32))
             (cur1-generation row)))

(defun cur2->cur1 (row)
  (declare (xargs :guard (cur2-p row)))
  (cur1-make (cdr (assoc-equal :registration row))
             (cur2-position row)
             (cur2-generation row)))

(local (in-theory (enable cur1-position cur1-generation cur1-with-position)))

(defiso cur1-iso-cur2
  cur1-p cur2-p cur1->cur2 cur2->cur1
  :thm-enable :all-nonguard)

; The correspondence theorems, two per base function.

(defthmd cur1-position-->cur2
  (implies (cur1-p row)
           (equal (cur1-position row) (cur2-position (cur1->cur2 row)))))
(defthmd cur2-position-->cur1
  (implies (cur2-p row)
           (equal (cur2-position row) (cur1-position (cur2->cur1 row)))))

(defthmd cur1-generation-->cur2
  (implies (cur1-p row)
           (equal (cur1-generation row) (cur2-generation (cur1->cur2 row)))))
(defthmd cur2-generation-->cur1
  (implies (cur2-p row)
           (equal (cur2-generation row) (cur1-generation (cur2->cur1 row)))))

(defthmd cur1-with-position-->cur2
  (implies (cur1-p row)
           (equal (cur1-with-position row p)
                  (cur2->cur1 (cur2-with-position (cur1->cur2 row) p)))))
(defthmd cur2-with-position-->cur1
  (implies (cur2-p row)
           (equal (cur2-with-position row p)
                  (cur1->cur2 (cur1-with-position (cur2->cur1 row) p)))))

(in-theory (disable cur2-position cur2-generation cur2-with-position
                    cur1->cur2 cur2->cur1))

(apt::propagate-iso cur1-iso-cur2
  ((cur1-position cur2-position cur1-position-->cur2 cur2-position-->cur1
                  (cur1-p) => *)
   (cur1-generation cur2-generation cur1-generation-->cur2 cur2-generation-->cur1
                    (cur1-p) => *)
   (cur1-with-position cur2-with-position
                       cur1-with-position-->cur2 cur2-with-position-->cur1
                       (cur1-p *) => cur1-p))
  :first-event cur1-position-of-cur1-with-position
  :last-event cur1-advance-keeps-token)

; END OF HAND-WRITTEN PART (the checks below are acceptance, not transport).
; ===========================================================================

(assert-event (theorem-namep 'cur2-advance-monotone (w state)))
(assert-event (theorem-namep 'cur2-advance-idempotent (w state)))
(assert-event (theorem-namep 'cur2-advance-rowp (w state)))
(assert-event (theorem-namep 'cur2-advance-keeps-token (w state)))
