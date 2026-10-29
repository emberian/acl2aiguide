; examples/transport/cursor-v1.lisp
;
; What it shows: a consumer-cursor row, v1, written in two layers so that
; its users' theorems can be carried to another representation (Experiment
; B).  The row is the LOGICAL view, an alist
;   ((:registration . r) (:position . p) (:generation . g))
; with r a u32 and p, g u60, the column kinds of fn2's DEFCOLUMNS
; declaration language (fn2/books/columns.lisp); the generation column
; plays the part of fn2-pool's GEN, which rejects a stale handle
; (fn2-pool-handle-code returns :STALE when the presented generation is not
; the slot's, fn2/books/pool.lisp:46-50).
;
; Layer 1, the base functions: CUR1-P (the row recognizer), CUR1-POSITION,
; CUR1-GENERATION, CUR1-WITH-POSITION.  Layer 2, the users: CUR1-ADVANCE
; (forward-only) and CUR1-ACCEPTS-TOKEN, with their theorems.  The users
; touch the row only through layer 1; that is what lets cursor-iso.lisp
; carry them (a theorem transports only if it is stated through the
; interface).
;
; The recognizer is named CUR1-P, not CUR1-ROWP: propagate-iso names each
; new event by substituting the isomorphism's codomain name for its domain
; name in the old event's name, dropping a trailing "-P" from both
; (string-subst-remove-p, kestrel/apt/lift-iso.lisp).  With CUR1-P and
; CUR2-P, CUR1-ADVANCE-MONOTONE becomes CUR2-ADVANCE-MONOTONE.
;
; Cited by examples/transport/README.md, "Experiment B".

(in-package "ACL2")

; The row is exactly this alist, keys in this order (CASE-MATCH expands to
; CAR/CDR tests, which the prover destructures directly).
(defun cur1-p (x)
  (declare (xargs :guard t))
  (case-match x
    (((':registration . r) (':position . p) (':generation . g))
     (and (unsigned-byte-p 32 r) (unsigned-byte-p 60 p) (unsigned-byte-p 60 g)))
    (& nil)))

(defun cur1-make (reg pos gen)
  (declare (xargs :guard t))
  (list (cons :registration reg) (cons :position pos) (cons :generation gen)))

(defun cur1-registration (row)
  (declare (xargs :guard (cur1-p row)))
  (cdr (assoc-equal :registration row)))

(defun cur1-position (row)
  (declare (xargs :guard (cur1-p row)))
  (cdr (assoc-equal :position row)))

(defun cur1-generation (row)
  (declare (xargs :guard (cur1-p row)))
  (cdr (assoc-equal :generation row)))

(defun cur1-with-position (row p)
  (declare (xargs :guard (cur1-p row)))
  (if (unsigned-byte-p 60 p)
      (cur1-make (cur1-registration row) p (cur1-generation row))
    row))

; ---------------------------------------------------------------------------
; Base lemmas (v1, hand-written; carried to v2 by propagate-iso).

(defthm cur1-position-of-cur1-with-position
  (implies (cur1-p row)
           (equal (cur1-position (cur1-with-position row p))
                  (if (unsigned-byte-p 60 p) p (cur1-position row)))))

; Stated under CUR1-P although it holds without it: propagate-iso carries a
; theorem through the isomorphism only where its hypotheses put the row in
; the isomorphism's domain (the unconditional form fails to transport; see
; README.md, "Experiment B").
(defthm cur1-generation-of-cur1-with-position
  (implies (cur1-p row)
           (equal (cur1-generation (cur1-with-position row p))
                  (cur1-generation row))))

(defthm cur1-p-of-cur1-with-position
  (implies (cur1-p row)
           (cur1-p (cur1-with-position row p))))

(defthm cur1-with-position-of-cur1-with-position
  (implies (cur1-p row)
           (equal (cur1-with-position (cur1-with-position row p) p)
                  (cur1-with-position row p))))

(defthm natp-of-cur1-position
  (implies (cur1-p row)
           (natp (cur1-position row)))
  :rule-classes :type-prescription)

(in-theory (disable cur1-position cur1-generation cur1-with-position))

; ---------------------------------------------------------------------------
; The users.

; Forward-only: a request below the current position leaves the row alone.
(defun cur1-advance (row p)
  (declare (xargs :guard (cur1-p row)))
  (if (and (natp p) (<= (cur1-position row) p))
      (cur1-with-position row p)
    row))

; Stale-incarnation rejection: a token is accepted only at its generation.
(defun cur1-accepts-token (row token)
  (declare (xargs :guard (cur1-p row)))
  (equal token (cur1-generation row)))

(defthm cur1-advance-monotone
  (implies (cur1-p row)
           (<= (cur1-position row) (cur1-position (cur1-advance row p)))))

(defthm cur1-advance-idempotent
  (implies (cur1-p row)
           (equal (cur1-advance (cur1-advance row p) p)
                  (cur1-advance row p))))

(defthm cur1-advance-rowp
  (implies (cur1-p row)
           (cur1-p (cur1-advance row p))))

(defthm cur1-advance-keeps-token
  (implies (cur1-p row)
           (equal (cur1-accepts-token (cur1-advance row p) token)
                  (cur1-accepts-token row token))))

(assert-event
 (let ((row (cur1-make 7 100 5)))
   (and (cur1-p row)
        (equal (cur1-position (cur1-advance row 200)) 200)
        (equal (cur1-position (cur1-advance row 50)) 100)
        (cur1-accepts-token (cur1-advance row 200) 5)
        (not (cur1-accepts-token (cur1-advance row 200) 4)))))
