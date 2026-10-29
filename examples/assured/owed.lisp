; examples/assured/owed.lisp
;
; What it shows: an honest ledger of claims, kept in the world rather than
; in prose, in the shape of fn2's DEFTHM-OWED (fn2/books/owed.lisp
; @127f7b877) and the generated fn2/docs/OWED.md.
;
;   (defthm-owed NAME (VARS) FORMULA :teeth (FN ...))
;      translates FORMULA (it must name real functions with their real
;      arities: a DEFUN-NX of the statement is admitted, so a typo is an
;      error now, not a surprise when the proof is attempted), records a
;      row with status :OWED, and proves nothing.  :TEETH must name
;      zero-argument evaluating functions, never prose; each is run and
;      must return exactly T.
;   (defthm-claimed NAME FORMULA ...)
;      is DEFTHM, plus a row with status :PROVED and the same formula.
;
;
; SAT-RUN-MONOTONE, the owed row below, is false at x = 256 (proved here as
; SAT-RUN-MONOTONE-FALSE-AT-256): recorded, translated, teeth passing, and
; not a theorem.
;
; CLAIM-COUNTS reads the table and answers (proved owed): the numbers a
; status page prints come from the world, never from a hand-kept count.
;
; Cited by assured/humans/07-honest-costs.md, assured/ai/07-honest-costs.md
; and assured/humans/06-metatheory-split.md.

(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defun owed-teethp (names)
  (declare (xargs :guard t))
  (if (atom names) (null names)
    (and (symbolp (car names)) (car names)
         (not (keywordp (car names))) (not (eq (car names) t))
         (owed-teethp (cdr names)))))

(defun owed-tooth-events (teeth)
  (declare (xargs :guard t))
  (if (atom teeth) nil
    (cons `(assert-event (equal (,(car teeth)) t))
          (owed-tooth-events (cdr teeth)))))

(defmacro defthm-owed (name vars formula &key teeth)
  (if (and (consp teeth) (owed-teethp teeth))
      `(progn
         (defun-nx ,(intern-in-package-of-symbol
                     (concatenate 'string (symbol-name name) "$OWED") name)
           ,vars ,formula)
         ,@(owed-tooth-events teeth)
         (table claims ',name '(:formula ,formula :teeth ,teeth :status :owed)))
    `(make-event
      (er soft 'defthm-owed
          "~x0: :teeth must name evaluating functions, not prose or forms."
          ',name))))

(defmacro defthm-claimed (name formula &rest args)
  `(progn (defthm ,name ,formula ,@args)
          (table claims ',name '(:formula ,formula :status :proved))))

(defun claim-counts-aux (rows proved owed)
  (declare (xargs :guard (and (natp proved) (natp owed))))
  (if (atom rows) (list proved owed)
    (let ((status (and (consp (car rows)) (true-listp (cdar rows))
                       (cadr (member-eq :status (cdar rows))))))
      (claim-counts-aux (cdr rows)
                        (if (eq status :proved) (+ 1 proved) proved)
                        (if (eq status :owed) (+ 1 owed) owed)))))

(defun claim-counts (wrld)
  (declare (xargs :guard (plist-worldp wrld)))
  (claim-counts-aux (table-alist 'claims wrld) 0 0))

; ----------------------------------------------------------------------
; A tiny subject: a saturating counter.

(defconst *sat-max* 255)
(defun sat-inc (x) (declare (xargs :guard (natp x))) (if (< x *sat-max*) (+ 1 x) *sat-max*))

(defthm-claimed sat-inc-bounded
  (implies (natp x) (<= (sat-inc x) (max x *sat-max*))))

; Owed: monotone over any run of increments.  The teeth evaluate a
; positive case and a negative case (a broken sibling that wraps to 0).
(defun sat-run (x n) (declare (xargs :guard (and (natp x) (natp n)))) (if (zp n) x (sat-run (sat-inc x) (- n 1))))
(defun wrap-inc (x) (declare (xargs :guard (natp x))) (if (< x *sat-max*) (+ 1 x) 0))

(defun sat-run-teeth ()
  (declare (xargs :guard t))
  (and (equal (sat-run 250 10) 255)                ; positive: saturates
       (< (wrap-inc 255) 255)                       ; negative: the sibling wraps
       t))

(defthm-owed sat-run-monotone (x n)
  (implies (and (natp x) (natp n)) (<= x (sat-run x n)))
  :teeth (sat-run-teeth))

; The owed statement is FALSE outside the domain its author had in mind:
; SAT-INC of 256 is 255, so one step from 256 goes down.  The teeth passed
; and the book certified with the row recorded; only a witness search over
; the degenerate corner finds it.  An owed row is a conjecture.
(defthm sat-run-monotone-false-at-256
  (not (<= 256 (sat-run 256 1))))

; The table holds the exact statement, and the counts come from it.
(assert-event (equal (claim-counts (w state)) '(1 1)))
(assert-event
 (equal (cadr (member-eq :status (cdr (assoc-eq 'sat-run-monotone
                                                (table-alist 'claims (w state))))))
        :owed))

; Refused: teeth that are prose.
(must-fail
 (defthm-owed sat-run-bounded (x n)
   (implies (and (natp x) (natp n)) (<= (sat-run x n) (max x *sat-max*)))
   :teeth ("evaluated by hand in the REPL")))

; Refused: a statement that does not translate (an undefined function).
(must-fail
 (defthm-owed sat-run-fixed (x n)
   (implies (natp x) (equal (sat-run x n) (sat-fixpoint x)))
   :teeth (sat-run-teeth)))
