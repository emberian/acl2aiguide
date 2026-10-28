; acl2aiguide example: an mbe/guard pair whose :exec is a fixnum loop over a
; fixed-size stobj array, and the theorem that equates it to a list recursion.
;
; Cited by humans/05-high-performance.md, sections "What runs when" and
; "Static allocation: fixed-size stobjs".
;
; What it shows:
;   - a stobj array of (unsigned-byte 61) words, :resizable nil, :inline t
;     (fn's books/msgid-linear-exec.lisp page shape, cut down to one page);
;   - the two element facts the guard proof needs (natp by
;     :type-prescription, the bound by :linear), because a type declaration's
;     obligation is about (nth i (car tagtab)) once the recognizer opens;
;   - the :exec loop: tail recursive, every formal declared with `type',
;     every arithmetic result wrapped in `the', the termination test written
;     as an mbe so the raw code compares two fixnums;
;   - the :logic side: an index recursion over the same stobj (an mbe's
;     :logic obeys the stobj discipline too: (nth *tagi* tagtab) there is a
;     translate error, so the list view lives in a theorem, not in the mbe);
;   - the guard obligation of the mbe, discharged by count-tag-loop-is-rec,
;     and the list theorem count-tag-st-is-count-tag that every caller uses.

(in-package "ACL2")

(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defconst *slots* 1024)

(defstobj tagtab
  (tag :type (array (unsigned-byte 61) (*slots*)) :initially 0 :resizable nil)
  :inline t)

; The specification: a list recursion, the thing proofs reason about.
(defun count-tag (x l)
  (declare (xargs :guard (true-listp l)))
  (cond ((endp l) 0)
        ((equal x (car l)) (+ 1 (count-tag x (cdr l))))
        (t (count-tag x (cdr l)))))

; The first draft, kept as a record.  With only a rewrite rule concluding
; (unsigned-byte-p 61 (nth i l)), the loop's guard proof leaves goals such as
; (ACL2-NUMBERP (NTH I (CAR TAGTAB))) open, and the definition is refused.
(local (defthm tagp-nth-is-word-draft
         (implies (and (tagp l) (natp i) (< i (len l)))
                  (unsigned-byte-p 61 (nth i l)))
         :hints (("Goal" :in-theory (enable nth)))))

(local
 (must-fail
  (defun count-tag-loop-draft-1 (x i acc tagtab)
    (declare (xargs :stobjs tagtab
                    :guard (and (natp i) (natp acc) (<= i *slots*) (<= acc i))
                    :measure (nfix (- *slots* (nfix i))))
             (type (unsigned-byte 61) x acc)
             (type (integer 0 1024) i))
    (if (mbe :logic (or (not (natp i)) (>= i *slots*)) :exec (= i *slots*))
        acc
      (count-tag-loop-draft-1 x (the (integer 0 1024) (+ 1 i))
                              (if (= x (the (unsigned-byte 61) (tagi i tagtab)))
                                  (the (unsigned-byte 61) (+ 1 acc))
                                acc)
                              tagtab)))))

; The element facts.  With tagtabp open, a guard goal about (tagi i tagtab)
; reads (nth i (car tagtab)); these two rules answer it.
(defthm tagp-nth-natp
  (implies (and (tagp l) (natp i) (< i (len l)))
           (natp (nth i l)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable nth))))

(defthm tagp-nth-below
  (implies (and (tagp l) (natp i) (< i (len l)))
           (< (nth i l) (expt 2 61)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable nth))))

; The second draft, kept as a record: the element facts are in place, but the
; :guard starts with (<= i *slots*), whose own guard obligation is left as
; (RATIONALP I), undischarged by the type declaration of I.  Refused.
(local
 (must-fail
  (defun count-tag-loop-draft-2 (x i acc tagtab)
    (declare (xargs :stobjs tagtab
                    :guard (and (<= i *slots*) (<= acc i))
                    :measure (nfix (- *slots* (nfix i))))
             (type (unsigned-byte 61) x acc)
             (type (integer 0 1024) i))
    (if (mbe :logic (or (not (natp i)) (>= i *slots*)) :exec (= i *slots*))
        acc
      (count-tag-loop-draft-2 x (the (integer 0 1024) (+ 1 i))
                              (if (= x (the (unsigned-byte 61) (tagi i tagtab)))
                                  (the (unsigned-byte 61) (+ 1 acc))
                                acc)
                              tagtab)))))

; The executable loop.  The :guard leads with (natp i) (natp acc).
(defun count-tag-loop (x i acc tagtab)
  (declare (xargs :stobjs tagtab
                  :guard (and (natp i) (natp acc) (<= i *slots*) (<= acc i))
                  :measure (nfix (- *slots* (nfix i))))
           (type (unsigned-byte 61) x acc)
           (type (integer 0 1024) i))
  (if (mbe :logic (or (not (natp i)) (>= i *slots*)) :exec (= i *slots*))
      acc
    (count-tag-loop x
                    (the (integer 0 1024) (+ 1 i))
                    (if (= x (the (unsigned-byte 61) (tagi i tagtab)))
                        (the (unsigned-byte 61) (+ 1 acc))
                      acc)
                    tagtab)))

; The logical body the mbe exposes to proofs: total, no accumulator.
(defun count-tag-rec (x i tagtab)
  (declare (xargs :stobjs tagtab
                  :guard (and (natp i) (<= i *slots*))
                  :measure (nfix (- *slots* (nfix i)))))
  (if (or (not (natp i)) (>= i *slots*))
      0
    (+ (if (equal x (tagi i tagtab)) 1 0)
       (count-tag-rec x (+ 1 i) tagtab))))

; The accumulator bridge: the mbe's guard obligation.
(defthm count-tag-loop-is-rec
  (implies (and (tagtabp tagtab) (natp i) (natp acc))
           (equal (count-tag-loop x i acc tagtab)
                  (+ acc (count-tag-rec x i tagtab)))))

; The tempting form, with the list view as the :logic, is refused when it is
; translated: "A single-threaded object, namely TAGTAB, is being used where
; an ordinary object is expected" (context (NTH *TAGI* TAGTAB)).
(must-fail
 (defun count-tag-st-list-logic (x tagtab)
   (declare (xargs :stobjs tagtab
                   :guard (unsigned-byte-p 61 x)))
   (mbe :logic (count-tag x (nth *tagi* tagtab))
        :exec (count-tag-loop x 0 0 tagtab))))

(defun count-tag-st (x tagtab)
  (declare (xargs :stobjs tagtab
                  :guard (unsigned-byte-p 61 x)))
  (mbe :logic (count-tag-rec x 0 tagtab)
       :exec (count-tag-loop x 0 0 tagtab)))

; The list view.
(defthm count-tag-rec-is-count-tag
  (implies (and (tagtabp tagtab) (natp i) (<= i *slots*))
           (equal (count-tag-rec x i tagtab)
                  (count-tag x (nthcdr i (nth *tagi* tagtab))))))

(defthm count-tag-st-is-count-tag
  (implies (tagtabp tagtab)
           (equal (count-tag-st x tagtab)
                  (count-tag x (nth *tagi* tagtab)))))

; The global stobj starts at its :initially value: 1024 zero words.
(assert-event (equal (count-tag-st 0 tagtab) 1024))
(assert-event (equal (count-tag-st 7 tagtab) 0))

; Guard verification is what makes the raw loop the one that runs.
(assert-event (eq (symbol-class 'count-tag-st (w state)) :common-lisp-compliant))
(assert-event (eq (symbol-class 'count-tag-loop (w state)) :common-lisp-compliant))
