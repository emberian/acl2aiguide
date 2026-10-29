; examples/transport/cursor-wide.lisp
;
; What it shows: a widened representation is an isomorphism only onto its
; image (Experiment B's partiality tooth; Kappelmann's partial Galois
; connections, fn's TRANSPORT note section 1.1).  CUR2-WIDE-P admits any
; u32 epoch, the natural reading of "two u32 columns".  The v2 row with
; epoch 2^28 and seq 0 is a CUR2-WIDE-P row whose position, 2^60, is no u60:
; CUR2->CUR1 sends it outside CUR1-P.  So the backward image condition of
; DEFISO fails at that row, and the unrestricted DEFISO is refused by name.
; cursor-iso.lisp restricts the epoch to u28, which makes the image of
; CUR1->CUR2 exactly CUR2-P, and there the isomorphism holds.
;
; Cited by examples/transport/README.md, "Experiment B".

(in-package "ACL2")
(include-book "cursor-iso")
(include-book "std/testing/must-fail" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))

(defun cur2-wide-p (x)
  (declare (xargs :guard t))
  (case-match x
    (((':registration . r) (':epoch . e) (':seq . s) (':generation . g))
     (and (unsigned-byte-p 32 r) (unsigned-byte-p 32 e) (unsigned-byte-p 32 s)
          (unsigned-byte-p 60 g)))
    (& nil)))

(defconst *cur2-wide-row* (cur2-make 7 (expt 2 28) 0 5))

; The witness.  Stated as theorems, not ASSERT-EVENT: CUR2->CUR1's guard is
; CUR2-P, which this row does not satisfy, so top-level evaluation would be
; a guard violation; the prover evaluates ground terms in the logic.
(defthm cur2-wide-witness
  (and (cur2-wide-p *cur2-wide-row*)
       (not (cur2-p *cur2-wide-row*))
       (equal (cur1-position (cur2->cur1 *cur2-wide-row*)) (expt 2 60))
       (not (cur1-p (cur2->cur1 *cur2-wide-row*))))
  :rule-classes nil)

; The image condition, false at the witness: no proof of it exists.
(defthm cur2-wide-beta-image-false
  (not (implies (cur2-wide-p *cur2-wide-row*)
                (cur1-p (cur2->cur1 *cur2-wide-row*))))
  :rule-classes nil)

; The unrestricted DEFISO is refused.  :GUARD-THMS NIL removes the guard
; conditions, so the condition that fails is :BETA-IMAGE (read in the
; prover's output: "The proof of the :BETA-IMAGE applicability condition
; fails").
(must-fail
 (defiso cur1-iso-cur2-wide
   cur1-p cur2-wide-p cur1->cur2 cur2->cur1
   :guard-thms nil
   :thm-enable :all-nonguard
   :hints (:alpha-image (("Goal" :in-theory (enable cur1->cur2 cur1-position
                                                    cur1-generation)))
           :beta-image (("Goal" :in-theory (enable cur2->cur1 cur2-position
                                                   cur2-generation)))
           :beta-of-alpha (("Goal" :in-theory (enable cur1->cur2 cur2->cur1
                                                      cur1-position cur1-generation
                                                      cur2-position cur2-generation)))
           :alpha-of-beta (("Goal" :in-theory (enable cur1->cur2 cur2->cur1
                                                      cur1-position cur1-generation
                                                      cur2-position cur2-generation))))))
