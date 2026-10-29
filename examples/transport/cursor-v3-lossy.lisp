; examples/transport/cursor-v3-lossy.lisp
;
; What it shows: a lossy representation change is detected by a concrete
; behavioural witness (Experiment B's lossy tooth).  v3 drops the
; generation column: ((:registration . r) (:position . p)).  DEFMAPPING
; records the one-way relationship: v3 embeds into v1 (generation 0), so
; ALPHA-OF-BETA holds, but BETA-OF-ALPHA does not, and the DEFISO is
; refused by name.  The kernel of CUR1->CUR3 is exactly the identification
; of generations: two v1 rows differing only in generation have one v3
; image, yet one accepts token 5 and the other rejects it as stale.  So NO
; function on v3 rows can be a v3 CUR1-ACCEPTS-TOKEN: CUR3-ACCEPTS-TOKEN
; below is unconstrained, so the theorem NO-V3-TOKEN-CHECK holds of every
; function by functional instantiation.  Dropping the generation column
; breaks stale-incarnation rejection, and propagate-iso has nothing to
; propagate, because there is no isomorphism to propagate along.
;
; Cited by examples/transport/README.md, "Experiment B".

(in-package "ACL2")
(include-book "cursor-iso")
(include-book "std/util/defmapping" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(defun cur3-p (x)
  (declare (xargs :guard t))
  (case-match x
    (((':registration . r) (':position . p))
     (and (unsigned-byte-p 32 r) (unsigned-byte-p 60 p)))
    (& nil)))

(defun cur1->cur3 (row)
  (declare (xargs :guard (cur1-p row)))
  (list (cons :registration (cdr (assoc-equal :registration row)))
        (cons :position (cur1-position row))))

(defun cur3->cur1 (row)
  (declare (xargs :guard (cur3-p row)))
  (cur1-make (cdr (assoc-equal :registration row))
             (cdr (assoc-equal :position row))
             0))

(local (in-theory (enable cur1-position cur1-generation)))

; The one-way record: both images, and v3 -> v1 -> v3 is the identity.
(defmapping cur1-to-cur3
  cur1-p cur3-p cur1->cur3 cur3->cur1
  :alpha-of-beta-thm t
  :beta-of-alpha-thm nil)

; The isomorphism is refused: BETA-OF-ALPHA, v1 -> v3 -> v1 = identity,
; fails (the generation comes back as 0).
(must-fail
 (defiso cur1-iso-cur3
   cur1-p cur3-p cur1->cur3 cur3->cur1))

(defconst *cur1-r1* (cur1-make 7 100 5))
(defconst *cur1-r2* (cur1-make 7 100 6))

; The witness, evaluated: one v3 image, different token answers.
(assert-event
 (and (cur1-p *cur1-r1*) (cur1-p *cur1-r2*)
      (equal (cur1->cur3 *cur1-r1*) (cur1->cur3 *cur1-r2*))
      (cur1-accepts-token *cur1-r1* 5)
      (not (cur1-accepts-token *cur1-r2* 5))))

; The round trip loses the generation at a real row.
(assert-event (not (equal (cur3->cur1 (cur1->cur3 *cur1-r1*)) *cur1-r1*)))

; Any function on v3 rows, in the role of a v3 token check.
(encapsulate (((cur3-accepts-token * *) => *))
  (local (defun cur3-accepts-token (row token) (declare (ignore row token)) t)))

; No v3 token check agrees with v1's on both rows.
(defthm no-v3-token-check
  (not (and (equal (cur3-accepts-token (cur1->cur3 *cur1-r1*) 5)
                   (cur1-accepts-token *cur1-r1* 5))
            (equal (cur3-accepts-token (cur1->cur3 *cur1-r2*) 5)
                   (cur1-accepts-token *cur1-r2* 5))))
  :rule-classes nil)
