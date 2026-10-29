; examples/assured/summary-upto.lisp
;
; What it shows: the summary certificate in its cheaper form, the graph of
; the converter up to a congruence, which fn2's reading of up-to
; techniques proposed as a second form of the guide's fold contract
; (HIGHER-STRUCTURES.md section 6, "fc-graph-upto-fold", verdict USE NOW;
; the first form is FC-REL-FOLD in examples/transport/fold-contract.lisp).
;
; The generic contract: a history step and a summary step, their
; observations, a converter CONV from histories to summaries, and an
; equivalence GU-EQUIV on summaries (two summaries with the same meaning).
; The constraints are exactly what ACL2's rewriter already knows how to
; use without a quantifier:
;   (defequiv gu-equiv)                                  ; an equivalence
;   (defcong gu-equiv gu-equiv (gu-s-step s e) 1)        ; step respects it
;   (defcong gu-equiv equal    (gu-s-obs s q) 1)         ; obs respects it
;   step equation, per event:  (gu-equiv (gu-s-step (gu-conv h) e)
;                                        (gu-conv (gu-h-step h e)))
;   edge:                      (equal (gu-h-obs h q) (gu-s-obs (gu-conv h) q))
; GU-GRAPH-UPTO-FOLD concludes that any summary equivalent to CONV of a
; history stays equivalent to CONV of the extended history after every
; suffix, and the observations agree.  Compared with FC-REL-FOLD: no
; DEFUN-SK relation, and the converter theorem (the G0 square) and the
; step lemmas are one obligation per event kind.
;
; The instance is the counterexample that showed a plain homomorphism is
; too strong (fn2's UNIVERSAL-CONSTRUCTIONS.md section 2.2, Astra's
; "(n mod 2, 0)", cited in HIGHER-STRUCTURES.md section 6): the history is
; a list of :inc events, the observation is the parity of their count, and
; the summary is (PARITY . STEPS), where STEPS counts summary steps taken
; and is never observed.  The converter answers (PARITY . 0).  Up to
; equality the step equation is false (PARITY-STEP-NOT-HOMOMORPHISM): a
; stepped summary carries STEPS = 1, the converted one 0.  Up to "same
; parity" it holds, and the generic theorem applies.
;
; Cited by assured/humans/05-transport.md and assured/ai/05-transport.md.

(in-package "ACL2")

(encapsulate
  (((gu-h-step * *) => *) ((gu-s-step * *) => *)
   ((gu-h-obs * *) => *) ((gu-s-obs * *) => *)
   ((gu-conv *) => *) ((gu-equiv * *) => *))

  (local (defun gu-h-step (h e) (declare (ignore h e)) nil))
  (local (defun gu-s-step (s e) (declare (ignore s e)) nil))
  (local (defun gu-h-obs (h q) (declare (ignore h q)) nil))
  (local (defun gu-s-obs (s q) (declare (ignore s q)) nil))
  (local (defun gu-conv (h) (declare (ignore h)) nil))
  (local (defun gu-equiv (x y) (equal x y)))

  (defequiv gu-equiv)
  (defcong gu-equiv gu-equiv (gu-s-step s e) 1)
  (defcong gu-equiv equal (gu-s-obs s q) 1)

  (defthm gu-step-equation
    (gu-equiv (gu-s-step (gu-conv h) e) (gu-conv (gu-h-step h e))))

  (defthm gu-edge
    (equal (gu-h-obs h q) (gu-s-obs (gu-conv h) q))))

(defun gu-h-fold (h j) (if (atom j) h (gu-h-fold (gu-h-step h (car j)) (cdr j))))
(defun gu-s-fold (s j) (if (atom j) s (gu-s-fold (gu-s-step s (car j)) (cdr j))))

(defun gu-induct (s h j)
  (if (atom j) (list s h)
    (gu-induct (gu-s-step s (car j)) (gu-h-step h (car j)) (cdr j))))

(in-theory (disable (:executable-counterpart gu-h-fold)
                    (:executable-counterpart gu-s-fold)))

; One step: congruence carries the summary to CONV of the history, and the
; step equation closes the square.
(defthm gu-step-related
  (implies (gu-equiv s (gu-conv h))
           (gu-equiv (gu-s-step s e) (gu-conv (gu-h-step h e))))
  :hints (("Goal" :use ((:instance gu-equiv-implies-gu-equiv-gu-s-step-1
                                   (s-equiv (gu-conv h)))
                        (:instance gu-step-equation))
                  :in-theory (disable gu-equiv-implies-gu-equiv-gu-s-step-1
                                      gu-step-equation))))

(defthm gu-graph-upto-fold
  (implies (gu-equiv s (gu-conv h))
           (gu-equiv (gu-s-fold s j) (gu-conv (gu-h-fold h j))))
  :hints (("Goal" :induct (gu-induct s h j))))

(defthm gu-graph-upto-obs
  (implies (gu-equiv s (gu-conv h))
           (equal (gu-s-obs (gu-s-fold s j) q)
                  (gu-h-obs (gu-h-fold h j) q)))
  :hints (("Goal" :use gu-graph-upto-fold :in-theory (disable gu-graph-upto-fold))))

; ----------------------------------------------------------------------
; The instance: parity of a count, with an unobserved step counter.

(defun par-h-step (h e) (if (eq e :inc) (cons e h) h))
(defun par-count (h) (if (atom h) 0 (+ 1 (par-count (cdr h)))))
(defun par-h-obs (h q) (declare (ignore q)) (mod (par-count h) 2))

(defun par-bit (x) (if (equal x 1) 1 0))
(defun par-s-step (s e)
  (if (eq e :inc)
      (cons (- 1 (par-bit (car s))) (+ 1 (nfix (cdr s))))
    (cons (par-bit (car s)) (+ 1 (nfix (cdr s))))))
(defun par-s-obs (s q) (declare (ignore q)) (par-bit (car s)))
(defun par-conv (h) (cons (mod (par-count h) 2) 0))

(defun par-equiv (x y) (equal (par-bit (car x)) (par-bit (car y))))

(defequiv par-equiv)
(defcong par-equiv par-equiv (par-s-step s e) 1)
(defcong par-equiv equal (par-s-obs s q) 1)

(local (include-book "arithmetic-5/top" :dir :system))

(defthm par-count-natp (natp (par-count h)) :rule-classes :type-prescription)

; The per-event step equation, up to PAR-EQUIV.
(defthm par-step-equation
  (par-equiv (par-s-step (par-conv h) e) (par-conv (par-h-step h e))))

(defthm par-edge
  (equal (par-h-obs h q) (par-s-obs (par-conv h) q)))

(in-theory (disable par-equiv par-s-step par-s-obs par-conv par-h-step par-h-obs))

(defun par-h-fold (h j) (if (atom j) h (par-h-fold (par-h-step h (car j)) (cdr j))))
(defun par-s-fold (s j) (if (atom j) s (par-s-fold (par-s-step s (car j)) (cdr j))))

; Adequacy after every suffix, by functional instance only.
(defthm par-summary-adequate
  (implies (par-equiv s (par-conv h))
           (equal (par-s-obs (par-s-fold s j) q)
                  (par-h-obs (par-h-fold h j) q)))
  :hints (("Goal" :use ((:functional-instance gu-graph-upto-obs
                         (gu-h-step par-h-step) (gu-s-step par-s-step)
                         (gu-h-obs par-h-obs) (gu-s-obs par-s-obs)
                         (gu-conv par-conv) (gu-equiv par-equiv)
                         (gu-h-fold par-h-fold) (gu-s-fold par-s-fold))))))

; Teeth: up to equality, the same certificate is false.
(defthm parity-step-not-homomorphism
  (not (equal (par-s-step (par-conv nil) :inc) (par-conv (par-h-step nil :inc))))
  :hints (("Goal" :in-theory (enable par-s-step par-conv par-h-step))))

; And evaluated: a summary five steps old answers like the history.
(assert-event
 (let ((j '(:inc :noop :inc :inc :noop)))
   (and (equal (par-s-obs (par-s-fold (par-conv nil) j) :parity) 1)
        (equal (par-h-obs (par-h-fold nil j) :parity) 1)
        (equal (cdr (par-s-fold (par-conv nil) j)) 5))))
