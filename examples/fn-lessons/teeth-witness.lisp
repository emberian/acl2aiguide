; examples/fn-lessons/teeth-witness.lisp
;
; What it shows: teeth as concrete witnesses, checked by assert-event.  A
; keystone ships with a positive witness (the hypotheses hold, the
; conclusion holds, and the step did something) and one violating value per
; hypothesis (the hypothesis false, the conclusion false).  Searching for the
; violating value of a hypothesis that has none shows the hypothesis is
; unnecessary: here the first statement's NATP hypothesis has no
; counterexample, and the keystone is restated without it
; (:doc assert-event; fn docs/proof-style.md section 5).
;
; Cited by fn-lessons/23-teeth.md, "The shape to copy".

(in-package "ACL2")

(defun bounded-push (x xs cap)
  (declare (xargs :guard (true-listp xs)))
  (if (< (len xs) (nfix cap))
      (cons x xs)
    xs))

; The statement as first written.
(defthm bounded-push-respects-cap-v0
  (implies (and (natp cap) (<= (len xs) cap))
           (<= (len (bounded-push x xs cap)) cap))
  :rule-classes nil)

; Positive witness: reachable, non-degenerate (the push happened).
(assert-event
 (let ((xs '(a)) (cap 2))
   (and (natp cap) (<= (len xs) cap)
        (equal (bounded-push 'b xs cap) '(b a))
        (<= (len (bounded-push 'b xs cap)) cap))))

; Teeth for (<= (len xs) cap): that hypothesis false, the conclusion false.
(assert-event
 (let ((xs '(a b c)) (cap 2))
   (and (natp cap)
        (not (<= (len xs) cap))
        (not (<= (len (bounded-push 'z xs cap)) cap)))))

; Searching for teeth for (natp cap): non-naturals that satisfy the other
; hypothesis still satisfy the conclusion, because NFIX turns them into 0.
(assert-event
 (and (let ((xs nil) (cap 1/2))
        (and (not (natp cap)) (<= (len xs) cap)
             (<= (len (bounded-push 'z xs cap)) cap)))
      (let ((xs '(a)) (cap 3/2))
        (and (not (natp cap)) (<= (len xs) cap)
             (<= (len (bounded-push 'z xs cap)) cap)))))

; So the keystone drops the hypothesis, and says so here.
(defthm bounded-push-respects-cap
  (implies (<= (len xs) cap)
           (<= (len (bounded-push x xs cap)) cap)))
