; examples/assured/diamond.lisp
;
; What it shows: an independence diamond (fn2's G2, COHERENCE.md section
; 2.1) and the false diamond that refuted fn2's first independence
; condition (COHERENCE.md section 2.4; the Lean teeth acceptClose_* in
; fn2/meta/Fn2/Coherence.lean @dddc32d34).
;
; State: a list of positions.  An action declares the positions it reads
; and writes (its footprint).  Two actions are footprint-independent when
; neither writes what the other reads or writes.
;
;   1. FOOTPRINT-DIAMOND: two actions that each read and write one
;      position, at different positions, commute, whatever they compute
;      there (proved once, over constrained functions).
;   2. The false diamond.  Position 0 is the allocator's free count,
;      position 1 one echo row with an outstanding close, position 2 the
;      admissions the client sees.  ACCEPT (the listener) needs a free row;
;      CLOSE (the echo machine) frees its row.  From the start state
;      (free 0, row occupied, admitted 0), accept-then-close admits nobody
;      and close-then-accept admits one client: a client-visible difference.
;      Declared independent "because they are different machines", the
;      diamond is false (ACCEPT-CLOSE-NOT-DIAMOND); declared by footprints,
;      the pair is dependent at the free count and no diamond is claimed.
;
; Cited by assured/humans/03-commuting-squares.md and
; assured/ai/03-commuting-squares.md.

(in-package "ACL2")
(include-book "std/lists/update-nth" :dir :system)

; ---- 1. The generic diamond ------------------------------------------

(encapsulate (((dm-f *) => *) ((dm-g *) => *))
  (local (defun dm-f (x) x))
  (local (defun dm-g (x) x)))

; An action that reads and writes position P only.
(defun at-f (p s) (update-nth p (dm-f (nth p s)) s))
(defun at-g (q s) (update-nth q (dm-g (nth q s)) s))

(defthm footprint-diamond
  (implies (and (natp p) (natp q) (not (equal p q)))
           (equal (at-f p (at-g q s)) (at-g q (at-f p s)))))

; ---- Footprints as data -----------------------------------------------

(defun footprint-independent (fp1 fp2)
  ; FP is (reads . writes); neither writes what the other touches.
  (declare (xargs :guard (and (consp fp1) (consp fp2)
                              (eqlable-listp (car fp1)) (eqlable-listp (cdr fp1))
                              (eqlable-listp (car fp2)) (eqlable-listp (cdr fp2)))))
  (and (not (intersectp (cdr fp1) (append (car fp2) (cdr fp2))))
       (not (intersectp (cdr fp2) (append (car fp1) (cdr fp1))))))

; ---- 2. The false diamond --------------------------------------------

(defconst *free* 0)
(defconst *row* 1)
(defconst *admitted* 2)

(defun accept (s)
  ; The listener: admit if a row is free, else close the new connection.
  (if (< 0 (nfix (nth *free* s)))
      (update-nth *admitted* (+ 1 (nfix (nth *admitted* s)))
                  (update-nth *free* (- (nfix (nth *free* s)) 1) s))
    s))

(defun close-row (s)
  ; The echo machine: release its row to the allocator.
  (if (equal (nth *row* s) 1)
      (update-nth *free* (+ 1 (nfix (nth *free* s)))
                  (update-nth *row* 0 s))
    s))

(defconst *accept-footprint* (cons (list *free* *admitted*) (list *free* *admitted*)))
(defconst *close-footprint* (cons (list *row* *free*) (list *row* *free*)))

(defconst *start* (list 0 1 0))

; Evaluated: the two orders give different admissions.
(assert-event (equal (nth *admitted* (close-row (accept *start*))) 0))
(assert-event (equal (nth *admitted* (accept (close-row *start*))) 1))

; The declaration "different machines are independent" is refuted.
(defun machine-of (action) (if (eq action 'accept) :listener :echo))
(assert-event (not (equal (machine-of 'accept) (machine-of 'close-row))))

(defthm accept-close-not-diamond
  (not (equal (close-row (accept *start*)) (accept (close-row *start*)))))

; The footprint declaration classifies the pair dependent, at the free
; count, so no diamond is claimed for it.
(assert-event (not (footprint-independent *accept-footprint* *close-footprint*)))
(assert-event (equal (intersection-equal (cdr *accept-footprint*) (cdr *close-footprint*))
                     (list *free*)))

; And a pair the footprints do declare independent: two counter bumps at
; different positions, an instance of the generic diamond.
(defun bump-at (p s) (update-nth p (+ 1 (nfix (nth p s))) s))

(defthm bump-diamond
  (implies (and (natp p) (natp q) (not (equal p q)))
           (equal (bump-at p (bump-at q s)) (bump-at q (bump-at p s))))
  :hints (("Goal" :use ((:functional-instance footprint-diamond
                         (dm-f (lambda (x) (+ 1 (nfix x))))
                         (dm-g (lambda (x) (+ 1 (nfix x))))
                         (at-f bump-at) (at-g bump-at))))))

(assert-event (footprint-independent (cons '(3) '(3)) (cons '(4) '(4))))
