; examples/stobjs/absstobj-counter.lisp
;
; A complete small abstract stobj: a counter whose logical value is a pair
; (VALUE . OPS) and whose executable is a two-field concrete stobj.  Every
; obligation that `defabsstobj' demands is written out, as ACL2 prints it
; when the event is submitted without them, and proved before the event.
; The increment and the reset each update TWO fields of the foundation, so
; each needs `:protect t' (without it ACL2 refuses the event: "appears
; capable of modifying the foundational stobj ... non-atomically").
;
; Cited by humans/03-modelling-data.md, "Abstract stobjs".

(in-package "ACL2")

; The foundation: an ordinary stobj with two natural-number fields.
(defstobj ctr$c
  (ctr$c-val :type (integer 0 *) :initially 0)
  (ctr$c-ops :type (integer 0 *) :initially 0))

; The logical side: a cons of two naturals.  These :logic functions are used
; only as the logic of the primitives (:DOC defabsstobj, "a good discipline").
(defun ctr$ap (x)
  (declare (xargs :guard t))
  (and (consp x) (natp (car x)) (natp (cdr x))))

(defun create-ctr$a ()
  (declare (xargs :guard t))
  (cons 0 0))

(defun ctr$a-val (x)
  (declare (xargs :guard (ctr$ap x)))
  (car x))

(defun ctr$a-ops (x)
  (declare (xargs :guard (ctr$ap x)))
  (cdr x))

(defun ctr$a-incr (x)
  (declare (xargs :guard (ctr$ap x)))
  (cons (+ 1 (car x)) (+ 1 (cdr x))))

(defun ctr$a-reset (x)
  (declare (xargs :guard (ctr$ap x)))
  (cons 0 (+ 1 (cdr x))))

; The executable side: two updates each, so not atomic.
(defun ctr$c-incr (ctr$c)
  (declare (xargs :stobjs ctr$c))
  (let ((ctr$c (update-ctr$c-val (+ 1 (ctr$c-val ctr$c)) ctr$c)))
    (update-ctr$c-ops (+ 1 (ctr$c-ops ctr$c)) ctr$c)))

(defun ctr$c-reset (ctr$c)
  (declare (xargs :stobjs ctr$c))
  (let ((ctr$c (update-ctr$c-val 0 ctr$c)))
    (update-ctr$c-ops (+ 1 (ctr$c-ops ctr$c)) ctr$c)))

; The correspondence: stated once.  It need not execute (defun-nx).
(defun-nx ctr$corr (ctr$c x)
  (and (equal (ctr$c-val ctr$c) (car x))
       (equal (ctr$c-ops ctr$c) (cdr x))))

; The obligations, exactly as `defabsstobj' prints them when they are missing.
(defthm create-ctr{correspondence}
  (ctr$corr (create-ctr$c) (create-ctr$a))
  :rule-classes nil)

(defthm create-ctr{preserved}
  (ctr$ap (create-ctr$a))
  :rule-classes nil)

(defthm ctr-val{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (equal (ctr$c-val ctr$c) (ctr$a-val ctr)))
  :rule-classes nil)

(defthm ctr-ops{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (equal (ctr$c-ops ctr$c) (ctr$a-ops ctr)))
  :rule-classes nil)

(defthm ctr-incr{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (ctr$corr (ctr$c-incr ctr$c) (ctr$a-incr ctr)))
  :rule-classes nil)

(defthm ctr-incr{preserved}
  (implies (ctr$ap ctr) (ctr$ap (ctr$a-incr ctr)))
  :rule-classes nil)

(defthm ctr-reset{correspondence}
  (implies (and (ctr$corr ctr$c ctr) (ctr$ap ctr))
           (ctr$corr (ctr$c-reset ctr$c) (ctr$a-reset ctr)))
  :rule-classes nil)

(defthm ctr-reset{preserved}
  (implies (ctr$ap ctr) (ctr$ap (ctr$a-reset ctr)))
  :rule-classes nil)

(defabsstobj ctr
  :foundation ctr$c
  :recognizer (ctrp :logic ctr$ap :exec ctr$cp)
  :creator (create-ctr :logic create-ctr$a :exec create-ctr$c)
  :corr-fn ctr$corr
  :exports ((ctr-val :logic ctr$a-val :exec ctr$c-val)
            (ctr-ops :logic ctr$a-ops :exec ctr$c-ops)
            (ctr-incr :logic ctr$a-incr :exec ctr$c-incr :protect t)
            (ctr-reset :logic ctr$a-reset :exec ctr$c-reset :protect t)))

; Theorems are about the logical pair.  The two below need no hypothesis.
; The recognizer is still a hypothesis wherever the claim depends on it: the
; logic of a stobj primitive is total and is applied to arbitrary objects in
; a theorem, so (ctr-val ctr) need not be a number there.  What the
; {preserved} obligations buy is that a guard-verified caller never has to
; recompute (ctrp ctr) at run time.
(defthm ctr-val-of-ctr-incr
  (equal (ctr-val (ctr-incr ctr)) (+ 1 (ctr-val ctr))))

(defthm ctr-ops-grows
  (and (equal (ctr-ops (ctr-incr ctr)) (+ 1 (ctr-ops ctr)))
       (equal (ctr-ops (ctr-reset ctr)) (+ 1 (ctr-ops ctr)))))

; A caller in the ordinary single-threaded style.
(defun ctr-incr-n (n ctr)
  (declare (xargs :stobjs ctr :guard (natp n)))
  (if (zp n)
      ctr
    (let ((ctr (ctr-incr ctr)))
      (ctr-incr-n (- n 1) ctr))))

; Without (ctrp ctr) this fails at n = 0: the checkpoint is
; (ACL2-NUMBERP (CAR CTR)).
(defthm ctr-val-of-ctr-incr-n
  (implies (and (natp n) (ctrp ctr))
           (equal (ctr-val (ctr-incr-n n ctr)) (+ n (ctr-val ctr)))))

; A pure function over a local counter.  The mv-let binds the stobj and
; returns only the ordinary value (:DOC with-local-stobj).
(defun count-to (n)
  (declare (xargs :guard (natp n)))
  (with-local-stobj
   ctr
   (mv-let (v ctr)
     (let ((ctr (ctr-incr-n n ctr)))
       (mv (ctr-val ctr) ctr))
     v)))

(assert-event (equal (count-to 1000) 1000))
