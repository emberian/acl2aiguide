; acl2aiguide example (a test book): which side of an mbe runs, observed by
; what it allocates.
;
; Cited by humans/05-high-performance.md, section "What runs when".
;
; One function, two copies: COUNT-EVENS is guard-verified, COUNT-EVENS-
; UNVERIFIED has the same guard and body but :verify-guards nil.  The mbe's
; :logic builds a list and takes its length (16 bytes per even element); its
; :exec counts in a loop and allocates nothing.  So the bytes time$ reports
; say which side ran:
;   - the verified function, called from a verified caller: raw Lisp, :exec;
;   - the unverified function through ec-call from a verified caller: its
;     executable counterpart (*1*), which runs :logic;
;   - the unverified function called from a :program-mode function: raw
;     Lisp, so :exec, and no callee guard is evaluated;
;   - the verified function called from an unverified caller: the caller's
;     *1* calls the callee's *1*, which checks the callee's guard once and
;     then runs the callee's raw code, so :exec.
; The printed lines are the record (this book's .cert.out).

(in-package "ACL2")

(defun keep-evens (l)
  (declare (xargs :guard (integer-listp l)))
  (cond ((endp l) nil)
        ((evenp (car l)) (cons (car l) (keep-evens (cdr l))))
        (t (keep-evens (cdr l)))))

(defun count-evens-loop (l acc)
  (declare (xargs :guard (and (integer-listp l) (natp acc))))
  (cond ((endp l) acc)
        ((evenp (car l)) (count-evens-loop (cdr l) (+ 1 acc)))
        (t (count-evens-loop (cdr l) acc))))

(defthm count-evens-loop-is-len-keep-evens
  (implies (natp acc)
           (equal (count-evens-loop l acc)
                  (+ acc (len (keep-evens l))))))

(defun count-evens (l)
  (declare (xargs :guard (integer-listp l)))
  (mbe :logic (len (keep-evens l))
       :exec (count-evens-loop l 0)))

(defun count-evens-unverified (l)
  (declare (xargs :guard (integer-listp l) :verify-guards nil))
  (mbe :logic (len (keep-evens l))
       :exec (count-evens-loop l 0)))

(defun ints-upto (n acc)
  (declare (xargs :guard (and (natp n) (true-listp acc))))
  (if (zp n) acc (ints-upto (- n 1) (cons n acc))))

(defthm integer-listp-of-ints-upto
  (implies (integer-listp acc) (integer-listp (ints-upto n acc))))

; A verified caller: (count-evens l) is a raw call; the ec-call forces the
; unverified function's executable counterpart.
(defun what-runs-verified (n)
  (declare (xargs :guard (natp n)))
  (let ((l (ints-upto n nil)))
    (list (time$ (count-evens l)
                 :mintime 0
                 :msg "verified callee from a verified caller: ~sa bytes~%")
          (time$ (ec-call (count-evens-unverified l))
                 :mintime 0
                 :msg "unverified callee by ec-call from a verified caller: ~sa bytes~%"))))

; A :program-mode caller.
(defun what-runs-program (n)
  (declare (xargs :mode :program))
  (let ((l (ints-upto n nil)))
    (time$ (count-evens-unverified l)
           :mintime 0
           :msg "unverified callee from a :program caller: ~sa bytes~%")))

; An unverified :logic caller.
(defun what-runs-unverified-caller (n)
  (declare (xargs :guard (natp n) :verify-guards nil))
  (let ((l (ints-upto n nil)))
    (time$ (count-evens l)
           :mintime 0
           :msg "verified callee from an unverified caller: ~sa bytes~%")))

(assert-event (equal (what-runs-verified 100000) (list 50000 50000)))
(assert-event (equal (what-runs-program 100000) 50000))
(assert-event (equal (what-runs-unverified-caller 100000) 50000))

; The symbol classes the evaluation depends on.
(assert-event (eq (symbol-class 'count-evens (w state)) :common-lisp-compliant))
(assert-event (eq (symbol-class 'count-evens-unverified (w state)) :ideal))
(assert-event (eq (symbol-class 'what-runs-program (w state)) :program))
