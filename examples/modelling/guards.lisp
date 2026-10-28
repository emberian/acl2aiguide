; examples/modelling/guards.lisp
;
; Guard verification that needs help: a THE declaration whose obligation
; rests on a fact about a recursive function, discharged by a
; :rule-classes nil lemma named in :guard-hints (fn docs/proof-style.md
; section 3); the same function defined with :verify-guards nil and verified
; later with :guard-debug; ec-call to call a function whose guards are not
; verified from one whose guards are; defun-nx for a specification that must
; not run; mbt to put a guard fact into the logic for termination.
;
; Cited by humans/03-modelling-data.md, "Guards".

(in-package "ACL2")
(include-book "arithmetic/top" :dir :system)

(defun byte-listp* (xs)
  (declare (xargs :guard t))
  (if (atom xs)
      (null xs)
    (and (unsigned-byte-p 8 (car xs)) (byte-listp* (cdr xs)))))

(defun sum-bytes (xs)
  (declare (xargs :guard (byte-listp* xs)))
  (if (atom xs)
      0
    (+ (car xs) (sum-bytes (cdr xs)))))

; The bound, stated once, :rule-classes nil: it exists to discharge a guard.
(defthm sum-bytes-bound
  (implies (byte-listp* xs)
           (and (natp (sum-bytes xs))
                (<= (sum-bytes xs) (* 255 (len xs)))))
  :rule-classes nil)

; The THE promises SBCL a 32-bit result; the guard conjecture asks for
; (unsigned-byte-p 32 (sum-bytes xs)), which needs the bound.
(defun checksum32 (xs)
  (declare (xargs :guard (and (byte-listp* xs) (< (len xs) 1000000))
                  :guard-hints (("Goal" :use ((:instance sum-bytes-bound))))))
  (the (unsigned-byte 32) (sum-bytes xs)))

; The same function, guards deferred and then verified with :guard-debug,
; which tags each obligation with the call it came from (:DOC guard-debug).
(defun checksum32-late (xs)
  (declare (xargs :guard (and (byte-listp* xs) (< (len xs) 1000000))
                  :verify-guards nil))
  (the (unsigned-byte 32) (sum-bytes xs)))

(verify-guards checksum32-late
  :guard-debug t
  :hints (("Goal" :use ((:instance sum-bytes-bound)))))

; ---------------------------------------------------------------------------
; ec-call: SPEC has no verified guards (none were asked for), so a
; guard-verified caller may not call it directly; wrapped in ec-call the
; call generates no guard obligation and runs SPEC's executable
; counterpart (:DOC ec-call).

(defun spec-reverse (x)
  (declare (xargs :verify-guards nil))
  (if (consp x) (append (spec-reverse (cdr x)) (list (car x))) nil))

(defun fast-reverse (x acc)
  (declare (xargs :guard (true-listp acc)))
  (if (consp x) (fast-reverse (cdr x) (cons (car x) acc)) acc))

(defun reverse-agrees-p (x)
  (declare (xargs :guard t))
  (equal (fast-reverse x nil) (ec-call (spec-reverse x))))

(assert-event (reverse-agrees-p '(1 2 3)))

; ---------------------------------------------------------------------------
; defun-nx: a specification with a free choice of representation that is
; never executed.  Calls of it cannot be evaluated, and the executable
; counterpart rune is disabled (:DOC defun-nx).

(defun-nx some-permutation-p (x y)
  (and (true-listp x) (true-listp y)
       (equal (len x) (len y))
       (subsetp-equal x y) (subsetp-equal y x)))

(defthm fast-reverse-is-spec
  (implies (true-listp acc)
           (equal (fast-reverse x acc) (append (spec-reverse x) acc))))

; ---------------------------------------------------------------------------
; mbt: the guard says I is a natural below the length; the logic must also
; know it for the measure, so it is asserted with mbt, which raw Lisp
; compiles to T once guards are verified (:DOC mbt).

(defun count-down-to (i n)
  (declare (xargs :guard (and (natp i) (natp n) (<= i n))
                  :measure (nfix (- n i))))
  (if (mbt (and (natp i) (natp n) (<= i n)))
      (if (= i n) 0 (+ 1 (count-down-to (+ 1 i) n)))
    0))

(defthm count-down-to-is-difference
  (implies (and (natp i) (natp n) (<= i n))
           (equal (count-down-to i n) (- n i))))
