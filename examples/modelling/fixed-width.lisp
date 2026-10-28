; examples/modelling/fixed-width.lisp
;
; Fixed-width arithmetic over ordinary integers: unsigned-byte-p as the type,
; logand/logior/ash/loghead/logtail as the operations, THE and type
; declarations so SBCL compiles fixnum arithmetic, and the bitops library
; (centaur/bitops/ihsext-basics, certified on the laptop) for the lemmas.
; The guard of each function is where the width is proved.
;
; Cited by humans/03-modelling-data.md, "Fixed-width arithmetic".

(in-package "ACL2")
(include-book "centaur/bitops/ihsext-basics" :dir :system)

; Keep UNSIGNED-BYTE-P closed.  Open, it turns every width goal into
; (< (LOGIOR ...) 4294967296), about which the library has no rule; closed,
; the library's UNSIGNED-BYTE-P-OF-LOGIOR / -OF-LOGHEAD / -OF-LOGTAIL fire.
; (With it enabled the guard proof of ROTL32 below fails at exactly that
; checkpoint.)
(local (in-theory (disable unsigned-byte-p)))

; Two bytes into a 16-bit word, written as :DOC the shows it.  The THE
; forms are promises to the compiler; each generates a guard obligation.
(defun merge-bytes (b1 b2)
  (declare (type (unsigned-byte 8) b1 b2))
  (the (unsigned-byte 16)
       (logior (the (unsigned-byte 16) (ash b1 8)) b2)))

(defthm merge-bytes-type
  (implies (and (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2))
           (unsigned-byte-p 16 (merge-bytes b1 b2))))

; The low byte and the high byte back out.
(defthm loghead-8-of-merge-bytes
  (implies (and (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2))
           (equal (loghead 8 (merge-bytes b1 b2)) b2))
  :hints (("Goal" :in-theory (enable merge-bytes))))

(defthm logtail-8-of-merge-bytes
  (implies (and (unsigned-byte-p 8 b1) (unsigned-byte-p 8 b2))
           (equal (logtail 8 (merge-bytes b1 b2)) b1))
  :hints (("Goal" :in-theory (enable merge-bytes))))

; A 32-bit rotate.  The type declarations let SBCL use fixnum arithmetic on
; a 64-bit host; the guard proof is that every intermediate fits.
(defun rotl32 (x n)
  (declare (type (unsigned-byte 32) x)
           (type (integer 0 31) n))
  (the (unsigned-byte 32)
       (logior (the (unsigned-byte 32) (loghead 32 (ash x n)))
               (the (unsigned-byte 32) (ash x (- n 32))))))

; The guard is not a hypothesis of the logic: ROTL32 is defined on every N,
; and for N = 40 the second shift is a LEFT shift by 8.  So the type theorem
; carries the range of N, or it is false.
(defthm rotl32-type
  (implies (and (unsigned-byte-p 32 x) (natp n) (< n 32))
           (unsigned-byte-p 32 (rotl32 x n))))

(assert-event
 (with-guard-checking :none
   (not (unsigned-byte-p 32 (rotl32 #xFFFFFFFF 40)))))

(defthm rotl32-by-0
  (implies (unsigned-byte-p 32 x)
           (equal (rotl32 x 0) x)))

; Width is a theorem about the operation, not about the inputs only: a
; masked value always fits, whatever the integer.
(defthm logand-255-fits
  (implies (integerp x) (unsigned-byte-p 8 (logand x 255))))

; A fold of bytes into a word with fixnum-bounded intermediates.
(defun pack-le (bytes acc shift)
  (declare (xargs :guard (and (true-listp bytes) (natp acc) (natp shift))))
  (if (atom bytes)
      acc
    (pack-le (cdr bytes)
             (logior acc (ash (loghead 8 (ifix (car bytes))) shift))
             (+ 8 shift))))

(defthm natp-of-pack-le
  (implies (natp acc) (natp (pack-le bytes acc shift)))
  :rule-classes :type-prescription)

(assert-event (equal (pack-le '(#x78 #x56 #x34 #x12) 0 0) #x12345678))
(assert-event (equal (rotl32 #x80000001 1) 3))
(assert-event (equal (merge-bytes #xAB #xCD) #xABCD))
