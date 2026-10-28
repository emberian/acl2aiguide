; examples/rewriting/induction-rule.lisp
;
; What it shows: the :induction rune of a function is what links its calls to
; its induction scheme; disable it and the function suggests no induction.
; An :induction rule (no proof obligation; the theorem is T) links a pattern
; to the scheme of another term (:doc induction).
;
; Cited by humans/02-rewriting-theories-books.md, ":induction".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defun drop (n x)
  (if (zp n) x (drop (1- n) (cdr x))))

(defun tk (n x)
  (if (zp n) nil (cons (car x) (tk (1- n) (cdr x)))))

(in-theory (disable (:induction drop)))

; DROP-OF-DROP proves by induction on (DROP J X), which is now unavailable.
(local
 (must-fail
  (thm (implies (and (natp i) (natp j))
                (equal (drop i (drop j x))
                       (drop (+ i j) x))))))

; Calls (drop n x) now suggest the scheme of (tk n x), which recurs the same
; way.
(defthm drop-suggests-tk-induction
  t
  :rule-classes ((:induction :pattern (drop n x)
                             :scheme (tk n x))))

(defthm drop-of-drop
  (implies (and (natp i) (natp j))
           (equal (drop i (drop j x))
                  (drop (+ i j) x))))
