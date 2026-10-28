; examples/rewriting/syntaxp.lisp
;
; What it shows: a rule whose right-hand side contains an instance of its
; left-hand side, (lxd x) -> (lxd (nrm x)), loops on its own output; a syntaxp
; hypothesis that refuses to fire when the argument is already a (nrm ...)
; term stops it after one step (:doc syntaxp, its LXD/NORM example).
;
; Cited by humans/02-rewriting-theories-books.md, "syntaxp and bind-free".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(encapsulate
  (((nrm *) => *) ((lxd *) => *))
  (local (defun nrm (x) x))
  (local (defun lxd (x) (declare (ignore x)) 0))
  (defthm lxd-of-nrm
    (equal (lxd (nrm x)) (lxd x))
    :rule-classes nil))

(defthm lxd-normalize-unguarded
  (equal (lxd x) (lxd (nrm x)))
  :hints (("Goal" :use ((:instance lxd-of-nrm)))))

; (lxd a) -> (lxd (nrm a)) -> (lxd (nrm (nrm a))) -> ... to the depth limit.
(local
 (must-fail
  (thm (equal (lxd a) (lxd (nrm a))))))

(in-theory (disable lxd-normalize-unguarded))

; The syntaxp test sees the TERM the variable is bound to, quoted.
(defthm lxd-normalize
  (implies (syntaxp (not (and (consp x) (eq (car x) 'nrm))))
           (equal (lxd x) (lxd (nrm x))))
  :hints (("Goal" :use ((:instance lxd-of-nrm)))))

(defthm lxd-a-normalized
  (equal (lxd a) (lxd (nrm a)))
  :rule-classes nil)
