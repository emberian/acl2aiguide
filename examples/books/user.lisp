; examples/books/user.lisp
;
; What it shows: what an includer of examples/books/lib.lisp gets.  The local
; lemma and the locally included TAKE rules are not in its world at all; the
; exported theorem is; the definition the library withdrew is disabled here
; and can be opened, in one hint, through the named theory.
;
; Cited by humans/02-rewriting-theories-books.md, "local and the export
; boundary".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "lib")

; The local lemma does not exist here: no event of that name.
(assert-event
 (not (getpropc 'sum-list-of-append-local 'theorem nil (w state))))

; Neither does LEN-OF-TAKE from the library's local include.
(assert-event
 (not (getpropc 'len-of-take 'theorem nil (w state))))

; The exported theorem does.
(assert-event
 (getpropc 'sum-list-of-append-of-cons 'theorem nil (w state)))

; SUM-LIST arrives closed, as the export event left it.
(assert-event (equal (disabledp 'sum-list)
                     '((:definition sum-list) (:induction sum-list))))

; Without the local lemma, and with SUM-LIST closed, the general append fact
; is not provable here.
(local
 (must-fail
  (thm (equal (sum-list (append x y))
              (+ (sum-list x) (sum-list y))))))

; The includer opens the library's vocabulary in the one hint that needs it.
(defthm sum-list-of-append
  (equal (sum-list (append x y))
         (+ (sum-list x) (sum-list y)))
  :hints (("Goal" :in-theory (enable lib-internals))))
