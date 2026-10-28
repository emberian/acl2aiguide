; examples/rewriting/theories.lisp
;
; What it shows: runic designators and theory events.  DEFUND disables a
; definition (its :definition and :induction runes); the executable
; counterpart is a separate rune that computes ground calls; DEFTHEORY names a
; set of runes that a later hint can enable in one word; (theory 'ground-zero)
; is the boot-strap theory, the right theory for a lemma about primitives; and
; the tau system is switched off by disabling one executable-counterpart rune.
;
; Cited by humans/02-rewriting-theories-books.md, "Theories".

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

(defund fact (n)
  (if (zp n) 1 (* n (fact (1- n)))))

; DEFUND leaves the executable counterpart and type prescription enabled.
(assert-event (equal (disabledp 'fact)
                     '((:definition fact) (:induction fact))))

; The ground term is computed by the executable counterpart.  (Stored with
; :rule-classes nil: as a rewrite rule it would itself prove the next goal.)
(defthm fact-5
  (equal (fact 5) 120)
  :rule-classes nil)

; With (:e fact) disabled the term is not computed, and the definition alone
; is not opened five times by the rewriter's heuristics.
(local
 (must-fail
  (thm (equal (fact 5) 120)
       :hints (("Goal" :in-theory (e/d (fact) ((:e fact))))))))

; A named theory: the definition and induction runes of FACT.
(deftheory fact-vocabulary
  '((:d fact) (:i fact)))

(defthm fact-positive
  (implies (natp n) (< 0 (fact n)))
  :hints (("Goal" :in-theory (enable fact-vocabulary))))

; A lemma about primitives only: no rule from this book or any include can
; help it, so prove it in the boot-strap theory (fn docs/proof-style.md
; section 6).
(defthm len-of-append-in-ground-zero
  (equal (len (append x y))
         (+ (len x) (len y)))
  :hints (("Goal" :in-theory (theory 'ground-zero))))

; The tau system is the executable-counterpart rune of the function TAU-SYSTEM
; (:doc tau-system).  Local, so includers keep their own setting.
(local (in-theory (disable (tau-system))))
