; examples/stobjs/nested-stobj.lisp
;
; stobj-let over a nested stobj: a parent with a scalar child stobj and an
; array of child stobjs.  Reads and writes of a child go through stobj-let
; (direct calls of a stobj-typed field's accessor are refused: :DOC
; nested-stobjs, "An aliasing problem"); two children of the same array are
; bound at once through a congruent stobj, with distinct indices.
;
; Cited by humans/03-modelling-data.md, "Nested stobjs and stobj-let".

(in-package "ACL2")

(defstobj acct (bal :type (integer 0 *) :initially 0))
(defstobj acct2 (bal2 :type (integer 0 *) :initially 0) :congruent-to acct)
(defstobj acct3 (bal3 :type (integer 0 *) :initially 0) :congruent-to acct)

(defstobj bank
  (fees :type acct)                       ; a child stobj
  (accts :type (array acct (4)))          ; an array of child stobjs
  (nops :type (integer 0 *) :initially 0))

; The generated recognizers, accessors and updaters are enabled
; definitions over NTH and UPDATE-NTH.  Guard proofs through stobj-let then
; fail on goals like (ACL2-NUMBERP (CAR (NTH I (NTH *ACCTSI* BANK)))): a rule
; about (ACCTP ...) or (BAL ...) never fires, because the goal has already
; opened them.  So: prove the facts in the accessors' vocabulary while they
; are open, then close them, as an opaque record is closed.

(defthm acctp-nth-of-acctsp
  (implies (and (acctsp l) (natp i) (< i (len l)))
           (acctp (nth i l))))

(defthm acctsp-of-update-nth
  (implies (and (acctsp l) (natp i) (< i (len l)) (acctp a))
           (acctsp (update-nth i a l))))

; Not a :type-prescription: its hypothesis (ACCTP A) would be relieved by
; type reasoning alone, and (ACCTP (ACCTSI I BANK)) needs rewriting.  And a
; rewrite rule concluding (INTEGERP (BAL A)) does not help a goal
; (INTEGERP (+ AMT (BAL ...))): that goal is settled by type reasoning,
; which does not call the rewriter.  So the guard proofs below :use it.
(defthm bal-type-when-acctp
  (implies (acctp a) (and (integerp (bal a)) (<= 0 (bal a))))
  ; :rule-classes nil: a fact for :use.  As a rewrite rule it would erase
  ; its own (INTEGERP (BAL ...)) from the :use'd hypothesis before type
  ; reasoning saw it (the checkpoint then still asks for that INTEGERP).
  :rule-classes nil)

(defthm acctp-of-update-bal
  (implies (and (acctp a) (natp v)) (acctp (update-bal v a))))

(defthm bal-of-update-bal
  (equal (bal (update-bal v a)) v))

(defthm acctp-of-acctsi
  (implies (and (bankp bank) (natp i) (< i (accts-length bank)))
           (acctp (acctsi i bank))))

(defthm acctp-of-fees
  (implies (bankp bank) (acctp (fees bank))))

(defthm bankp-of-update-acctsi
  (implies (and (bankp bank) (natp i) (< i (accts-length bank)) (acctp a))
           (bankp (update-acctsi i a bank))))

(defthm bankp-of-update-fees
  (implies (and (bankp bank) (acctp a)) (bankp (update-fees a bank))))

(defthm bankp-of-update-nops
  (implies (and (bankp bank) (natp v)) (bankp (update-nops v bank))))

(defthm nops-type-when-bankp
  (implies (bankp bank) (and (integerp (nops bank)) (<= 0 (nops bank))))
  :rule-classes nil)

(defthm accts-length-of-updates
  (and (implies (and (natp i) (< i (accts-length bank)))
                (equal (accts-length (update-acctsi i a bank))
                       (accts-length bank)))
       (equal (accts-length (update-fees a bank)) (accts-length bank))
       (equal (accts-length (update-nops v bank)) (accts-length bank))))

(defthm acctsi-of-updates
  (and (implies (and (natp i) (natp j))
                (equal (acctsi j (update-acctsi i a bank))
                       (if (equal i j) a (acctsi j bank))))
       (equal (acctsi j (update-fees a bank)) (acctsi j bank))
       (equal (acctsi j (update-nops v bank)) (acctsi j bank))))

(defthm nops-of-updates
  (and (equal (nops (update-acctsi i a bank)) (nops bank))
       (equal (nops (update-fees a bank)) (nops bank))))

(defthm fees-of-updates
  (and (equal (fees (update-acctsi i a bank)) (fees bank))
       (equal (fees (update-fees a bank)) a)
       (equal (fees (update-nops v bank)) (fees bank))))

(in-theory (disable acctp acctsp bankp bal update-bal acctsi update-acctsi
                    accts-length fees update-fees nops update-nops))

; Deposit into account I: bind the child, produce the new child, consume.
(defun deposit (i amt bank)
  (declare (xargs :stobjs bank
                  :guard (and (natp i) (< i (accts-length bank)) (natp amt))
                  :guard-hints
                  (("Goal" :use ((:instance bal-type-when-acctp
                                            (a (acctsi i bank)))
                                 nops-type-when-bankp)))))
  (stobj-let
   ((acct (acctsi i bank)))                      ; bindings
   (acct)                                        ; producer variables
   (update-bal (+ amt (bal acct)) acct)          ; producer
   (update-nops (+ 1 (nops bank)) bank)))        ; consumer

; Read a balance: the producer variable is an ordinary value.
(defun balance (i bank)
  (declare (xargs :stobjs bank
                  :guard (and (natp i) (< i (accts-length bank)))))
  (stobj-let
   ((acct (acctsi i bank)))
   (b)
   (bal acct)
   b))

; Move AMT from account I to account J, charging a fee into the FEES child.
; Three children of type ACCT are bound at once, so three congruent stobj
; NAMES are needed: a stobj-let variable must be a stobj name (binding FEES,
; a field name, is refused: "The stobj-let bound variable FEES is not the
; name of a known single-threaded object").  Two elements of one array are
; bound together, so the guard must show I and J differ (the aliasing check).
(defun xfer (i j amt bank)
  (declare (xargs :stobjs bank
                  :guard (and (natp i) (< i (accts-length bank))
                              (natp j) (< j (accts-length bank))
                              (not (equal i j))
                              (natp amt))
                  :guard-hints
                  (("Goal" :use ((:instance bal-type-when-acctp
                                            (a (acctsi i bank)))
                                 (:instance bal-type-when-acctp
                                            (a (acctsi j bank)))
                                 (:instance bal-type-when-acctp
                                            (a (fees bank)))
                                 nops-type-when-bankp)))))
  (stobj-let
   ((acct (acctsi i bank))
    (acct2 (acctsi j bank))
    (acct3 (fees bank) update-fees))
   (acct acct2 acct3)
   (let* ((have (bal acct))
          (moved (if (<= (+ 1 amt) have) amt 0))
          (fee (if (< 0 moved) 1 0))
          (acct (update-bal (- have (+ moved fee)) acct))
          (acct2 (update-bal (+ moved (bal acct2)) acct2))
          (acct3 (update-bal (+ fee (bal acct3)) acct3)))
     (mv acct acct2 acct3))
   (update-nops (+ 1 (nops bank)) bank)))

; Logically a stobj-let is a let over the parent's accessor and updater, so
; read-over-write facts are provable about the parent as a list.
(defthm balance-of-deposit
  (implies (and (natp i) (natp amt) (natp j))
           (equal (balance j (deposit i amt bank))
                  (if (equal i j)
                      (+ amt (bal (acctsi j bank)))
                    (balance j bank)))))

; Run it on the live stobj.
(defun demo (bank)
  (declare (xargs :stobjs bank
                  :guard (<= 4 (accts-length bank))))
  (let* ((bank (deposit 0 10 bank))
         (bank (xfer 0 3 4 bank)))
    (mv (list (balance 0 bank) (balance 3 bank)) bank)))

(make-event
 (mv-let (vals bank)
   (demo bank)
   (mv nil `(defconst *demo-result* ',vals) state bank)))

(assert-event (equal *demo-result* '(5 4)))
