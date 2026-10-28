; examples/stobjs/attach-stobj.lisp
;
; One logical memory, two executables.  The attachable abstract stobj MEM
; (attach-mem.lisp) is proved against an array foundation; a second abstract
; stobj MEM-HT (attach-mem-ht.lisp), with the same :logic functions and a
; hash-table foundation, is attached BEFORE MEM is introduced, so every MEM
; primitive executes as a hash-table operation while every theorem about MEM
; is the array-backed book's, not reproved.  This is the shape of
; books/demos/attach-stobj/mem-as-ht.lisp.
;
; The three events are in three books on purpose.  A one-book version
; (implementation, attach-stobj, then the attachable defabsstobj, all in one
; book) passes its first pass and then fails when certify-book re-includes
; it: "HARD ACL2 ERROR in ASSERT$ ... An error has occurred while
; DEFABSSTOBJ was defining the supporting functions.  This is supposed to be
; impossible!" (ACL2 8.7, SBCL 2.6.8, laptop, examples/certify.sh).
;
; Cited by humans/03-modelling-data.md, "Attachable stobjs".

(in-package "ACL2")

; The implementation must exist before the attach-stobj event names it.
(include-book "attach-mem-ht")

; The attachment comes BEFORE the attachable stobj is introduced.
(attach-stobj mem mem-ht)

; Introduce MEM: its execution is now MEM-HT's.
(include-book "attach-mem")

; The attachment is in force: the world records it, and MEM's creator is the
; implementation's (the check fn's catalog makes, books/catalog.lisp:51).
(assert-event
 (and (eq (cdr (assoc-eq 'mem (table-alist 'attach-stobj-table (w state))))
          'mem-ht)
      (let* ((gen (access absstobj-info (getpropc 'mem 'absstobj-info nil (w state))
                          :absstobj-tuples))
             (impl (access absstobj-info (getpropc 'mem-ht 'absstobj-info nil (w state))
                           :absstobj-tuples)))
        (equal (caddr (assoc-eq 'create-mem gen))
               (caddr (assoc-eq 'create-mem-ht impl))))))

; The theorem proved in attach-mem.lisp about the array-backed MEM is in
; the world, unchanged.
(assert-event (equal (getpropc 'lookup-update 'untranslated-theorem nil (w state))
                     '(implies (and (mem-indexp i) (mem-indexp j))
                               (equal (lookup i (update j v mem))
                                      (if (equal i j) v (lookup i mem))))))

; And MEM executes (as a hash table) on its live stobj.
(defun poke-and-peek (mem)
  (declare (xargs :stobjs mem))
  (let ((mem (update 5 'five mem)))
    (mv (lookup 5 mem) mem)))

(make-event
 (mv-let (v mem) (poke-and-peek mem)
   (mv nil `(defconst *peek* ',v) state mem)))

(assert-event (eq *peek* 'five))
