; examples/systems/state-io.lisp
;
; I/O through the ACL2 state: a guard-verified function that writes bytes
; to an open :byte channel, a writer and a reader around it.  Logically each
; is a function of the STATE object, whose channels and files are fields of
; a list (:doc state).  The book performs no I/O when certified; at the REPL
; (save-bytes "x.bin" '(1 2 255) state) then (load-bytes "x.bin" 100 state)
; returned ((1 2 255) <state>) (laptop, ACL2 8.7).
;
; Cited by humans/04-modelling-systems.md, "I/O and the operating system".

(in-package "ACL2")

(defun octet-listp (x)
  (declare (xargs :guard t))
  (if (atom x) (null x) (and (unsigned-byte-p 8 (car x)) (octet-listp (cdr x)))))

(defun write-bytes (bytes channel state)
  (declare (xargs :stobjs state
                  :guard (and (octet-listp bytes)
                              (symbolp channel)
                              (open-output-channel-p channel :byte state))))
  (if (atom bytes)
      state
    (let ((state (write-byte$ (car bytes) channel state)))
      (write-bytes (cdr bytes) channel state))))

; The open/write/close sequence's guard conjecture is a statement about the
; channel fields of the state after OPEN-OUTPUT-CHANNEL; proving it needs the
; lemma library std/io/base.lisp, which is not certified on this laptop, so
; the two wrappers below are left with :verify-guards nil and run through
; their executable counterparts (:doc guard-evaluation-table, row b).
(defun save-bytes (filename bytes state)
  (declare (xargs :stobjs state
                  :guard (and (stringp filename) (octet-listp bytes))
                  :verify-guards nil))
  (mv-let (channel state)
    (open-output-channel filename :byte state)
    (if (null channel)
        (mv :cannot-open state)
      (let* ((state (write-bytes bytes channel state))
             (state (close-output-channel channel state)))
        (mv nil state)))))

; A read loop needs a measure.  Over the channel itself that is
; FILE-MEASURE, from std/io/file-measure.lisp (not certified here); bounding
; the loop by a count is the measure that needs no library.
(defun read-bytes-loop (channel n acc state)
  (declare (xargs :stobjs state
                  :guard (and (symbolp channel) (natp n)
                              (open-input-channel-p channel :byte state)
                              (true-listp acc))
                  :verify-guards nil))
  (if (zp n)
      (mv (reverse acc) state)
    (mv-let (b state)
      (read-byte$ channel state)
      (if (null b)
          (mv (reverse acc) state)
        (read-bytes-loop channel (- n 1) (cons b acc) state)))))

(defun load-bytes (filename n state)
  (declare (xargs :stobjs state :guard (and (stringp filename) (natp n))
                  :verify-guards nil))
  (mv-let (channel state)
    (open-input-channel filename :byte state)
    (if (null channel)
        (mv :cannot-open state)
      (mv-let (bytes state)
        (read-bytes-loop channel n nil state)
        (let ((state (close-input-channel channel state)))
          (mv bytes state))))))

; What the logic can say about the state these return is a matter of lemmas
; over the state's channel fields (STATE-P1-OF-WRITE-BYTE$ and
; OPEN-OUTPUT-CHANNEL-P1-OF-WRITE-BYTE$, std/io/base.lisp:979-992, and the
; local lemmas they rest on).  That library is not certified on this laptop;
; restating its first lemma with its hint here does not close (the checkpoint
; is (OPEN-CHANNEL-LISTP (ADD-PAIR CHANNEL ...))), so this book proves no
; theorem about the state and says so.  Nothing in it, in any case, is about
; the file system: the logic's files are fields of the state list.
