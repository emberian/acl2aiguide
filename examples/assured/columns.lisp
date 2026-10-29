; examples/assured/columns.lisp
;
; What it shows: TigerStyle's "put a limit on everything" and "no
; allocation after init" written as a declaration that generates its own
; storage, guards and theorems, in the shape of fn2's DEFCOLUMNS
; (fn2/books/columns.lisp @127f7b877), cut to what fits in one page.
;
;   (defcols NAME ((FIELD KIND) ...) :rows-bound B)
;
; KIND is :u8, :u16, :u32, :u60 or (:enum ENAME (:kw0 :kw1 ...)).  The form
; expands, at macro-expansion time only, into:
;   - a DEFSTOBJ with one resizable typed array per column and a ROWS
;     scalar whose type is (integer 0 B-1): the bound is in the type;
;   - NAME-WFP: every column has exactly ROWS entries;
;   - NAME-INIT: the only function that resizes anything (static
;     allocation: the arrays are sized once, at init);
;   - per column a reader whose guard requires a valid row (no reader
;     returns a made-up value for a bad index) and a setter whose guard
;     requires the value to fit the column (no setter silently drops a
;     value that does not fit; fn2's review found that shape, finding A3 of
;     REVIEW-SINS-20261028.md, and fn2's generator now puts the width in
;     the guard, fn2/books/columns.lisp:488-492 @127f7b877);
;   - per enum a constant per keyword and *ENAME-COUNT*, which the enum
;     setter's guard uses (a consumer never types the count by hand;
;     finding A13);
;   - a row in the world table ASSURED-COLUMNS, so later forms and tools
;     read the declaration, never a copy of it.
; The theorems every column receives: the setter preserves NAME-WFP and
; ROWS (so nothing after init changes a length), and the reader is a
; natural below the column's limit.
;
; Cited by assured/humans/01-rules-as-declarations.md and
; assured/ai/01-rules-as-declarations.md.

(in-package "ACL2")

; The two length facts every generated shape theorem uses (fn2 states the
; same pair at fn2/books/columns.lisp:6-15 @127f7b877).
(defthm ac-len-resize-list
  (equal (len (resize-list xs n default)) (nfix n)))
(defthm ac-len-update-nth
  (implies (and (natp i) (< i (len xs)))
           (equal (len (update-nth i v xs)) (len xs))))

; One list template, proved once over a constrained value predicate; each
; column's array predicate gets its facts by functional instance, never by
; a fresh induction (fn2's kit K1, fn2/books/columns.lisp:17-32
; @127f7b877).
(encapsulate (((ac-valuep *) => *))
  (local (defun ac-valuep (x) (natp x))))
(defun ac-valuesp (xs)
  (if (atom xs) (eq xs nil)
    (and (ac-valuep (car xs)) (ac-valuesp (cdr xs)))))
(defthm ac-valuesp-nth
  (implies (and (ac-valuesp xs) (natp i) (< i (len xs)))
           (ac-valuep (nth i xs))))
(defthm ac-valuesp-update
  (implies (and (ac-valuesp xs) (natp i) (< i (len xs)) (ac-valuep v))
           (ac-valuesp (update-nth i v xs))))
(defthm ac-valuesp-resize
  (implies (and (ac-valuesp xs) (ac-valuep v))
           (ac-valuesp (resize-list xs n v))))

; Expansion-time helpers: logic mode, guards unverified, never executed on
; a served path (fn2 keeps the same rule: no :program in any book).
(defun ac-sym-chars (parts)
  (declare (xargs :verify-guards nil))
  (if (atom parts) nil
    (append (coerce (if (symbolp (car parts)) (symbol-name (car parts))
                      (if (stringp (car parts)) (car parts) ""))
                    'list)
            (ac-sym-chars (cdr parts)))))

(defun ac-symlist (parts)
  (declare (xargs :verify-guards nil))
  (intern-in-package-of-symbol (coerce (ac-sym-chars parts) 'string) 'acl2))

(defmacro ac-sym (&rest parts) `(ac-symlist (list ,@parts)))

(defun ac-width (kind)
  (declare (xargs :verify-guards nil))
  (cond ((eq kind :u8) 8) ((eq kind :u16) 16) ((eq kind :u32) 32)
        ((eq kind :u60) 60)
        ((and (consp kind) (eq (car kind) :enum)) 8)
        (t nil)))

(defun ac-kindp (kind)
  (declare (xargs :verify-guards nil))
  (or (member-eq kind '(:u8 :u16 :u32 :u60))
      (and (true-listp kind) (equal (len kind) 3) (eq (car kind) :enum)
           (symbolp (cadr kind))
           (consp (caddr kind)) (symbol-listp (caddr kind))
           (no-duplicatesp-eq (caddr kind))
           (<= (len (caddr kind)) 256))))

(defun ac-cols-okp (cols)
  (declare (xargs :verify-guards nil))
  (or (null cols)
      (and (consp cols) (true-listp (car cols)) (equal (len (car cols)) 2)
           (symbolp (caar cols)) (ac-kindp (cadar cols))
           (ac-cols-okp (cdr cols)))))

(defun ac-enum-consts (ename kws n)
  (declare (xargs :verify-guards nil))
  (if (atom kws) nil
    (cons `(defconst ,(ac-sym "*" ename "-" (car kws) "*") ,n)
          (ac-enum-consts ename (cdr kws) (+ 1 n)))))

(defun ac-enum-events (cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (let ((kind (cadar cols)))
      (append (if (consp kind)
                  (cons `(defconst ,(ac-sym "*" (cadr kind) "-COUNT*") ,(len (caddr kind)))
                        (ac-enum-consts (cadr kind) (caddr kind) 0))
                nil)
              (ac-enum-events (cdr cols))))))

(defun ac-fields (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons `(,(ac-sym name "-" (caar cols) "$A")
            :type (array (unsigned-byte ,(ac-width (cadar cols))) (0))
            :initially 0 :resizable t)
          (ac-fields name (cdr cols)))))

(defun ac-wfp-conjuncts (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons `(equal (,(ac-sym name "-" (caar cols) "$A-LENGTH") ,name)
                  (,(ac-sym name "-ROWS") ,name))
          (ac-wfp-conjuncts name (cdr cols)))))

(defun ac-resizes (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (cons `(,name (,(ac-sym "RESIZE-" name "-" (caar cols) "$A") n ,name))
          (ac-resizes name (cdr cols)))))

(defun ac-value-guard (kind)
  (declare (xargs :verify-guards nil))
  (if (consp kind)
      `(and (natp v) (< v ,(ac-sym "*" (cadr kind) "-COUNT*")))
    `(unsigned-byte-p ,(ac-width kind) v)))

; Per array column: the template's three facts by functional instance.
; The NTH facts match every (nth i xs) in every proof, whatever the
; field; the defcols expansion uses them for the typed reader theorems
; and then disables them (fn2's W1 repair, commit 1fa1fe24b: with this
; family as its main cause, the layer-A closure's summed certify time fell
; from 1,876 s to 284 s).
(defun ac-array-facts (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (let* ((p (ac-sym name "-" (caar cols) "$AP"))
           (w (ac-width (cadar cols)))
           (subst `((ac-valuep (lambda (x) (unsigned-byte-p ,w x)))
                    (ac-valuesp ,p))))
      (append
       `((defthm ,(ac-sym p "-NTH-NATP")
           (implies (and (,p xs) (natp i) (< i (len xs))) (natp (nth i xs)))
           :rule-classes :type-prescription
           :hints (("Goal" :use ((:functional-instance ac-valuesp-nth ,@subst)))))
         (defthm ,(ac-sym p "-NTH-BOUND")
           (implies (and (,p xs) (natp i) (< i (len xs))) (< (nth i xs) ,(expt 2 w)))
           :rule-classes :linear
           :hints (("Goal" :use ((:functional-instance ac-valuesp-nth ,@subst)))))
         (defthm ,(ac-sym p "-OF-UPDATE-NTH")
           (implies (and (,p xs) (natp i) (< i (len xs)) (unsigned-byte-p ,w v))
                    (,p (update-nth i v xs)))
           :hints (("Goal" :use ((:functional-instance ac-valuesp-update ,@subst)))))
         (defthm ,(ac-sym p "-OF-RESIZE-LIST")
           (implies (and (,p xs) (unsigned-byte-p ,w v)) (,p (resize-list xs n v)))
           :hints (("Goal" :use ((:functional-instance ac-valuesp-resize ,@subst))))))
       (ac-array-facts name (cdr cols))))))

(defun ac-nth-runes (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (let ((p (ac-sym name "-" (caar cols) "$AP")))
      (list* `(:type-prescription ,(ac-sym p "-NTH-NATP"))
             `(:linear ,(ac-sym p "-NTH-BOUND"))
             (ac-nth-runes name (cdr cols))))))

(defun ac-column-events (name cols)
  (declare (xargs :verify-guards nil))
  (if (atom cols) nil
    (let* ((f (caar cols)) (kind (cadar cols)) (w (ac-width kind))
           (wfp (ac-sym name "-WFP")) (rows (ac-sym name "-ROWS"))
           (p (ac-sym name "P"))
           (read (ac-sym name "-" f)) (write (ac-sym name "-SET-" f))
           (raw (ac-sym name "-" f "$AI")) (raw-write (ac-sym "UPDATE-" name "-" f "$AI"))
           (row-guard `(and (,wfp ,name) (natp i) (< i (,rows ,name)))))
      (append
       `((defun ,read (i ,name)
           (declare (xargs :stobjs ,name :guard ,row-guard
                           :guard-hints (("Goal" :in-theory (enable ,wfp ,p)))))
           (,raw i ,name))
         (defun ,write (i v ,name)
           (declare (xargs :stobjs ,name
                           :guard (and ,row-guard ,(ac-value-guard kind))
                           :guard-hints (("Goal" :in-theory (enable ,wfp ,p)))))
           (,raw-write i v ,name))
         (defthm ,(ac-sym write "-PRESERVES-WFP")
           (implies ,row-guard (,wfp (,write i v ,name)))
           :hints (("Goal" :in-theory (enable ,wfp))))
         (defthm ,(ac-sym write "-PRESERVES-TYPE")
           (implies (and (,p ,name) ,row-guard ,(ac-value-guard kind))
                    (,p (,write i v ,name)))
           :hints (("Goal" :in-theory (enable ,wfp ,p))))
         (defthm ,(ac-sym write "-ROWS")
           (equal (,rows (,write i v ,name)) (,rows ,name)))
         (defthm ,(ac-sym read "-NATP")
           (implies (and (,p ,name) ,row-guard) (natp (,read i ,name)))
           :rule-classes :type-prescription
           :hints (("Goal" :in-theory (enable ,wfp ,p))))
         (defthm ,(ac-sym read "-BOUND")
           (implies (and (,p ,name) ,row-guard) (< (,read i ,name) ,(expt 2 w)))
           :rule-classes :linear
           :hints (("Goal" :in-theory (enable ,wfp ,p))))
         (in-theory (disable ,read ,write)))
       (ac-column-events name (cdr cols))))))

(defmacro defcols (name cols &key (rows-bound '4294967296))
  (if (not (and (symbolp name) (consp cols) (ac-cols-okp cols)
                (no-duplicatesp-eq (strip-cars cols))
                (posp rows-bound) (<= rows-bound (expt 2 60))))
      (er hard 'defcols
          "Invalid declaration ~x0: distinct columns of kind :u8, :u16, :u32, ~
           :u60 or (:enum NAME (keywords)), and a rows bound in 1..2^60."
          name)
    (let ((rows (ac-sym name "-ROWS")) (wfp (ac-sym name "-WFP"))
          (init (ac-sym name "-INIT")) (p (ac-sym name "P")))
      `(encapsulate ()
         ,@(ac-enum-events cols)
         (defstobj ,name ,@(ac-fields name cols)
           (,rows :type (integer 0 ,(- rows-bound 1)) :initially 0))
         ,@(ac-array-facts name cols)
         (defun ,wfp (,name)
           (declare (xargs :stobjs ,name))
           (and ,@(ac-wfp-conjuncts name cols)))
         (defun ,init (n ,name)
           (declare (xargs :stobjs ,name
                           :guard (and (natp n) (< n ,rows-bound))))
           (let* (,@(ac-resizes name cols)
                  (,name (,(ac-sym "UPDATE-" rows) n ,name)))
             ,name))
         (defthm ,(ac-sym init "-WFP")
           (implies (and (natp n) (< n ,rows-bound)) (,wfp (,init n ,name))))
         (defthm ,(ac-sym init "-TYPE")
           (implies (and (,p ,name) (natp n) (< n ,rows-bound))
                    (,p (,init n ,name))))
         (defthm ,(ac-sym init "-ROWS")
           (implies (natp n) (equal (,rows (,init n ,name)) n)))
         (in-theory (disable ,wfp ,init ,p))
         ,@(ac-column-events name cols)
         ; ROWS is a stobj accessor (an NTH); closed, the generated -ROWS
         ; theorems are what callers see, and NTH never reappears.
         (defthm ,(ac-sym rows "-NATP")
           (implies (,p ,name) (natp (,rows ,name)))
           :rule-classes :type-prescription
           :hints (("Goal" :in-theory (enable ,p))))
         (in-theory (disable ,rows ,@(ac-nth-runes name cols)))
         (table assured-columns ',name
                '(:columns ,cols :rows-bound ,rows-bound :init ,init))))))

; ----------------------------------------------------------------------
; An instance: a table of buffer slots with an ownership phase.

(defcols slots
  ((phase (:enum slot-phase (:free :leased :borrowed :retired)))
   (gen :u60)
   (len :u32))
  :rows-bound 1024)

; The declaration is data in the world, readable by the next form.
(assert-event
 (equal (cdr (assoc-eq 'slots (table-alist 'assured-columns (w state))))
        '(:columns ((phase (:enum slot-phase (:free :leased :borrowed :retired)))
                    (gen :u60) (len :u32))
          :rows-bound 1024 :init slots-init)))

(assert-event (equal *slot-phase-count* 4))
(assert-event (equal *slot-phase-borrowed* 2))

; A setter call whose value cannot be shown to fit is a guard violation,
; caught at the call site when the caller is guard-verified: the caller
; below must establish the width itself, here by a test that refuses by
; name at the boundary.
(defun slots-record-len (i n slots)
  (declare (xargs :stobjs slots
                  :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots)))))
  (if (unsigned-byte-p 32 n)
      (let ((slots (slots-set-len i n slots))) (mv :ok slots))
    (mv :too-long slots)))

; Without the test, guard verification fails: the width is a proof
; obligation, not a run-time branch that drops the write.
(include-book "std/testing/must-fail" :dir :system)
(must-fail
 (defun slots-record-len-unchecked (i n slots)
   (declare (xargs :stobjs slots
                   :guard (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                               (natp n))))
   (slots-set-len i n slots)))

; Static allocation: after init, a run of setters keeps every length.
(defthm slots-two-writes-keep-shape
  (implies (and (slots-wfp slots) (natp i) (< i (slots-rows slots))
                (natp j) (< j (slots-rows slots)))
           (and (slots-wfp (slots-set-gen j g (slots-set-len i n slots)))
                (equal (slots-rows (slots-set-gen j g (slots-set-len i n slots)))
                       (slots-rows slots)))))

; Execution: init sizes the arrays once; writes and reads follow.
(defun slots-demo ()
  (declare (xargs :guard t))
  (with-local-stobj slots
    (mv-let (answer slots)
      (let* ((slots (slots-init 8 slots))
             (slots (slots-set-phase 3 *slot-phase-leased* slots)))
        (mv-let (code slots) (slots-record-len 3 4096 slots)
          (mv (list code (slots-phase 3 slots) (slots-len 3 slots) (slots-rows slots))
              slots)))
      answer)))

(assert-event (equal (slots-demo) '(:ok 1 4096 8)))
