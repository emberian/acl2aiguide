; examples/stobjs/array-stobj.lisp
;
; A concrete stobj with a fixed array field, a resizable array field, a
; scalar and a hash-table field; theorems about the array updater
; (read-over-write, length preserved) stated over the generated accessors;
; a guard-verified loop that fills the array in place.
;
; Cited by humans/03-modelling-data.md, "Arrays and single-threaded objects".

(in-package "ACL2")

(defconst *regs* 8)

(defstobj mach
  (regs :type (array (unsigned-byte 32) (*regs*)) :initially 0)
  (mem  :type (array (unsigned-byte 8) (16)) :initially 0 :resizable t)
  (pc   :type (unsigned-byte 32) :initially 0)
  (seen :type (hash-table eql))
  ; PC is already an ACL2 macro, so its default accessor name would clash
  ; ("The name PC is in use as a macro"); :renaming substitutes for the
  ; DEFAULT names, so the updater is renamed separately.
  :renaming ((pc get-pc) (update-pc set-pc))
  :inline t)

; What the event generated, by name and arity (:DOC defstobj, "The Default
; Function Names"): regsi, update-regsi, regs-length, memi, update-memi,
; mem-length, resize-mem, get-pc, set-pc (renamed), seen-get, seen-put, seen-boundp,
; seen-count, ... and the recognizer machp and creator create-mach.

; Logically the stobj is a list of fields and an array field is a list, so
; the updater is update-nth of update-nth.  These rules restate that in the
; vocabulary of the accessors.

(defthm regsi-of-update-regsi
  (implies (and (natp i) (natp j))
           (equal (regsi i (update-regsi j v mach))
                  (if (equal i j) v (regsi i mach)))))

(defthm regs-length-of-update-regsi
  (implies (and (natp j) (< j (regs-length mach)))
           (equal (regs-length (update-regsi j v mach))
                  (regs-length mach))))

(defthm get-pc-of-update-regsi
  (equal (get-pc (update-regsi j v mach)) (get-pc mach)))

; The recognizer is preserved by an in-bounds, in-type write.  This is the
; fact guard verification of a caller needs.  It does not come for free: the
; field recognizer REGSP is a recursion over the list, and the prover needs
; the list fact first (the checkpoint without it is
; (REGSP (UPDATE-NTH J V (CAR MACH)))).
(defthm regsp-of-update-nth
  (implies (and (regsp l) (natp j) (< j (len l)) (unsigned-byte-p 32 v))
           (regsp (update-nth j v l))))

(defthm machp-of-update-regsi
  (implies (and (machp mach)
                (natp j) (< j (regs-length mach))
                (unsigned-byte-p 32 v))
           (machp (update-regsi j v mach))))

; From here on, reason in the accessor vocabulary only.  The generated
; accessors and updaters are enabled definitions (:inline or not), so a rule
; stated about (REGSI K ...) never fires: the goal has already opened REGSI to
; (NTH K (CAR ...)).  Close them, as an opaque record is closed.
(in-theory (disable regsi update-regsi regs-length machp))

; Fill registers [i, n) with v, destructively.
(defun fill-regs (i v mach)
  (declare (xargs :stobjs mach
                  :guard (and (natp i) (<= i (regs-length mach))
                              (unsigned-byte-p 32 v))
                  :measure (nfix (- (regs-length mach) i))))
  (if (or (not (natp i)) (>= i (regs-length mach)))
      mach
    (let ((mach (update-regsi i v mach)))
      (fill-regs (+ 1 i) v mach))))

(defthm regs-length-of-fill-regs
  (equal (regs-length (fill-regs i v mach)) (regs-length mach)))

; Below the start, the fill changes nothing; at and above it, every cell is V.
; The second needs the first (the cell written at I must survive the
; recursive call from I + 1), which is why it is a separate lemma.
(defthm regsi-of-fill-regs-below
  (implies (and (natp i) (natp k) (< k i))
           (equal (regsi k (fill-regs i v mach)) (regsi k mach))))

(defthm regsi-of-fill-regs
  (implies (and (natp i) (natp k) (<= i k) (< k (regs-length mach)))
           (equal (regsi k (fill-regs i v mach)) v))
  :hints (("Goal" :induct (fill-regs i v mach))))

; Resizing: a resizable field's length changes and its new cells read as the
; :initially value.
(defun grow-mem (n mach)
  (declare (xargs :stobjs mach :guard (natp n)))
  (resize-mem n mach))

; Logically the resize is RESIZE-LIST, about which nothing is built in.
(defthm len-of-resize-list
  (equal (len (resize-list lst n default)) (nfix n)))

(defthm mem-length-of-grow-mem
  (equal (mem-length (grow-mem n mach)) (nfix n)))

; Hash-table field: logically an alist read with hons-assoc-equal.
(defun note-seen (k mach)
  (declare (xargs :stobjs mach :guard (eqlablep k)))
  (seen-put k t mach))

(defthm seen-get-of-note-seen
  (seen-get k (note-seen k mach)))

; Execution on the live stobj.
(make-event
 (let ((mach (fill-regs 0 7 mach)))
   (mv nil '(value-triple :filled) state mach)))

(assert-event (and (equal (regsi 0 mach) 7) (equal (regsi 7 mach) 7)))
