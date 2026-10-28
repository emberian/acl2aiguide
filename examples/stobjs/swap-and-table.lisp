; examples/stobjs/swap-and-table.lisp
;
; Two smaller stobj facilities.  swap-stobjs exchanges two congruent stobjs
; in constant time (logically it returns them in reverse order: :doc
; swap-stobjs).  A stobj-table field maps stobj NAMES to stobjs and is read
; and written through stobj-let, the default creator call supplying a fresh
; stobj for an absent key (:doc stobj-table, following the example in
; std/stobjs/stobj-table.lisp).
;
; Cited by humans/03-modelling-data.md, "Nested stobjs and stobj-let".

(in-package "ACL2")

; --- swap-stobjs: double buffering with congruent stobjs.

(defstobj front (front-val :initially 0))
(defstobj back (back-val :initially 0) :congruent-to front)

; Write into the back buffer, then flip: front becomes what back was.
(defun draw-and-flip (v front back)
  (declare (xargs :stobjs (front back)))
  (let ((back (update-front-val v back)))   ; congruent: front's updater on back
    (swap-stobjs front back)))

(defthm draw-and-flip-shows-the-drawing
  (equal (front-val (mv-nth 0 (draw-and-flip v front back))) v))

(make-event
 (mv-let (front back) (draw-and-flip 7 front back)
   (mv nil `(defconst *flipped* ',(list (front-val front) (front-val back)))
       state front back)))

(assert-event (equal *flipped* '(7 0)))

; --- a stobj-table field.

(defstobj ctr1 (n1 :type (integer 0 *) :initially 0))
(defstobj tbl (stobjs :type (stobj-table)))

(defun bump-ctr1-in-tbl (tbl)
  (declare (xargs :stobjs tbl))
  (stobj-let ((ctr1 (stobjs-get 'ctr1 tbl (create-ctr1))))
             (ctr1)
             (update-n1 (+ 1 (n1 ctr1)) ctr1)
             tbl))

(defun read-ctr1-in-tbl (tbl)
  (declare (xargs :stobjs tbl))
  (stobj-let ((ctr1 (stobjs-get 'ctr1 tbl (create-ctr1))))
             (val)
             (n1 ctr1)
             val))

; Read-over-write, as std/stobjs/stobj-table.lisp proves it.
(defthm read-ctr1-of-bump
  (implies (tblp tbl)
           (equal (read-ctr1-in-tbl (bump-ctr1-in-tbl tbl))
                  (+ 1 (read-ctr1-in-tbl tbl)))))

(assert-event
 (let ((tbl (bump-ctr1-in-tbl tbl)))
   (mv (equal (read-ctr1-in-tbl tbl) 1) tbl))
 :stobjs-out '(nil tbl))
