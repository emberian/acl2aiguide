; examples/assured/sim.lisp
;
; What it shows: deterministic simulation as a gate, at the size of one
; page, with the three properties fn2's simulator had to be repaired to
; have (fn2/sim/ @127f7b877; REVIEW-SINS-20261028.md findings S1, S2, T1,
; T3; fn2/docs/a-pool-host-sim.md section 6 "Fault selection and landing
; coverage"):
;
;   1. Seeded and replayable.  One xorshift32 generator, seeded from the
;      run's seed; a run is a function of (seed, profile), so its
;      fingerprint is a constant the book can state, and the same seed
;      gives the same fingerprint (fn2 uses xoshiro128**, fn2/sim/prng.lisp).
;   2. Faults land, and only landings count.  The fault is chosen AFTER the
;      flight, from the classes applicable to that flight, and a class is
;      counted only when its effect happened.  The variant DRAW-HITS counts
;      draws the way fn2's first simulator did (finding S1): on a one-byte
;      reply the short-send class can never apply, yet draws report it
;      exercised.
;   3. The checker compares witnesses, not verdicts.  CHECK-ECHO compares
;      the bytes the client received against the bytes the client sent
;      (the client oracle never reads server state), and attributes every
;      shortfall to a landed reset.  CHECK-VERDICT trusts the server's own
;      "all sent" flag.  A mutant server with fn2's own proposed mutation
;      (wrong short-send accumulation, COHERENCE.md section 6.1: off = count
;      instead of off = old-off + count; here the new offset is the larger
;      of count and the old offset) fails the witness checker on 24 of 200
;      seeds and the verdict checker on 12: the verdict checker sees only
;      the runs where the mutant stalls, and passes 12 runs on which the
;      server reported "all sent" after sending wrong bytes.
;
; The system: one connection; the server holds a reply of N bytes and
; sends it in flights; each flight may be shortened (:short), held a tick
; (:delay) or the connection reset (:reset).
;
; Cited by assured/humans/02-simulation-and-checkers.md and
; assured/ai/02-simulation-and-checkers.md.

(in-package "ACL2")
(include-book "std/lists/take" :dir :system)
(include-book "std/lists/nthcdr" :dir :system)
(include-book "std/lists/append" :dir :system)

(defconst *max-ticks* 64)

; --- 1. The generator --------------------------------------------------

(defun u32 (x) (declare (xargs :guard (integerp x))) (mod (ifix x) 4294967296))
; A draw reduced to 0..n-1.
(defun modn (x n)
  (declare (xargs :guard (and (natp x) (posp n))))
  (mod (nfix x) (if (posp n) n 1)))

(encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm u32-natp (natp (u32 x)) :rule-classes :type-prescription)
  (defthm u32-bound (< (u32 x) 4294967296) :rule-classes :linear)
  (defthm modn-natp (natp (modn x n)) :rule-classes :type-prescription)
  (defthm modn-bound (implies (posp n) (< (modn x n) n)) :rule-classes :linear))
(in-theory (disable modn))
(in-theory (disable u32))

(defun xorshift32 (x)
  (declare (xargs :guard (natp x)))
  (let* ((x (u32 (logxor x (ash x 13))))
         (x (u32 (logxor x (ash x -17))))
         (x (u32 (logxor x (ash x 5)))))
    x))

(defthm xorshift32-natp (natp (xorshift32 x)) :rule-classes :type-prescription)
(in-theory (disable xorshift32))

(defun seed-state (seed)
  (declare (xargs :guard (natp seed)))
  (let ((x (u32 (+ 1 (* 2654435761 seed)))))
    (if (zp x) 1 x)))

(defthm seed-state-natp (natp (seed-state seed)) :rule-classes :type-prescription)
(in-theory (disable seed-state))

; --- The system and its faults -------------------------------------------

; Fault classes and their per-mille thresholds in the :broad profile.
(defconst *classes* '(:short :delay :reset))
(defun threshold (profile class)
  (declare (xargs :guard t))
  (cond ((eq profile :none) 0)
        ((eq class :short) 400)
        ((eq class :delay) 200)
        ((eq class :reset) 30)
        (t 0)))

; Which classes can apply to a send flight with REMAINING bytes: a short
; send needs at least two bytes to shorten.
(defun applicable (remaining)
  (declare (xargs :guard (natp remaining)))
  (if (<= 2 remaining) '(:short :delay :reset) '(:delay :reset)))

; Choose a class for this flight: pick among the applicable classes, then
; compare a draw with the class's threshold.  Answers (mv class rng).
(defun choose-fault (profile remaining rng)
  (declare (xargs :guard (and (natp remaining) (natp rng))))
  (let* ((cands (applicable remaining))
         (rng (xorshift32 rng))
         (class (nth (modn rng (len cands)) cands))
         (rng (xorshift32 rng)))
    (if (< (modn rng 1000) (threshold profile class))
        (mv class rng)
      (mv nil rng))))

(defthm choose-fault-rng-natp
  (natp (mv-nth 1 (choose-fault profile remaining rng)))
  :rule-classes :type-prescription)
(in-theory (disable choose-fault))

; Landings, counted at the effect: (short delay reset).
(defun land (class landed)
  (declare (xargs :guard (true-listp landed)))
  (case class
    (:short (list (+ 1 (nfix (nth 0 landed))) (nth 1 landed) (nth 2 landed)))
    (:delay (list (nth 0 landed) (+ 1 (nfix (nth 1 landed))) (nth 2 landed)))
    (:reset (list (nth 0 landed) (nth 1 landed) (+ 1 (nfix (nth 2 landed)))))
    (otherwise landed)))

; One send flight from OFF in a reply of length N.  MUTANTP selects the
; mutated offset update.  Answers (mv sent-bytes new-off).
(defun send-flight (reply off count mutantp)
  (declare (xargs :guard (and (true-listp reply) (natp off) (natp count))))
  (let ((bytes (take (min count (nfix (- (len reply) off))) (nthcdr off reply))))
    (mv bytes (if mutantp (max count off) (+ off (len bytes))))))

(defthm send-flight-bytes-true-listp
  (true-listp (car (send-flight reply off count mutantp))))
(defthm send-flight-off-natp
  (implies (and (natp off) (natp count))
           (natp (mv-nth 1 (send-flight reply off count mutantp))))
  :rule-classes :type-prescription)
(defthm land-true-listp
  (implies (true-listp landed) (true-listp (land class landed)))
  :rule-classes :type-prescription)
(in-theory (disable send-flight land))

; The run: (mv received reset-p server-says-done landed rng), bounded by
; FUEL ticks (the measure), never by the reply's progress.
(defun run-echo (reply off received landed rng profile mutantp fuel)
  (declare (xargs :guard (and (true-listp reply) (natp off) (true-listp received)
                              (true-listp landed) (natp rng) (natp fuel))
                  :measure (nfix fuel)))
  (let ((remaining (nfix (- (len reply) off))))
    (if (or (zp fuel) (zp remaining))
        (mv received nil (zp remaining) landed rng)
      (mv-let (class rng) (choose-fault profile remaining rng)
        (cond
         ((eq class :reset)
          (mv received t nil (land :reset landed) rng))
         ((eq class :delay)
          (run-echo reply off received (land :delay landed) rng profile mutantp
                    (- fuel 1)))
         (t
          (let* ((rng (xorshift32 rng))
                 ; a landed short sends 1..remaining-1 bytes; otherwise all
                 (shortp (and (eq class :short) (<= 2 remaining)))
                 (count (if shortp (+ 1 (modn rng (- remaining 1))) remaining))
                 (landed (if shortp (land :short landed) landed)))
            (mv-let (bytes off2) (send-flight reply off count mutantp)
              (run-echo reply off2 (append received bytes) landed rng profile
                        mutantp (- fuel 1))))))))))

(defthm run-echo-received-true-listp
  (implies (true-listp received)
           (true-listp (car (run-echo reply off received landed rng profile
                                        mutantp fuel)))))
(defthm run-echo-landed-true-listp
  (implies (true-listp landed)
           (true-listp (mv-nth 3 (run-echo reply off received landed rng profile
                                           mutantp fuel)))))

(defun reply-of (seed n)
  ; The reply bytes are distinct per position, so a repeated or skipped
  ; byte is visible to the client oracle.
  (declare (xargs :guard (and (natp seed) (natp n))))
  (if (zp n) nil
    (append (reply-of seed (- n 1)) (list (mod (+ seed n) 256)))))

(defun run-seed (seed n profile mutantp)
  (declare (xargs :guard (and (natp seed) (natp n))))
  (run-echo (reply-of seed n) 0 nil '(0 0 0) (seed-state seed) profile mutantp
            *max-ticks*))

(defthm run-seed-received-true-listp
  (true-listp (car (run-seed seed n profile mutantp))))
(defthm run-seed-landed-true-listp
  (true-listp (mv-nth 3 (run-seed seed n profile mutantp))))
(in-theory (disable run-seed))

; --- 3. Checkers ---------------------------------------------------------

; The witness checker: the client's received bytes against the bytes it
; is owed.  Equal, or a strict prefix explained by a landed reset;
; anything else is a failure naming the first divergent position.
(defun first-divergence (got want i)
  (declare (xargs :guard (and (true-listp got) (true-listp want) (natp i))))
  (cond ((atom got) (if (atom want) nil (list :short-at i)))
        ((atom want) (list :extra-at i (car got)))
        ((not (equal (car got) (car want))) (list :byte-at i (car want) (car got)))
        (t (first-divergence (cdr got) (cdr want) (+ 1 i)))))

(defun check-echo (got want reset-p)
  (declare (xargs :guard (and (true-listp got) (true-listp want))))
  (let ((d (first-divergence got want 0)))
    (cond ((null d) :pass)
          ((and reset-p (eq (car d) :short-at)) :pass) ; attributed drop
          (t (list :fail d)))))

; The verdict checker: believes the server.
(defun check-verdict (done reset-p)
  (declare (xargs :guard t))
  (if (or done reset-p) :pass (list :fail :not-done)))

; A sweep over seeds 1..K: the first failing seed and its witness, or :ok.
(defun sweep (k n profile mutantp witnessp)
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp k) :ok
    (let ((rest (sweep (- k 1) n profile mutantp witnessp)))
      (if (not (eq rest :ok)) rest
        (mv-let (got reset-p done landed rng) (run-seed k n profile mutantp)
          (declare (ignore landed rng))
          (let ((v (if witnessp
                       (check-echo got (reply-of k n) reset-p)
                     (check-verdict done reset-p))))
            (if (eq v :pass) :ok (list :seed k v))))))))

; Detections of the mutant over seeds 1..K, per checker:
; (witness-failures verdict-failures witness-only).
(defun detections (k n)
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp k) '(0 0 0)
    (mv-let (got reset-p done landed rng) (run-seed k n :broad t)
      (declare (ignore landed rng))
      (let* ((w (if (eq (check-echo got (reply-of k n) reset-p) :pass) 0 1))
             (v (if (eq (check-verdict done reset-p) :pass) 0 1))
             (rest (detections (- k 1) n)))
        (list (+ w (nfix (nth 0 rest)))
              (+ v (nfix (nth 1 rest)))
              (+ (if (and (= w 1) (= v 0)) 1 0) (nfix (nth 2 rest))))))))

; Landing coverage summed over a sweep: (short delay reset).
(defun coverage (k n profile)
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp k) '(0 0 0)
    (mv-let (got reset-p done landed rng) (run-seed k n profile nil)
      (declare (ignore got reset-p done rng))
      (let ((rest (coverage (- k 1) n profile)))
        (list (+ (nfix (nth 0 landed)) (nfix (nth 0 rest)))
              (+ (nfix (nth 1 landed)) (nfix (nth 1 rest)))
              (+ (nfix (nth 2 landed)) (nfix (nth 2 rest))))))))

; fn2's first counting, for contrast: one draw per flight from ALL classes,
; counted as a hit whether or not it could apply.
(defun draw-hits (k n)
  (declare (xargs :guard (and (natp k) (natp n))))
  (if (zp k) 0
    (let* ((rng (xorshift32 (seed-state k)))
           (class (nth (modn rng 3) *classes*))
           (rng (xorshift32 rng)))
      (+ (if (and (eq class :short) (< (modn rng 1000) (threshold :broad :short))) 1 0)
         (draw-hits (- k 1) n)))))

; --- The gate --------------------------------------------------------------

; Replay: the same seed gives the same run, so the run is a constant.
(assert-event (equal (mv-list 5 (run-seed 73 12 :broad nil))
                     (mv-list 5 (run-seed 73 12 :broad nil))))

; The real server passes the witness checker on every seed.
(assert-event (eq (sweep 200 12 :broad nil t) :ok))

; Every class LANDED at least once over the sweep (not merely drawn).
(assert-event (let ((c (coverage 200 12 :broad)))
                (and (< 0 (nth 0 c)) (< 0 (nth 1 c)) (< 0 (nth 2 c)))))

; The mutant.  The witness checker's first catch is a constant, because
; the run is deterministic: seed 8, an extra byte at position 12.
(assert-event (equal (sweep 200 12 :broad t t)
                     '(:seed 8 (:fail (:extra-at 12 19)))))
; Over 200 seeds the witness checker fails 24 runs; the verdict checker
; fails 12 (the runs where the mutant stalls and never reports done), and
; passes 12 runs on which the server reported done after sending wrong
; bytes.
(assert-event (equal (detections 200 12) '(24 12 12)))

; Without landed faults the mutant is invisible: coverage is what makes a
; simulation a gate.
(assert-event (eq (sweep 200 12 :none t t) :ok))

; Draws are not landings: with one-byte replies a short send can never
; apply, so no short ever lands, yet the draw counter reports hundreds.
(assert-event (equal (nth 0 (coverage 1000 1 :broad)) 0))
(assert-event (< 100 (draw-hits 1000 1)))
