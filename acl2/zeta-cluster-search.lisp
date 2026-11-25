(in-package "ACL2")

(include-book "zeta-cluster-quadratic")

; Bounded large-term search for the actual normalized zeta principal
; parts. Cancellation of their initial aggregate is allowed. A positive
; pole cluster forces a large normalized term in M+2 consecutive orders.

(local (defthm lw-zcs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zcs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zcs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zcs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zcs-times-negative (a b) (b a)))
                 :in-theory (disable lw-zcs-times-negative)))))

(local (defthm lw-zcs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zcs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zcs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zcs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zcs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zcs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zcs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zcs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zcs-left-commutes)))))

(defun lw-zeta-cluster-power-system (center entries radius)
 (if (endp entries) nil
  (let ((offset (lw-complex-sub center (caar entries))))
   (cons (cons (lw-pole-resolvent-ratio offset radius)
               (lw-pole-resolvent-factor
                (lw-zeta-pole-residue (caar entries) (cdar entries)) offset))
         (lw-zeta-cluster-power-system center (cdr entries) radius)))))

(defun lw-zeta-cluster-large-cap (center entries radius start)
 (* 1/2 (lw-pole-cluster-large-cap center entries radius start)
    (/ (lw-pole-unit-quadratic-cap center radius))))

(defun lw-zeta-cluster-large-index (center entries radius start)
 (lw-power-block-search (lw-zeta-cluster-power-system center entries radius)
                       (- start 1) (+ 2 (len entries))
                       (lw-zeta-cluster-large-cap center entries radius start)))

(defthm lw-zeta-cluster-power-system-length
 (equal (len (lw-zeta-cluster-power-system center entries radius)) (len entries))
 :hints (("Goal" :induct (lw-zeta-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-cluster-power-system len lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zcs-ratio-rational
 (implies (and (lw-complexp offset) (rationalp radius))
          (lw-complexp (lw-pole-resolvent-ratio offset radius)))
 :hints (("Goal" :use ((:instance lw-pole-resolvent-data (residue (cons 0 0))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-zeta-cluster-power-system-typed
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries) (rationalp radius))
  (lw-power-systemp (lw-zeta-cluster-power-system center entries radius)))
 :hints (("Goal" :induct (lw-zeta-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-cluster-power-system lw-power-systemp lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-zeta-pole-residue-rational lw-zcs-ratio-rational lw-pole-resolvent-data lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zcs-unit-term
 (implies (and (lw-complexp residue) (lw-complexp offset)
               (rationalp radius) (natp index))
  (equal
   (lw-complex-mul (lw-pole-resolvent-factor residue offset)
                   (lw-complex-power (lw-pole-resolvent-ratio offset radius) index))
   (lw-complex-scale (lw-rational-power radius index)
                     (lw-pole-coefficient residue offset index))))
 :hints (("Goal" :use (lw-pole-unit-coefficient-scaled)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-unit-coefficient lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-zeta-cluster-power-sum-coefficients
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (natp index))
  (equal
   (lw-weighted-power-sum (lw-zeta-cluster-power-system center entries radius) index)
   (lw-complex-scale (lw-rational-power radius index)
                     (lw-zeta-pole-coefficient-sum center entries index))))
 :hints (("Goal" :induct (lw-zeta-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-cluster-power-system lw-weighted-power-sum lw-zeta-pole-coefficient-sum lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-zeta-pole-residue-rational lw-zeta-pole-coefficient-sum-rational lw-pole-coefficient-rational lw-zcs-unit-term lw-rational-power-rational lw-complex-scale-add lw-complex-scale-zero lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zcs-positive-inverse
 (implies (and (rationalp factor) (< 0 factor)) (< 0 (/ factor)))
 :hints (("Goal" :use ((:instance inverse-of-* (x factor)))
          :in-theory (disable inverse-of-*) :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcs-cap-algebra
 (implies (and (rationalp cap) (< 0 cap) (rationalp factor) (<= 1 factor))
  (and (rationalp (* 1/2 cap (/ factor))) (< 0 (* 1/2 cap (/ factor)))
       (equal (* factor 1/2 cap (/ factor)) (* 1/2 cap))))
 :hints (("Goal"
  :use ((:instance lw-zcs-positive-inverse)
        (:instance lw-zcs-inverse-factor (divisor factor) (coefficient (* 1/2 cap))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-zeta-cluster-large-cap-valid
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (lw-pole-cluster-check center entries radius))
  (and (rationalp (lw-zeta-cluster-large-cap center entries radius start))
       (< 0 (lw-zeta-cluster-large-cap center entries radius start))
       (equal
        (* (lw-pole-unit-quadratic-cap center radius)
           (lw-zeta-cluster-large-cap center entries radius start))
        (* 1/2 (lw-pole-cluster-large-cap center entries radius start)))))
 :hints (("Goal"
  :use ((:instance lw-zcs-cap-algebra
          (cap (lw-pole-cluster-large-cap center entries radius start))
          (factor (lw-pole-unit-quadratic-cap center radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-cluster-large-cap lw-pole-cluster-large-cap-positive lw-pole-unit-quadratic-cap-valid lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zcs-negated-disk
 (implies (lw-complexp point)
  (equal (lw-complex-diskp (lw-complex-scale -1 point) cap)
         (lw-complex-diskp point cap)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-diskp lw-complex-scale lw-diskp lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-zcs-small-quadratic
 (implies (and (lw-complexp center) (rationalp radius) (lw-complexp exact)
               (rationalp cap) (< 0 cap) (rationalp small) (<= 0 small)
               (equal (* small (lw-pole-unit-quadratic-cap center radius)) (* 1/2 cap))
               (lw-complex-diskp current small)
               (lw-complex-diskp previous small)
               (lw-complex-diskp earlier small)
               (equal (lw-pole-unit-quadratic-coefficient center radius current previous earlier)
                      (lw-complex-scale -1 exact)))
  (lw-complex-diskp exact cap))
 :hints (("Goal"
  :use ((:instance lw-pole-unit-quadratic-bound (cap small))
        (:instance lw-complex-disk-enlarge (point exact) (radius (* 1/2 cap))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zcs-negated-disk lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-zcs-length-natural
 (natp (len entries)) :rule-classes (:rewrite :type-prescription)))

(defthm lw-zeta-cluster-block-nontrivial
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (< 0 radius) (natp start) (<= 1 start)
               (lw-pole-cluster-check center entries radius))
  (not (lw-power-block-boundedp
         (lw-zeta-cluster-power-system center entries radius)
         (- start 1) (+ 2 (len entries))
         (lw-zeta-cluster-large-cap center entries radius start))))
 :hints (("Goal"
  :use (lw-pole-cluster-large-index-certificate
        lw-pole-cluster-large-cap-positive
        lw-zeta-cluster-large-cap-valid
        (:instance lw-zeta-pole-cluster-unit-quadratic
          (index (- (lw-pole-cluster-large-index center entries radius start) 2)))
        (:instance lw-power-block-at
          (entries (lw-zeta-cluster-power-system center entries radius))
          (start (- start 1)) (count (+ 2 (len entries)))
          (index (lw-pole-cluster-large-index center entries radius start))
          (cap (lw-zeta-cluster-large-cap center entries radius start)))
        (:instance lw-power-block-at
          (entries (lw-zeta-cluster-power-system center entries radius))
          (start (- start 1)) (count (+ 2 (len entries)))
          (index (- (lw-pole-cluster-large-index center entries radius start) 1))
          (cap (lw-zeta-cluster-large-cap center entries radius start)))
        (:instance lw-power-block-at
          (entries (lw-zeta-cluster-power-system center entries radius))
          (start (- start 1)) (count (+ 2 (len entries)))
          (index (- (lw-pole-cluster-large-index center entries radius start) 2))
          (cap (lw-zeta-cluster-large-cap center entries radius start)))
        (:instance lw-zcs-small-quadratic
          (cap (lw-pole-cluster-large-cap center entries radius start))
          (small (lw-zeta-cluster-large-cap center entries radius start))
          (exact (lw-complex-scale
            (lw-rational-power radius (lw-pole-cluster-large-index center entries radius start))
            (lw-pole-log-coefficient-sum center entries
             (lw-pole-cluster-large-index center entries radius start))))
          (current (lw-weighted-power-sum
            (lw-zeta-cluster-power-system center entries radius)
            (lw-pole-cluster-large-index center entries radius start)))
          (previous (lw-weighted-power-sum
            (lw-zeta-cluster-power-system center entries radius)
            (- (lw-pole-cluster-large-index center entries radius start) 1)))
          (earlier (lw-weighted-power-sum
            (lw-zeta-cluster-power-system center entries radius)
            (- (lw-pole-cluster-large-index center entries radius start) 2)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zcs-length-natural lw-zeta-cluster-power-sum-coefficients lw-pole-cluster-away-check lw-pole-log-coefficient-sum-rational lw-rational-power-rational lw-complex-scale-rational lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-zeta-cluster-large-index-certificate
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (< 0 radius) (natp start) (<= 1 start)
               (lw-pole-cluster-check center entries radius))
  (let ((index (lw-zeta-cluster-large-index center entries radius start)))
   (and (natp index) (<= (- start 1) index) (<= index (+ start (len entries)))
        (not (lw-complex-diskp
          (lw-complex-scale (lw-rational-power radius index)
            (lw-zeta-pole-coefficient-sum center entries index))
          (lw-zeta-cluster-large-cap center entries radius start))))))
 :hints (("Goal"
  :use (lw-zeta-cluster-block-nontrivial
        (:instance lw-power-block-search-empty
          (entries (lw-zeta-cluster-power-system center entries radius))
          (start (- start 1)) (count (+ 2 (len entries)))
          (cap (lw-zeta-cluster-large-cap center entries radius start)))
        (:instance lw-power-block-search-sound
          (entries (lw-zeta-cluster-power-system center entries radius))
          (start (- start 1)) (count (+ 2 (len entries)))
          (cap (lw-zeta-cluster-large-cap center entries radius start))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-cluster-large-index lw-zcs-length-natural lw-zeta-cluster-power-sum-coefficients lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-zeta-cluster-large-approximation-certificate
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (< 0 radius) (natp start) (<= 1 start)
               (lw-pole-cluster-check center entries radius) (lw-complexp approximate)
               (lw-complex-diskp
                (lw-complex-sub
                 (lw-complex-scale
                   (lw-rational-power radius (lw-zeta-cluster-large-index center entries radius start))
                   (lw-zeta-pole-coefficient-sum center entries
                     (lw-zeta-cluster-large-index center entries radius start)))
                 approximate)
                (* 1/4 (lw-zeta-cluster-large-cap center entries radius start))))
  (not (lw-complex-diskp approximate
          (* 1/2 (lw-zeta-cluster-large-cap center entries radius start)))))
 :hints (("Goal"
  :use (lw-zeta-cluster-large-index-certificate
        lw-zeta-cluster-large-cap-valid
        (:instance lw-complex-large-value-stable
          (exact (lw-complex-scale
                   (lw-rational-power radius (lw-zeta-cluster-large-index center entries radius start))
                   (lw-zeta-pole-coefficient-sum center entries
                     (lw-zeta-cluster-large-index center entries radius start))))
          (cap (lw-zeta-cluster-large-cap center entries radius start))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-pole-coefficient-sum-rational lw-rational-power-rational lw-complex-scale-rational lw-zcs-left-commutes lw-zcs-left-distributes lw-zcs-fold-constants lw-zcs-times-negative lw-zcs-negative-times lw-zcs-zero-times lw-zcs-minus-one lw-zcs-double-negative lw-zcs-add-cancel lw-zcs-double lw-zcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))


