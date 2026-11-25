(in-package "ACL2")

(include-book "pole-cluster-powers")

; Large coefficients for an entire finite positive-multiplicity cluster.
; The total weight is proved nonzero from geometry, rather than supplied.

(local (defthm lw-pcs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcs-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcs-times-negative)))))

(local (defthm lw-pcs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcs-left-commutes)))))

(defun lw-pole-cluster-large-index (center entries radius start)
 (lw-power-sum-large-index (lw-pole-cluster-power-system center entries radius) start))

(defun lw-pole-cluster-large-cap (center entries radius start)
 (lw-power-large-term-cap (lw-pole-cluster-power-system center entries radius) start))

(local (defthm lw-pcs-consp
 (implies (consp entries) (consp (lw-pole-cluster-power-system center entries radius)))
 :hints (("Goal" :expand ((lw-pole-cluster-power-system center entries radius))))))

(local (defthm lw-pcs-total-nonzero
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (lw-pole-cluster-check center entries radius))
  (not (equal (lw-weighted-power-sum
                (lw-pole-cluster-power-system center entries radius) 0) (cons 0 0))))
 :hints (("Goal" :use (lw-pole-cluster-total-weight-positive)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-pole-cluster-large-cap-positive
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (lw-pole-cluster-check center entries radius))
  (and (rationalp (lw-pole-cluster-large-cap center entries radius start))
       (< 0 (lw-pole-cluster-large-cap center entries radius start))))
 :hints (("Goal"
  :use ((:instance lw-power-large-term-cap-valid
          (entries (lw-pole-cluster-power-system center entries radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-large-cap lw-pole-cluster-power-system-typed lw-pcs-total-nonzero lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-pole-cluster-large-index-certificate
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (< 0 radius) (natp start)
               (lw-pole-cluster-check center entries radius))
  (let ((index (lw-pole-cluster-large-index center entries radius start)))
   (and (natp index) (< start index) (<= index (+ start (len entries)))
        (not (lw-complex-diskp
               (lw-complex-scale (lw-rational-power radius index)
                                 (lw-pole-log-coefficient-sum center entries index))
               (lw-pole-cluster-large-cap center entries radius start))))))
 :hints (("Goal"
  :use (lw-pcs-total-nonzero
        (:instance lw-power-sum-large-index-certificate
          (entries (lw-pole-cluster-power-system center entries radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-large-index lw-pole-cluster-large-cap lw-pcs-consp lw-pcs-total-nonzero lw-pole-cluster-power-system-outer lw-pole-cluster-power-system-length lw-pole-cluster-power-sum-coefficients lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pcs-mul-real
 (implies (and (rationalp factor) (lw-complexp point))
          (equal (lw-complex-mul (cons factor 0) point)
                 (lw-complex-scale factor point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-mul lw-complex-scale lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pcs-zero-power
 (equal (lw-complex-power point 0) (cons 1 0))
 :hints (("Goal" :in-theory (enable lw-complex-power)))))

(defthm lw-pole-cluster-total-weight-log-derivative
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries) (rationalp radius))
  (equal (lw-weighted-power-sum (lw-pole-cluster-power-system center entries radius) 0)
         (lw-factor-model-log-sum center entries)))
 :hints (("Goal" :induct (lw-pole-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-power-system lw-weighted-power-sum lw-factor-model-log-sum lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-complex-scale-rational lw-pole-resolvent-data lw-pole-resolvent-factor lw-complex-mul-one lw-complex-reciprocal-rational lw-pcs-zero-power lw-pcs-mul-real lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-pole-cluster-away-check
 (implies (lw-pole-cluster-check center entries radius)
          (lw-factor-model-away-check center entries))
 :hints (("Goal" :induct (lw-pole-cluster-check center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-check lw-factor-model-away-check lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-pole-cluster-total-weight-quotient
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (lw-pole-cluster-check center entries radius))
  (equal (lw-weighted-power-sum (lw-pole-cluster-power-system center entries radius) 0)
         (lw-complex-quotient (lw-factor-model-derivative center entries)
                              (lw-factor-model-value center entries))))
 :hints (("Goal" :use ((:instance lw-factor-model-log-derivative (point center)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-total-weight-log-derivative lw-pole-cluster-away-check lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pcs-reconstruct
 (implies (consp point) (equal (cons (car point) (cdr point)) point))))

(local (defthm lw-pcs-add-sub-exact
 (implies (and (lw-complexp exact) (lw-complexp approximate))
          (equal (lw-complex-add approximate (lw-complex-sub exact approximate)) exact))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-pcs-reconstruct lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pcs-quarters
 (implies (rationalp cap)
  (equal (+ (* 1/2 cap) (* 1/4 cap)) (* 3/4 cap)))))

(defthm lw-complex-large-value-stable
 (implies (and (lw-complexp exact) (lw-complexp approximate)
               (rationalp cap) (< 0 cap)
               (not (lw-complex-diskp exact cap))
               (lw-complex-diskp (lw-complex-sub exact approximate) (* 1/4 cap)))
  (not (lw-complex-diskp approximate (* 1/2 cap))))
 :hints (("Goal"
  :use ((:instance lw-complex-add-disk (left approximate) (right (lw-complex-sub exact approximate))
          (radius (* 1/2 cap)) (other-radius (* 1/4 cap)))
        (:instance lw-complex-disk-enlarge (point exact) (radius (* 3/4 cap))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pcs-add-sub-exact lw-pcs-quarters lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-pole-cluster-large-approximation-certificate
 (implies (and (consp entries) (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (< 0 radius) (natp start)
               (lw-pole-cluster-check center entries radius) (lw-complexp approximate)
               (lw-complex-diskp
                (lw-complex-sub
                 (lw-complex-scale
                   (lw-rational-power radius (lw-pole-cluster-large-index center entries radius start))
                   (lw-pole-log-coefficient-sum center entries
                     (lw-pole-cluster-large-index center entries radius start)))
                 approximate)
                (* 1/4 (lw-pole-cluster-large-cap center entries radius start))))
  (not (lw-complex-diskp approximate
          (* 1/2 (lw-pole-cluster-large-cap center entries radius start)))))
 :hints (("Goal"
  :use (lw-pole-cluster-large-index-certificate
        lw-pole-cluster-large-cap-positive
        (:instance lw-complex-large-value-stable
          (exact (lw-complex-scale
                   (lw-rational-power radius (lw-pole-cluster-large-index center entries radius start))
                   (lw-pole-log-coefficient-sum center entries
                     (lw-pole-cluster-large-index center entries radius start))))
          (cap (lw-pole-cluster-large-cap center entries radius start))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-log-coefficient-sum-rational lw-rational-power-rational lw-complex-scale-rational lw-complex-operations-rational lw-pcs-left-commutes lw-pcs-left-distributes lw-pcs-fold-constants lw-pcs-times-negative lw-pcs-negative-times lw-pcs-zero-times lw-pcs-minus-one lw-pcs-double-negative lw-pcs-add-cancel lw-pcs-double lw-pcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

