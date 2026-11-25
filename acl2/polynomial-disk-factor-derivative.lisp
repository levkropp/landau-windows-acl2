(in-package "ACL2")

(include-book "polynomial-disk-factorization")
(include-book "polynomial-local-derivative-comparison")

; Use the gap between the two disk radii for local Cauchy extraction.

(local (defthm lw-dfd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dfd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dfd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dfd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dfd-times-negative (a b) (b a)))
                 :in-theory (disable lw-dfd-times-negative)))))

(local (defthm lw-dfd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dfd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dfd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dfd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dfd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dfd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dfd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dfd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dfd-left-commutes)))))

(local (defthm lw-dfd-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-dfd-centered-sample
 (implies (and (rationalp outer-radius) (rationalp inner-radius) (< inner-radius outer-radius)
               (lw-complex-diskp center inner-radius) (lw-complex-diskp point 1))
  (lw-complex-diskp (lw-complex-add center (lw-complex-scale (- outer-radius inner-radius) point)) outer-radius))
 :hints (("Goal"
  :use ((:instance lw-complex-scale-disk (factor (- outer-radius inner-radius)) (radius 1))
        (:instance lw-complex-add-disk (left center) (radius inner-radius)
         (right (lw-complex-scale (- outer-radius inner-radius) point)) (other-radius (- outer-radius inner-radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ abs lw-dfd-sum-rational lw-dfd-left-commutes lw-dfd-left-distributes lw-dfd-fold-constants lw-dfd-times-negative lw-dfd-negative-times lw-dfd-zero-times lw-dfd-minus-one lw-dfd-double-negative lw-dfd-add-cancel lw-dfd-double lw-dfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defun lw-dfd-countdown (samples)
 (declare (xargs :measure (nfix samples) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp samples) 0 (lw-dfd-countdown (- samples 1)))))

(local (defthm lw-dfd-generated-boundary-check
 (implies (and (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)) (lw-complex-diskp point 1) (natp samples))
  (lw-cauchy-boundary-check (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius)) point 0 samples epsilon))
 :hints (("Goal" :induct (lw-dfd-countdown samples)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-dfd-countdown) lw-cauchy-boundary-check lw-dfd-left-commutes lw-dfd-left-distributes lw-dfd-fold-constants lw-dfd-times-negative lw-dfd-negative-times lw-dfd-zero-times lw-dfd-minus-one lw-dfd-double-negative lw-dfd-add-cancel lw-dfd-double lw-dfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use (lw-polynomial-disk-factor-data
          (:instance lw-complex-disk-data (point center) (radius inner-radius))
          (:instance lw-complex-power-disk (radius 1) (index (- samples 1)))
          (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
          (:instance lw-dfd-centered-sample (point (lw-complex-power point (- samples 1))))
          (:instance lw-polynomial-local-difference-evaluation
           (left coefficients) (right (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon)) (radius (- outer-radius inner-radius)) (point (lw-complex-power point (- samples 1))))
          (:instance lw-polynomial-disk-factor-value-error (point (lw-complex-add center (lw-complex-scale (- outer-radius inner-radius) (lw-complex-power point (- samples 1)))))))
    :in-theory (union-theories
 '(fold-consts-in-+ lw-rational-power-one lw-dfd-sum-rational lw-dfd-left-commutes lw-dfd-left-distributes lw-dfd-fold-constants lw-dfd-times-negative lw-dfd-negative-times lw-dfd-zero-times lw-dfd-minus-one lw-dfd-double-negative lw-dfd-add-cancel lw-dfd-double lw-dfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
    :do-not-induct t)))))

(local (defthm lw-dfd-unscale-identity
 (implies (and (rationalp gap) (< 0 gap) (lw-complexp point))
  (equal (lw-complex-scale (/ gap) (lw-complex-scale gap point)) point))
 :hints (("Goal"
  :use ((:instance lw-dfd-inverse-factor (divisor gap) (coefficient (car point)))
        (:instance lw-dfd-inverse-factor (divisor gap) (coefficient (cdr point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complexp cons-car-cdr lw-dfd-left-commutes lw-dfd-left-distributes lw-dfd-fold-constants lw-dfd-times-negative lw-dfd-negative-times lw-dfd-zero-times lw-dfd-minus-one lw-dfd-double-negative lw-dfd-add-cancel lw-dfd-double lw-dfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-dfd-unscale-disk
 (implies (and (rationalp gap) (< 0 gap) (lw-complexp point)
               (lw-complex-diskp (lw-complex-scale gap point) cap))
  (lw-complex-diskp point (* cap (/ gap))))
 :hints (("Goal"
  :use (lw-dfd-unscale-identity (:instance lw-reciprocal-positive (value gap))
        (:instance lw-complex-scale-disk (point (lw-complex-scale gap point)) (factor (/ gap)) (radius cap)))
  :in-theory (union-theories
 '(fold-consts-in-+ abs lw-dfd-left-commutes lw-dfd-left-distributes lw-dfd-fold-constants lw-dfd-times-negative lw-dfd-negative-times lw-dfd-zero-times lw-dfd-minus-one lw-dfd-double-negative lw-dfd-add-cancel lw-dfd-double lw-dfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-disk-factor-derivative-error
 (implies (and (and (lw-complex-coefficientsp coefficients) (rationalp outer-radius) (<= 0 outer-radius) (rationalp epsilon) (< 0 epsilon)) (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius outer-radius) (lw-complex-diskp center inner-radius)) (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial-derivative coefficients center) (lw-complex-polynomial-derivative (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center)) (* epsilon (/ (- outer-radius inner-radius)))))
 :hints (("Goal"
  :use (lw-polynomial-disk-factor-data
        (:instance lw-complex-disk-data (point center) (radius inner-radius))
        (:instance lw-polynomial-local-difference-valid (left coefficients) (right (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon)) (radius (- outer-radius inner-radius)))
        (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius))) (cap epsilon))
        (:instance lw-cauchy-orbit-data (degree (len (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius)))))
        (:instance lw-dfd-generated-boundary-check
         (point (lw-cauchy-orbit-rotation (len (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius)))))
         (samples (lw-cauchy-coefficient-count (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius)) (len (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius))) (lw-polynomial-cap-test-error (lw-polynomial-local-difference coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center (- outer-radius inner-radius)) epsilon))))
        (:instance lw-polynomial-local-difference-derivative (left coefficients) (right (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon)) (radius (- outer-radius inner-radius)) (cap epsilon))
        (:instance lw-complex-polynomial-derivative-rational (point center))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon)) (point center))
        (:instance lw-complex-ring-rational
          (left (lw-complex-polynomial-derivative coefficients center)) (right (lw-complex-polynomial-derivative (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center)))
        (:instance lw-dfd-unscale-disk (point (lw-complex-sub (lw-complex-polynomial-derivative coefficients center) (lw-complex-polynomial-derivative (lw-polynomial-disk-factor-polynomial coefficients outer-radius epsilon) center))) (gap (- outer-radius inner-radius)) (cap epsilon)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-cauchy-cap-check lw-dfd-sum-rational lw-dfd-left-commutes lw-dfd-left-distributes lw-dfd-fold-constants lw-dfd-times-negative lw-dfd-negative-times lw-dfd-zero-times lw-dfd-minus-one lw-dfd-double-negative lw-dfd-add-cancel lw-dfd-double lw-dfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
