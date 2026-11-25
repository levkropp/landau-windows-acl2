(in-package "ACL2")

(include-book "dirichlet-right-block-mass")
(include-book "hyperbola-majorants")

; Summing dyadic blocks leaves a tail proportional to the reciprocal cutoff.

(local (defthm lw-drdm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-drdm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-drdm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-drdm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-drdm-times-negative (a b) (b a)))
                 :in-theory (disable lw-drdm-times-negative)))))

(local (defthm lw-drdm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-drdm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-drdm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-drdm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-drdm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-drdm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-drdm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-drdm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drdm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drdm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-drdm-left-commutes)))))

(local (deftheory lw-drdm-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-drdm-left-commutes lw-drdm-left-distributes lw-drdm-fold-constants
              lw-drdm-times-negative lw-drdm-negative-times lw-drdm-zero-times
              lw-drdm-minus-one lw-drdm-double-negative lw-drdm-add-cancel lw-drdm-double lw-drdm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-dirichlet-sample-mass-rational
  (implies (and (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
           (and (rationalp (lw-dirichlet-sample-mass rate height start count error)) (<= 0 (lw-dirichlet-sample-mass rate height start count error))))
  :hints (("Goal"
           :induct (lw-dirichlet-sample-mass rate height start count error)
           :in-theory (union-theories '(lw-dirichlet-sample-mass) (theory 'lw-drdm-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-dirichlet-sample-rational (index start) (log-error error) (node-error error))
                       (:instance lw-complex-l1-bound (point (lw-dirichlet-sample rate height start error error))))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-dirichlet-sample-mass-split
  (implies (and (natp start) (natp first) (natp last)
                (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
           (equal (lw-dirichlet-sample-mass rate height start (+ first last) error)
                  (+ (lw-dirichlet-sample-mass rate height start first error) (lw-dirichlet-sample-mass rate height (+ start first) last error))))
  :hints (("Goal"
           :induct (lw-dirichlet-sample-mass rate height start first error)
           :in-theory (union-theories '(lw-dirichlet-sample-mass) (theory 'lw-drdm-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-dirichlet-sample-mass-rational (count last))
                       (:instance lw-dirichlet-sample-mass-rational (start (+ start first)) (count last)))
                 :do-not-induct t)))
  :rule-classes nil)

(defun lw-dirichlet-right-dyadic-cost (rate height lower upper)
  (declare (xargs :measure (nfix upper) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (or (zp upper) (<= upper lower)) 0
    (let ((start (lw-rational-power 2 (- upper 1))))
      (+ (lw-dirichlet-right-range-cost rate height start start) (lw-dirichlet-right-dyadic-cost rate height lower (- upper 1))))))

(local
 (defthm lw-drdm-span-data
   (implies (and (natp lower) (<= 2 lower) (natp upper) (< lower upper))
            (and (posp (lw-rational-power 2 lower)) (posp (lw-rational-power 2 (- upper 1)))
                 (natp (- (lw-rational-power 2 (- upper 1)) (lw-rational-power 2 lower))) (<= 4 (lw-rational-power 2 (- upper 1)))
                 (equal (- (lw-rational-power 2 upper) (lw-rational-power 2 lower)) (+ (- (lw-rational-power 2 (- upper 1)) (lw-rational-power 2 lower)) (lw-rational-power 2 (- upper 1))))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-natural (base 2) (exponent lower))
                  (:instance lw-rational-power-natural (base 2) (exponent (- upper 1)))
                  (:instance lw-rational-power-monotone-exponent (base 2) (small lower) (large (- upper 1)))
                  (:instance lw-rational-power-monotone-exponent (base 2) (small 2) (large lower)))
            :expand ((lw-rational-power 2 upper))
            :in-theory (union-theories '((:executable-counterpart lw-rational-power)) (theory 'lw-drdm-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-dirichlet-right-dyadic-mass-bound
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
       (natp lower) (<= 2 lower) (natp upper) (<= lower upper)
       (rationalp error) (< 0 error) (<= error 1))
   (and (rationalp (lw-dirichlet-right-dyadic-cost rate height lower upper)) (<= 0 (lw-dirichlet-right-dyadic-cost rate height lower upper))
        (<= (lw-dirichlet-sample-mass rate height (lw-rational-power 2 lower) (- (lw-rational-power 2 upper) (lw-rational-power 2 lower)) error) (+ (* (* 64 (/ (- rate 1)) (/ (- rate 1))) (lw-reciprocal-square-tail (- upper 1) (- lower 1))) (* (lw-dirichlet-right-dyadic-cost rate height lower upper) error)))))
  :hints (("Goal"
           :induct (lw-dirichlet-right-dyadic-cost rate height lower upper)
           :expand ((lw-dirichlet-right-dyadic-cost rate height lower upper) (lw-reciprocal-square-tail (- upper 1) (- lower 1)))
           :in-theory (union-theories '(lw-dirichlet-right-block-decay (:induction lw-dirichlet-right-dyadic-cost)) (theory 'lw-drdm-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-drdm-span-data
                       (:instance lw-dirichlet-right-block-mass-bound (block (- upper 1)) (start (lw-rational-power 2 (- upper 1))) (count (lw-rational-power 2 (- upper 1))))
                       (:instance lw-dirichlet-right-range-mass-bound (block (- upper 1)) (start (lw-rational-power 2 (- upper 1))) (count (lw-rational-power 2 (- upper 1))))
                       (:instance lw-dirichlet-sample-mass-split (start (lw-rational-power 2 lower)) (first (- (lw-rational-power 2 (- upper 1)) (lw-rational-power 2 lower))) (last (lw-rational-power 2 (- upper 1))))
                       (:instance lw-dirichlet-sample-mass-rational (start (lw-rational-power 2 lower)) (count (- (lw-rational-power 2 (- upper 1)) (lw-rational-power 2 lower))))
                       (:instance lw-dirichlet-sample-mass-rational (start (lw-rational-power 2 (- upper 1))) (count (lw-rational-power 2 (- upper 1))))
                       (:instance lw-reciprocal-square-tail-data (count (- upper 2)) (start (- lower 1))))
                 :expand ((lw-dirichlet-sample-mass rate height (lw-rational-power 2 lower) 0 error))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-dirichlet-right-dyadic-tail-bound
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
       (natp lower) (<= 2 lower) (natp upper) (<= lower upper)
       (rationalp error) (< 0 error) (<= error 1))
   (<= (lw-dirichlet-sample-mass rate height (lw-rational-power 2 lower) (- (lw-rational-power 2 upper) (lw-rational-power 2 lower)) error)
       (+ (* (* 64 (/ (- rate 1)) (/ (- rate 1))) (/ (- lower 1))) (* (lw-dirichlet-right-dyadic-cost rate height lower upper) error))))
  :hints (("Goal"
           :use (lw-dirichlet-right-dyadic-mass-bound
                 (:instance lw-reciprocal-square-tail-bound (count (- upper 1)) (start (- lower 1)))
                 (:instance lw-drdm-multiply-order (a (lw-reciprocal-square-tail (- upper 1) (- lower 1))) (b (/ (- lower 1))) (factor (* 64 (/ (- rate 1)) (/ (- rate 1)))))
                 (:instance lw-reciprocal-positive (value (- rate 1))))
           :in-theory (theory 'lw-drdm-arithmetic)
           :nonlinearp t
           :do-not-induct t))
  :rule-classes nil)
