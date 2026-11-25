(in-package "ACL2")

(include-book "dirichlet-right-block-decay")

; Every dyadic block has at most as many terms as its first index.

(local (defthm lw-drbm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-drbm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-drbm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-drbm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-drbm-times-negative (a b) (b a)))
                 :in-theory (disable lw-drbm-times-negative)))))

(local (defthm lw-drbm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-drbm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-drbm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-drbm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-drbm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-drbm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-drbm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-drbm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drbm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drbm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-drbm-left-commutes)))))

(local (deftheory lw-drbm-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-drbm-left-commutes lw-drbm-left-distributes lw-drbm-fold-constants
              lw-drbm-times-negative lw-drbm-negative-times lw-drbm-zero-times
              lw-drbm-minus-one lw-drbm-double-negative lw-drbm-add-cancel lw-drbm-double lw-drbm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-dirichlet-sample-mass (rate height start count error)
  (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) 0
    (+ (lw-complex-l1 (lw-dirichlet-sample rate height start error error)) (lw-dirichlet-sample-mass rate height (+ 1 start) (- count 1) error))))

(defun lw-dirichlet-right-range-cost (rate height start count)
  (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) 0
    (+ (* 2 (lw-dirichlet-right-node-cost rate height start)) (lw-dirichlet-right-range-cost rate height (+ 1 start) (- count 1)))))

(defthm lw-complex-disk-l1-upper
  (implies (lw-complex-diskp point radius)
           (<= (lw-complex-l1 point) (* 2 radius)))
  :hints (("Goal"
           :use (lw-complex-disk-data lw-complex-disk-coordinates)
           :in-theory (union-theories '(lw-complex-l1 lw-complexp abs) (theory 'lw-drbm-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-drbm-decay-data
   (implies (and (rationalp rate) (< 1 rate) (natp block) (<= 2 block))
            (and (rationalp (lw-dirichlet-right-block-decay rate block)) (< 0 (lw-dirichlet-right-block-decay rate block)) (rationalp (lw-rational-power 2 block)) (< 0 (lw-rational-power 2 block))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-positive (base 2) (exponent block))
                  (:instance lw-rational-power-rational (base 2) (exponent block))
                  (:instance lw-reciprocal-positive (value (- rate 1)))
                  (:instance lw-reciprocal-positive (value block)))
            :in-theory (union-theories '(lw-dirichlet-right-block-decay) (theory 'lw-drbm-arithmetic))
            :nonlinearp t
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-drbm-node-mass
   (implies (and (rationalp rate) (< 1 rate) (rationalp height)
       (posp start) (< 1 start) (natp count)
       (natp block) (<= 2 block) (<= (lw-rational-power 2 block) start)
       (rationalp error) (< 0 error) (<= error 1))
            (and (rationalp (lw-complex-l1 (lw-dirichlet-sample rate height start error error)))
                 (<= (lw-complex-l1 (lw-dirichlet-sample rate height start error error)) (+ (* 2 (lw-dirichlet-right-block-decay rate block) (/ (lw-rational-power 2 block))) (* 2 (lw-dirichlet-right-node-cost rate height start) error)))))
   :hints (("Goal"
            :use (lw-drbm-decay-data
                  (:instance lw-dirichlet-right-node-cost-data (index start))
                  (:instance lw-dirichlet-right-block-sample-bound (index start))
                  (:instance lw-dirichlet-sample-rational (index start) (log-error error) (node-error error))
                  (:instance lw-complex-l1-bound (point (lw-dirichlet-sample rate height start error error)))
                  (:instance lw-complex-disk-l1-upper
                    (point (lw-dirichlet-sample rate height start error error)) (radius (/ (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height start) error)) start)))
                  (:instance lw-reciprocal-antitone (left (lw-rational-power 2 block)) (right start))
                  (:instance lw-reciprocal-antitone (left 1) (right start))
                  (:instance lw-drbm-multiply-order (a (/ start)) (b (/ (lw-rational-power 2 block))) (factor (* 2 (lw-dirichlet-right-block-decay rate block))))
                  (:instance lw-drbm-multiply-order (a (/ start)) (b 1) (factor (* 2 (lw-dirichlet-right-node-cost rate height start) error)))
                  (:instance lw-drbm-positive-product (a (lw-dirichlet-right-node-cost rate height start)) (b error)))
            :in-theory (theory 'lw-drbm-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-dirichlet-right-range-mass-bound
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
       (posp start) (< 1 start) (natp count)
       (natp block) (<= 2 block) (<= (lw-rational-power 2 block) start)
       (rationalp error) (< 0 error) (<= error 1))
   (and (rationalp (lw-dirichlet-sample-mass rate height start count error)) (rationalp (lw-dirichlet-right-range-cost rate height start count)) (<= 0 (lw-dirichlet-right-range-cost rate height start count))
        (<= (lw-dirichlet-sample-mass rate height start count error) (+ (* 2 count (lw-dirichlet-right-block-decay rate block) (/ (lw-rational-power 2 block))) (* (lw-dirichlet-right-range-cost rate height start count) error)))))
  :hints (("Goal"
           :induct (lw-dirichlet-sample-mass rate height start count error)
           :in-theory (union-theories '(lw-dirichlet-sample-mass lw-dirichlet-right-range-cost) (theory 'lw-drbm-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-drbm-decay-data lw-drbm-node-mass
                       (:instance lw-dirichlet-right-node-cost-data (index start)))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-dirichlet-right-block-mass-bound
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
       (posp start) (< 1 start) (natp count)
       (natp block) (<= 2 block) (<= (lw-rational-power 2 block) start)
       (rationalp error) (< 0 error) (<= error 1) (<= count (lw-rational-power 2 block)))
   (<= (lw-dirichlet-sample-mass rate height start count error) (+ (* 2 (lw-dirichlet-right-block-decay rate block)) (* (lw-dirichlet-right-range-cost rate height start count) error))))
  :hints (("Goal"
           :use (lw-dirichlet-right-range-mass-bound lw-drbm-decay-data
                 (:instance lw-reciprocal-positive (value (lw-rational-power 2 block)))
                 (:instance lw-drbm-multiply-order (a count) (b (lw-rational-power 2 block)) (factor (* 2 (lw-dirichlet-right-block-decay rate block) (/ (lw-rational-power 2 block)))))
                 (:instance lw-drbm-inverse-factor (divisor (lw-rational-power 2 block)) (coefficient (* 2 (lw-dirichlet-right-block-decay rate block)))))
           :in-theory (theory 'lw-drbm-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
