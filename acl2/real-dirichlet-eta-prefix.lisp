(in-package "ACL2")

(include-book "real-dirichlet-order")

; Pair consecutive terms in the finite alternating Dirichlet sum.

(local (defthm lw-rdep-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rdep-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rdep-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rdep-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rdep-times-negative (a b) (b a)))
                 :in-theory (disable lw-rdep-times-negative)))))

(local (defthm lw-rdep-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rdep-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rdep-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rdep-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rdep-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rdep-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rdep-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rdep-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdep-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdep-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rdep-left-commutes)))))

(local (deftheory lw-rdep-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-rdep-left-commutes lw-rdep-left-distributes lw-rdep-fold-constants
              lw-rdep-times-negative lw-rdep-negative-times lw-rdep-zero-times
              lw-rdep-minus-one lw-rdep-double-negative lw-rdep-add-cancel lw-rdep-double lw-rdep-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-real-dirichlet-eta-pair (rate count error)
  (lw-complex-sub (lw-dirichlet-sample rate 0 (- (* 2 count) 1) error error) (lw-dirichlet-sample rate 0 (* 2 count) error error)))

(defun lw-real-dirichlet-eta-pairs (rate count error)
  (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) (cons 0 0)
    (lw-complex-add (lw-real-dirichlet-eta-pair rate count error) (lw-real-dirichlet-eta-pairs rate (- count 1) error))))

(defun lw-real-dirichlet-eta-odd-prefix (rate count error)
  (lw-complex-add (lw-dirichlet-sample rate 0 (+ 1 (* 2 count)) error error) (lw-real-dirichlet-eta-pairs rate count error)))

(defthm lw-real-dirichlet-order-gain-data
  (implies (and (rationalp rate) (<= 0 rate) (rationalp limit) (<= 0 limit))
           (and (rationalp (lw-real-dirichlet-damping-gain rate limit))
                (rationalp (lw-real-dirichlet-order-gain rate limit)) (< 0 (lw-real-dirichlet-order-gain rate limit)) (<= (lw-real-dirichlet-damping-gain rate limit) (lw-real-dirichlet-order-gain rate limit))))
  :hints (("Goal"
           :use ((:instance lw-rdep-multiply-order (a 0) (b limit) (factor rate))
                 (:instance lw-complex-exp-uniform-cap-data (argument-cap (* rate limit)))
                 (:instance lw-exp-lipschitz-cap-valid (cap (* rate limit)))
                 (:instance lw-rdep-multiply-order (a 0) (b rate) (factor (lw-exp-lipschitz-cap (* rate limit)))))
           :in-theory (union-theories '(lw-real-dirichlet-order-gain lw-real-dirichlet-damping-gain) (theory 'lw-rdep-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-real-dirichlet-eta-pair-rational
  (implies (and (rationalp rate) (rationalp error) (< 0 error))
           (lw-complexp (lw-real-dirichlet-eta-pair rate count error)))
  :hints (("Goal"
           :use ((:instance lw-dirichlet-sample-rational (height 0) (index (- (* 2 count) 1)) (log-error error) (node-error error))
                 (:instance lw-dirichlet-sample-rational (height 0) (index (* 2 count)) (log-error error) (node-error error))
                 (:instance lw-complex-ring-rational (left (lw-dirichlet-sample rate 0 (- (* 2 count) 1) error error)) (right (lw-dirichlet-sample rate 0 (* 2 count) error error))))
           :in-theory (union-theories '(lw-real-dirichlet-eta-pair) (theory 'lw-rdep-arithmetic))
           :do-not-induct t)))

(defthm lw-real-dirichlet-eta-pairs-rational
  (implies (and (rationalp rate) (rationalp error) (< 0 error))
           (lw-complexp (lw-real-dirichlet-eta-pairs rate count error)))
  :hints (("Goal"
           :induct (lw-real-dirichlet-eta-pairs rate count error)
           :in-theory (union-theories '(lw-real-dirichlet-eta-pairs lw-real-dirichlet-eta-pair-rational lw-complex-ring-rational) (theory 'lw-rdep-arithmetic)))))

(local
 (defthm lw-rdep-eta-pair-lower
   (implies (and (rationalp rate) (< 0 rate) (rationalp limit) (<= (* 2 count) limit)
       (rationalp error) (< 0 error) (<= error 1) (posp count))
            (<= (- (if (equal count 1) (lw-real-dirichlet-first-gap rate) 0) (* (lw-real-dirichlet-order-gain rate limit) error)) (car (lw-real-dirichlet-eta-pair rate count error))))
   :hints (("Goal"
            :cases ((equal count 1))
            :use (lw-real-dirichlet-order-gain-data lw-real-dirichlet-first-pair
                  (:instance lw-real-dirichlet-sample-order (left (- (* 2 count) 1)) (right (* 2 count)))
                  (:instance lw-rdep-multiply-order (a (lw-real-dirichlet-damping-gain rate limit)) (b (lw-real-dirichlet-order-gain rate limit)) (factor error)))
            :in-theory (union-theories '(lw-real-dirichlet-eta-pair lw-complex-sub) (theory 'lw-rdep-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-eta-pairs-lower
  (implies (and (rationalp rate) (< 0 rate) (rationalp limit) (<= (* 2 count) limit)
       (rationalp error) (< 0 error) (<= error 1) (posp count))
           (<= (- (lw-real-dirichlet-first-gap rate) (* count (lw-real-dirichlet-order-gain rate limit) error)) (car (lw-real-dirichlet-eta-pairs rate count error))))
  :hints (("Goal"
           :induct (lw-real-dirichlet-eta-pairs rate count error)
           :in-theory (union-theories '(lw-real-dirichlet-eta-pairs lw-complex-add) (theory 'lw-rdep-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-rdep-eta-pair-lower (:instance lw-rdep-eta-pair-lower (count 1))
                        lw-real-dirichlet-first-gap-positive lw-real-dirichlet-order-gain-data
                        lw-real-dirichlet-eta-pair-rational
                        (:instance lw-real-dirichlet-eta-pair-rational (count 1))
                        (:instance lw-real-dirichlet-eta-pairs-rational (count (- count 1))))
                 :in-theory (union-theories '(lw-complexp lw-real-dirichlet-eta-pairs lw-complex-add)
                                           (theory 'lw-rdep-arithmetic))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-rdep-last-term-lower
   (implies (and (rationalp rate) (<= 0 rate) (rationalp index) (< 1 index)
                 (rationalp limit) (<= index limit) (rationalp error) (< 0 error))
            (and (rationalp (car (lw-dirichlet-sample rate 0 index error error)))
                 (<= (- (* (lw-real-dirichlet-order-gain rate limit) error)) (car (lw-dirichlet-sample rate 0 index error error)))))
   :hints (("Goal"
            :use (lw-real-dirichlet-sample-real-part-bounds lw-real-dirichlet-order-gain-data
                  (:instance lw-log-bounds-interval (value index) (epsilon error))
                  (:instance lw-log-bounds-lower-coarse (value index) (epsilon error))
                  (:instance lw-rdep-multiply-order (a 0) (b (car (lw-log-bounds index error))) (factor rate))
                  (:instance lw-exp-neg-bounds-valid (value (lw-real-dirichlet-damping-argument rate index error)) (epsilon error))
                  (:instance lw-rdep-multiply-order (a (lw-real-dirichlet-damping-gain rate limit)) (b (lw-real-dirichlet-order-gain rate limit)) (factor error)))
            :in-theory (union-theories '(lw-real-dirichlet-damping-argument lw-complex-log-ramp-start lw-intervalp) (theory 'lw-rdep-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-eta-odd-prefix-lower
  (implies (and (rationalp rate) (< 0 rate) (rationalp limit) (<= (* 2 count) limit)
       (rationalp error) (< 0 error) (<= error 1) (posp count) (<= (+ 1 (* 2 count)) limit))
           (<= (- (lw-real-dirichlet-first-gap rate) (* (+ 1 count) (lw-real-dirichlet-order-gain rate limit) error)) (car (lw-real-dirichlet-eta-odd-prefix rate count error))))
  :hints (("Goal"
           :use (lw-real-dirichlet-eta-pairs-lower lw-real-dirichlet-eta-pairs-rational lw-real-dirichlet-order-gain-data lw-real-dirichlet-first-gap-positive
                 (:instance lw-rdep-last-term-lower (index (+ 1 (* 2 count)))))
           :in-theory (union-theories '(lw-real-dirichlet-eta-odd-prefix lw-complex-add lw-complexp) (theory 'lw-rdep-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
