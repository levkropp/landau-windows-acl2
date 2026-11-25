(in-package "ACL2")

(include-book "dirichlet-dyadic-decay")
(include-book "mangoldt-dirichlet-convolution")

; For a rate above one, the harmonic weight leaves a summable dyadic bound.

(local (defthm lw-drbd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-drbd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-drbd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-drbd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-drbd-times-negative (a b) (b a)))
                 :in-theory (disable lw-drbd-times-negative)))))

(local (defthm lw-drbd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-drbd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-drbd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-drbd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-drbd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-drbd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-drbd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-drbd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drbd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-drbd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-drbd-left-commutes)))))

(local (deftheory lw-drbd-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-drbd-left-commutes lw-drbd-left-distributes lw-drbd-fold-constants
              lw-drbd-times-negative lw-drbd-negative-times lw-drbd-zero-times
              lw-drbd-minus-one lw-drbd-double-negative lw-drbd-add-cancel lw-drbd-double lw-drbd-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-dirichlet-right-node-cost (rate height index)
  (+ 7 (lw-complex-log-ramp-cap rate height index) (* 2 (lw-exp-lipschitz-cap index))))

(defun lw-dirichlet-right-block-decay (rate block)
  (* 32 (/ (- rate 1)) (/ (- rate 1)) (/ block) (/ block)))

(defthm lw-dirichlet-right-node-cost-data
  (implies (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index))
           (and (rationalp (lw-complex-log-ramp-cap rate height index)) (rationalp (lw-dirichlet-right-node-cost rate height index)) (< 0 (lw-dirichlet-right-node-cost rate height index))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index)))
                 (:instance lw-complex-exp-uniform-cap-data (argument-cap index))
                 (:instance lw-exp-lipschitz-cap-valid (cap index))
                 (:instance lw-drbd-positive-product (a (+ rate (abs height))) (b index)))
           :in-theory (union-theories '(lw-dirichlet-right-node-cost lw-complex-log-ramp-cap abs) (theory 'lw-drbd-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-drbd-normalization-and-decay
   (implies
    (and (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp index) (< 1 index) (natp block) (<= 2 block)
       (<= (lw-rational-power 2 block) index)
       (rationalp error) (< 0 error) (<= error 1))
    (and (lw-complexp (lw-dirichlet-sample rate height index error error)) (lw-complexp (lw-dirichlet-sample (- rate 1) height index error error))
         (lw-complex-diskp (lw-dirichlet-sample (- rate 1) height index error error) (+ (lw-dirichlet-right-block-decay rate block) (* 3 error)))
         (lw-complex-diskp (lw-complex-sub (lw-dirichlet-sample (- rate 1) height index error error) (lw-complex-scale index (lw-dirichlet-sample rate height index error error))) (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) error)))))
   :hints (("Goal"
            :use ((:instance lw-dirichlet-sample-rational (log-error error) (node-error error))
                  (:instance lw-dirichlet-sample-rational (rate (- rate 1)) (log-error error) (node-error error))
                  (:instance lw-complex-dirichlet-dyadic-decay (rate (- rate 1)))
                  (:instance lw-complex-log-ramp-independent-exp-normalization (log-error error) (delta error)))
            :in-theory (union-theories '(lw-dirichlet-sample lw-dirichlet-right-block-decay) (theory 'lw-drbd-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-dirichlet-right-scaled-sample-bound
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp index) (< 1 index) (natp block) (<= 2 block)
       (<= (lw-rational-power 2 block) index)
       (rationalp error) (< 0 error) (<= error 1))
   (lw-complex-diskp (lw-complex-scale index (lw-dirichlet-sample rate height index error error)) (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height index) error))))
  :hints (("Goal"
           :use (lw-drbd-normalization-and-decay
                 (:instance lw-complex-scale-rational (factor index) (point (lw-dirichlet-sample rate height index error error)))
                 (:instance lw-complex-difference-symmetric (left (lw-dirichlet-sample (- rate 1) height index error error)) (right (lw-complex-scale index (lw-dirichlet-sample rate height index error error))) (radius (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) error))))
                 (:instance lw-complex-sub-zero (point (lw-dirichlet-sample (- rate 1) height index error error)))
                 (:instance lw-complex-sub-zero (point (lw-complex-scale index (lw-dirichlet-sample rate height index error error))))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-scale index (lw-dirichlet-sample rate height index error error))) (middle (lw-dirichlet-sample (- rate 1) height index error error)) (right (cons 0 0))
                   (radius (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) error))) (other-radius (+ (lw-dirichlet-right-block-decay rate block) (* 3 error))))
                 (:instance lw-exp-lipschitz-cap-valid (cap index))
                 lw-dirichlet-right-node-cost-data
                 (:instance lw-complex-disk-enlarge (point (lw-complex-scale index (lw-dirichlet-sample rate height index error error)))
                   (radius (+ (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) error)) (+ (lw-dirichlet-right-block-decay rate block) (* 3 error)))) (cap (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height index) error)))))
           :in-theory (union-theories '(lw-dirichlet-right-node-cost lw-dirichlet-right-block-decay) (theory 'lw-drbd-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-dirichlet-right-block-sample-bound
  (implies
   (and (rationalp rate) (< 1 rate) (rationalp height)
       (rationalp index) (< 1 index) (natp block) (<= 2 block)
       (<= (lw-rational-power 2 block) index)
       (rationalp error) (< 0 error) (<= error 1))
   (lw-complex-diskp (lw-dirichlet-sample rate height index error error) (/ (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height index) error)) index)))
  :hints (("Goal"
           :use (lw-dirichlet-right-scaled-sample-bound
                 (:instance lw-dirichlet-sample-rational (log-error error) (node-error error))
                 (:instance lw-complex-scale-disk (point (lw-complex-scale index (lw-dirichlet-sample rate height index error error))) (radius (+ (lw-dirichlet-right-block-decay rate block) (* (lw-dirichlet-right-node-cost rate height index) error))) (factor (/ index)))
                 (:instance lw-complex-scale-compose (left (/ index)) (right index) (point (lw-dirichlet-sample rate height index error error)))
                 (:instance inverse-of-* (x index))
                 (:instance lw-reciprocal-positive (value index)))
           :in-theory (union-theories '(lw-complex-scale-one abs) (theory 'lw-drbd-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
