(in-package "ACL2")

(include-book "dirichlet-term-transport")

; Cubic Dirichlet decay from three certified logarithmic rate shifts.
; This right half-plane supplies a summable weighted majorant at the
; Landau anchor; continuation to the zero region remains separate.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-dcd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dcd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dcd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dcd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dcd-times-negative (a b) (b a)))
                 :in-theory (disable lw-dcd-times-negative)))))

(local (defthm lw-dcd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dcd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dcd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dcd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dcd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dcd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dcd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dcd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dcd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dcd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dcd-left-commutes)))))

(local (defthm lw-dcd-point-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                       (rationalp start) (<= 0 start) (rationalp index) (<= start index))
                  (and
                   (lw-complexp (cons start 0))
                   (lw-complexp (lw-complex-scale start (lw-complex-laplace-point rate height)))
                   (<= 0 (* rate start))
                   (<= 0 (* (+ rate (abs height)) index))
                   (<= (lw-complex-l1 (cons start 0)) index)
                   (<= (lw-complex-l1 (lw-complex-scale start (lw-complex-laplace-point rate height)))
                       (* (+ rate (abs height)) index))
                   (equal (lw-complex-add (cons start 0)
                             (lw-complex-scale start (lw-complex-laplace-point rate height)))
                          (lw-complex-scale start (lw-complex-laplace-point (- rate 1) height)))))
         :hints (("Goal" :cases ((<= 0 height))
                         :in-theory (enable lw-complexp lw-complex-add lw-complex-scale
                                            lw-complex-laplace-point lw-complex-l1)
                         :nonlinearp t))))

(local (defthm lw-dcd-cap-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index))
                  (and (rationalp (lw-complex-log-ramp-cap rate height index))
                       (<= 4 (lw-complex-log-ramp-cap rate height index))
                       (rationalp (lw-exp-lipschitz-cap index))
                       (<= 1 (lw-exp-lipschitz-cap index))))
         :hints (("Goal"
                  :use ((:instance lw-dcd-point-data (start 0))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap index))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index)))
                        (:instance lw-exp-lipschitz-cap-valid (cap index)))
                  :in-theory (e/d (lw-complex-log-ramp-cap)
                                  (lw-dcd-point-data lw-complex-exp-uniform-cap-data lw-exp-lipschitz-cap-valid))
                  :do-not-induct t))))

(local (in-theory (disable lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (defthm lw-dcd-recover-scaled
 (equal (lw-complex-sub a (lw-complex-sub a (lw-complex-scale index b)))
        (lw-complex-scale index b))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-dcd-inverse-scale
 (implies (and (lw-complexp b) (rationalp index) (< 0 index))
  (equal (lw-complex-scale (/ index) (lw-complex-scale index b)) b))
 :hints (("Goal" :use ((:instance inverse-of-* (x index)))
                 :in-theory (e/d (lw-complexp lw-complex-scale) (inverse-of-*))
                 :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dcd-inverse-step
 (implies
  (and (lw-complexp b) (rationalp index) (< 0 index)
       (lw-complex-diskp a cap)
       (lw-complex-diskp (lw-complex-sub a (lw-complex-scale index b)) error))
  (lw-complex-diskp b (* (/ index) (+ cap error))))
 :hints (("Goal"
  :use (lw-dcd-inverse-scale
        (:instance lw-complex-sub-disk
         (left a) (right (lw-complex-sub a (lw-complex-scale index b))) (radius cap) (other-radius error))
        (:instance lw-complex-scale-disk (point (lw-complex-scale index b)) (radius (+ cap error)) (factor (/ index))))
  :in-theory (disable lw-complex-sub-disk lw-complex-scale-disk)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dcd-cubic-weight-scalar
 (implies
  (and (rationalp index) (< 1 index) (rationalp weight) (<= 0 weight) (<= weight index)
       (rationalp r0) (<= 0 r0) (rationalp r1) (<= 0 r1) (rationalp r2) (<= 0 r2))
  (<= (* weight (/ index) (+ (* (/ index) (+ (* (/ index) (+ 2 r2)) r1)) r0))
      (+ (* 2 (/ index) (/ index)) r0 r1 r2)))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound (numerator weight) (divisor index) (bound 1))
        (:instance lw-reciprocal-antitone (left 1) (right index))
        (:instance lw-dcd-multiply-order (a (* weight (/ index))) (b 1)
         (factor (+ (* (/ index) (+ (* (/ index) (+ 2 r2)) r1)) r0)))
        (:instance lw-dcd-multiply-order (a (/ index)) (b 1) (factor r1))
        (:instance lw-dcd-multiply-order (a (/ index)) (b 1) (factor (/ index)))
        (:instance lw-dcd-multiply-order (a (* (/ index) (/ index))) (b 1) (factor r2)))
  :in-theory (disable lw-reciprocal-antitone)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-dirichlet-cubic-node-cost (rate height index)
 (+ (lw-complex-log-ramp-cap rate height index)
    (lw-complex-log-ramp-cap (- rate 1) height index)
    (lw-complex-log-ramp-cap (- rate 2) height index) 12))

(local (in-theory (disable lw-dirichlet-cubic-node-cost)))

(defthm lw-dirichlet-cubic-node-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp index) (< 1 index))
  (and (rationalp (lw-dirichlet-cubic-node-cost rate height index)) (<= 0 (lw-dirichlet-cubic-node-cost rate height index))))
 :hints (("Goal"
  :use (lw-dcd-cap-data (:instance lw-dcd-cap-data (rate (- rate 1))) (:instance lw-dcd-cap-data (rate (- rate 2))))
  :in-theory (e/d (lw-dirichlet-cubic-node-cost) (lw-dcd-cap-data))
  :do-not-induct t)))

(local (defthm lw-dcd-cascade
 (implies
  (and (lw-complexp b0) (lw-complexp b1) (lw-complexp b2)
       (rationalp index) (< 1 index)
       (lw-complex-diskp b3 2)
       (lw-complex-diskp (lw-complex-sub b3 (lw-complex-scale index b2)) r2)
       (lw-complex-diskp (lw-complex-sub b2 (lw-complex-scale index b1)) r1)
       (lw-complex-diskp (lw-complex-sub b1 (lw-complex-scale index b0)) r0))
  (lw-complex-diskp b0 (* (/ index) (+ (* (/ index) (+ (* (/ index) (+ 2 r2)) r1)) r0))))
 :hints (("Goal"
  :use ((:instance lw-dcd-inverse-step (a b3) (b b2) (cap 2) (error r2))
        (:instance lw-dcd-inverse-step (a b2) (b b1) (cap (* (/ index) (+ 2 r2))) (error r1))
        (:instance lw-dcd-inverse-step (a b1) (b b0) (cap (* (/ index) (+ (* (/ index) (+ 2 r2)) r1))) (error r0)))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dcd-weighted-cascade
 (implies
  (and (lw-complexp b0) (lw-complexp b1) (lw-complexp b2)
       (rationalp index) (< 1 index)
       (rationalp weight) (<= 0 weight) (<= weight index)
       (lw-complex-diskp b3 2)
       (lw-complex-diskp (lw-complex-sub b3 (lw-complex-scale index b2)) r2)
       (lw-complex-diskp (lw-complex-sub b2 (lw-complex-scale index b1)) r1)
       (lw-complex-diskp (lw-complex-sub b1 (lw-complex-scale index b0)) r0))
  (lw-complex-diskp (lw-complex-scale weight b0)
    (+ (* 2 (/ index) (/ index)) r0 r1 r2)))
 :hints (("Goal"
  :use (lw-dcd-cascade lw-dcd-cubic-weight-scalar
        (:instance lw-complex-scale-disk (point b0) (factor weight) (radius (* (/ index) (+ (* (/ index) (+ (* (/ index) (+ 2 r2)) r1)) r0))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-scale weight b0))
         (radius (* weight (* (/ index) (+ (* (/ index) (+ (* (/ index) (+ 2 r2)) r1)) r0)))) (cap (+ (* 2 (/ index) (/ index)) r0 r1 r2))))
  :in-theory (disable lw-complex-scale-disk)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-cubic-point-bound
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp index) (< 1 index)
       (rationalp log-error) (< 0 log-error) (<= log-error 1)
       (rationalp error) (< 0 error) (<= error 1)
       (rationalp weight) (<= 0 weight) (<= weight index))
  (lw-complex-diskp (lw-complex-scale weight (lw-complex-log-ramp-independent-exp rate height index log-error error))
   (+ (* 2 (/ index) (/ index))
      (* (lw-dirichlet-cubic-node-cost rate height index) error)
      (* 6 (lw-exp-lipschitz-cap index) log-error))))
 :hints (("Goal"
  :use ((:instance lw-dcd-cap-data)
        (:instance lw-dcd-cap-data (rate (- rate 1)))
        (:instance lw-dcd-cap-data (rate (- rate 2)))
        (:instance lw-complex-log-ramp-independent-exp-rational (delta error))
        (:instance lw-complex-log-ramp-independent-exp-rational (rate (- rate 1)) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-rational (rate (- rate 2)) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-normalization (delta error))
        (:instance lw-complex-log-ramp-independent-exp-normalization (rate (- rate 1)) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-normalization (rate (- rate 2)) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-unit-cap (rate (- rate 3)))
        (:instance lw-dcd-weighted-cascade
         (b0 (lw-complex-log-ramp-independent-exp rate height index log-error error)) (b1 (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error error)) (b2 (lw-complex-log-ramp-independent-exp (- rate 2) height index log-error error)) (b3 (lw-complex-log-ramp-independent-exp (- rate 3) height index log-error error))
         (r0 (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) log-error))) (r1 (+ (* (+ (lw-complex-log-ramp-cap (- rate 1) height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) log-error))) (r2 (+ (* (+ (lw-complex-log-ramp-cap (- rate 2) height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) log-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale weight (lw-complex-log-ramp-independent-exp rate height index log-error error)))
         (radius (+ (* 2 (/ index) (/ index)) (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) log-error)) (+ (* (+ (lw-complex-log-ramp-cap (- rate 1) height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) log-error)) (+ (* (+ (lw-complex-log-ramp-cap (- rate 2) height index) 4) error) (* 2 (lw-exp-lipschitz-cap index) log-error))))
         (cap (+ (* 2 (/ index) (/ index))
                 (* (lw-dirichlet-cubic-node-cost rate height index) error)
                 (* 6 (lw-exp-lipschitz-cap index) log-error)))))
  :in-theory (e/d (lw-dirichlet-cubic-node-cost)
    (lw-dcd-cap-data lw-complex-log-ramp-independent-exp-rational
     lw-complex-log-ramp-independent-exp-normalization
     lw-complex-log-ramp-independent-exp-unit-cap))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-dcd-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error)) (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-cubic-term-bound
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (< 1 index) (natp total)
       (rationalp model-error) (< 0 model-error)
       (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-scale (car (lw-mangoldt-bounds index primitive-error)) (lw-complex-log-ramp-independent-exp rate height index (lw-smoothed-ramp-log-error index total model-error) error)) (+ (* 2 (/ index) (/ index)) (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-smoothed-ramp-unit-error total model-error)))))
 :hints (("Goal"
  :use (lw-dcd-unit-data
        lw-dirichlet-cubic-node-cost-valid
        (:instance lw-smoothed-ramp-log-error-adequate (error model-error))
        (:instance lw-mangoldt-lower-coarse (epsilon primitive-error))
        (:instance lw-complex-dirichlet-cubic-point-bound (weight (car (lw-mangoldt-bounds index primitive-error))) (log-error (lw-smoothed-ramp-log-error index total model-error)))
        (:instance lw-dcd-multiply-order (a (* (lw-exp-lipschitz-cap index) (lw-smoothed-ramp-log-error index total model-error))) (b (lw-smoothed-ramp-unit-error total model-error)) (factor 6))
        (:instance lw-complex-disk-enlarge (point (lw-complex-scale (car (lw-mangoldt-bounds index primitive-error)) (lw-complex-log-ramp-independent-exp rate height index (lw-smoothed-ramp-log-error index total model-error) error)))
         (radius (+ (* 2 (/ index) (/ index)) (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-exp-lipschitz-cap index) (lw-smoothed-ramp-log-error index total model-error))))
         (cap (+ (* 2 (/ index) (/ index)) (* (lw-dirichlet-cubic-node-cost rate height index) error) (* 6 (lw-smoothed-ramp-unit-error total model-error))))))
  :in-theory (disable lw-dirichlet-cubic-node-cost-valid lw-smoothed-ramp-log-error-adequate
                      lw-mangoldt-lower-coarse lw-complex-dirichlet-cubic-point-bound)
  :nonlinearp nil :do-not-induct t)))


