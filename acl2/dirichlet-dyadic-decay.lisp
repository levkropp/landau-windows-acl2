(in-package "ACL2")

(include-book "dirichlet-product")
(include-book "complex-damping-cap")
(include-book "log-growth")

; Polynomial decay in the dyadic block number, valid for every positive
; real part. This supplies an effective, coarse continuation tail.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-neg-bounds-overlap
                 lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-phase-rotation lw-phase-grid lw-phase-value lw-phase-steps
                 lw-complex-phase-cap lw-complex-phase-comparison-steps
                 lw-complex-phase-comparison-amplifier lw-complex-phase-comparison-precision
                 lw-complex-exp-negative-precision lw-complex-damped-phase-budget
                 lw-complex-norm-square lw-disk-gap-error
                 lw-complex-damped-phase-value lw-complex-disk-enlarge lw-disk-enlarge)))

(local (in-theory (disable lw-complex-log-ramp-independent-exp
 lw-complex-log-ramp-start lw-complex-laplace-point lw-log-bounds
 lw-rational-power lw-exp-neg-bounds-overlap lw-log-bounds-overlap)))

(local (defthm lw-ddd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ddd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ddd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ddd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ddd-times-negative (a b) (b a)))
                 :in-theory (disable lw-ddd-times-negative)))))

(local (defthm lw-ddd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ddd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ddd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ddd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ddd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ddd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ddd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ddd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ddd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ddd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ddd-left-commutes)))))

(defthm lw-log-bounds-dyadic-quarter-growth
 (implies (and (rationalp value) (rationalp error) (< 0 error) (<= error 1)
               (natp block) (<= 2 block) (<= (lw-rational-power 2 block) value))
  (<= (* 1/4 block) (car (lw-log-bounds value error))))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-dyadic-growth (epsilon error) (steps (- block 1))))
  :in-theory (disable lw-log-bounds-dyadic-growth)
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-ddd-inverse-square-order
 (implies (and (rationalp lower) (< 0 lower) (rationalp value) (<= lower value))
  (<= (* 2 (/ value) (/ value)) (* 2 (/ lower) (/ lower))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-antitone (left lower) (right value))
        (:instance lw-ddd-multiply-order (a (/ value)) (b (/ lower)) (factor (/ value)))
        (:instance lw-ddd-multiply-order (a (/ value)) (b (/ lower)) (factor (/ lower))))
  :in-theory (disable lw-reciprocal-antitone)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ddd-cancel-equality
 (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
               (equal (* factor a) (* factor b)))
  (equal a b))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ddd-quarter-product-inverse
 (implies (and (rationalp rate) (< 0 rate) (rationalp block) (< 0 block))
  (equal (/ (* 1/4 rate block)) (* 4 (/ rate) (/ block))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x rate)) (:instance inverse-of-* (x block))
        (:instance inverse-of-* (x (* 1/4 rate block)))
        (:instance lw-ddd-cancel-equality
         (factor (* 1/4 rate block)) (a (/ (* 1/4 rate block))) (b (* 4 (/ rate) (/ block)))))
  :in-theory (disable inverse-of-*) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-ddd-negative-argument
 (implies (and (rationalp rate) (rationalp height) (rationalp index)
               (< 1 index) (rationalp error) (< 0 error))
  (equal (lw-complex-log-ramp-independent-exp rate height index error error)
   (lw-complex-exp-value
    (cons (- (* rate (car (lw-log-bounds index error))))
          (- (* height (car (lw-log-bounds index error))))) error)))
 :hints (("Goal" :in-theory (enable lw-complex-log-ramp-independent-exp
   lw-complex-log-ramp-start lw-complex-scale lw-complex-laplace-point lw-complexp)))))

(defthm lw-complex-dirichlet-dyadic-decay
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp index) (< 1 index)
               (rationalp error) (< 0 error) (<= error 1)
               (natp block) (<= 2 block)
               (<= (lw-rational-power 2 block) index))
  (lw-complex-diskp
   (lw-complex-log-ramp-independent-exp rate height index error error)
   (+ (* 32 (/ rate) (/ rate) (/ block) (/ block)) (* 3 error))))
 :hints (("Goal"
  :use ((:instance lw-log-bounds-dyadic-quarter-growth (value index))
        (:instance lw-log-bounds-interval (value index) (epsilon error))
        (:instance lw-ddd-positive-product (a rate) (b (* 1/4 block)))
        (:instance lw-ddd-multiply-order
         (a (* 1/4 block)) (b (car (lw-log-bounds index error))) (factor rate))
        (:instance lw-ddd-inverse-square-order
         (lower (* 1/4 rate block)) (value (* rate (car (lw-log-bounds index error)))))
        lw-ddd-quarter-product-inverse
        (:instance lw-complex-exp-quadratic-damping-cap
         (value (* rate (car (lw-log-bounds index error))))
         (angle (- (* height (car (lw-log-bounds index error))))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-log-ramp-independent-exp rate height index error error))
         (radius (+ (* 2 (/ (* rate (car (lw-log-bounds index error))))
                         (/ (* rate (car (lw-log-bounds index error))))) (* 3 error)))
         (cap (+ (* 32 (/ rate) (/ rate) (/ block) (/ block)) (* 3 error)))))
  :in-theory (e/d (lw-intervalp)
   (lw-log-bounds-dyadic-quarter-growth lw-log-bounds-interval
    lw-complex-exp-quadratic-damping-cap))
  :nonlinearp nil :do-not-induct t)))

