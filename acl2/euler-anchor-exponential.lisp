(in-package "ACL2")

(include-book "complex-log-ramp-independent")

; The exponential identity has a boundary value at rate one.
; No division by rate minus one occurs in this normalization.

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

(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (defthm lw-eae-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eae-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eae-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eae-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))

(local (defthm lw-eae-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eae-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eae-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eae-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eae-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eae-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eae-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eae-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eae-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eae-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eae-left-commutes)))))

(local (defthm lw-eae-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-eae-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-eae-start-data
         (implies (and (rationalp index) (< 1 index) (rationalp delta) (< 0 delta))
                  (and (rationalp (lw-complex-log-ramp-start index delta))
                       (<= 0 (lw-complex-log-ramp-start index delta))
                       (<= (lw-complex-log-ramp-start index delta) index)))
         :hints (("Goal"
                  :use ((:instance lw-log-bounds-interval (value index) (epsilon delta))
                        (:instance lw-log-bounds-lower-coarse (value index) (epsilon delta)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-log-bounds-interval lw-log-bounds-lower-coarse))
                  :do-not-induct t))))

(local (defthm lw-eae-scale-laplace
         (implies (and (rationalp rate) (rationalp height) (rationalp start))
                  (equal (lw-complex-scale start (lw-complex-laplace-point rate height))
                         (cons (- (* rate start)) (- (* height start)))))
         :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-eae-point-data
         (implies (and (rationalp rate) (<= 1 rate) (rationalp height)
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

(local (defthm lw-eae-real-difference-disk
         (implies (and (rationalp a) (rationalp b) (rationalp error) (<= (abs (- a b)) error))
                  (lw-complex-diskp (lw-complex-sub (cons a 0) (cons b 0)) error))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complex-sub lw-complexp lw-diskp)
                         :cases ((<= a b)) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-eae-residual-identity
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (rationalp index))
                  (equal
                   (lw-complex-add (lw-complex-sub c (lw-complex-mul a b))
                     (lw-complex-mul (lw-complex-sub a (cons index 0)) b))
                   (lw-complex-sub c (lw-complex-scale index b))))
         :hints (("Goal" :in-theory
                  (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)))))

(local (defthm lw-eae-residual-disk
         (implies
          (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (rationalp index)
               (lw-complex-diskp b 2)
               (lw-complex-diskp (lw-complex-sub c (lw-complex-mul a b)) radius)
               (lw-complex-diskp (lw-complex-sub a (cons index 0)) real-error))
          (lw-complex-diskp (lw-complex-sub c (lw-complex-scale index b))
                            (+ radius (* 2 real-error))))
         :hints (("Goal"
                  :use ((:instance lw-complex-mul-disk
                          (left (lw-complex-sub a (cons index 0))) (right b)
                          (radius real-error) (other-radius 2))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub c (lw-complex-mul a b)))
                          (right (lw-complex-mul (lw-complex-sub a (cons index 0)) b))
                          (other-radius (* 2 real-error))))
                  :in-theory (disable lw-complex-mul-disk lw-complex-add-disk lw-complex-sub-add-first)))
         :rule-classes nil))

(defthm lw-euler-anchor-exponential-normalization
  (implies
   (and (rationalp rate) (<= 1 rate) (rationalp height) (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error) (<= log-error 1)
        (rationalp delta) (< 0 delta) (<= delta 1))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
      (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error delta)))
    (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error))))
  :hints (("Goal"
           :use ((:instance lw-eae-start-data (delta log-error))
                 (:instance lw-eae-point-data (start (lw-complex-log-ramp-start index log-error)))
                 (:instance lw-exp-log-inverse-error (point index) (log-error log-error) (exp-error delta))
                 (:instance lw-exp-bounds-valid (value (lw-complex-log-ramp-start index log-error)) (epsilon delta))
                 (:instance lw-exp-lipschitz-cap-valid (cap index))
                 (:instance lw-complex-exp-cap-uniform
                   (point (cons (lw-complex-log-ramp-start index log-error) 0)) (argument-cap index))
                 (:instance lw-complex-exp-cap-uniform
                   (point (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                           (lw-complex-laplace-point rate height)))
                   (argument-cap (* (+ rate (abs height)) index)))
                 (:instance lw-complex-exp-value-multiplication
                   (left (cons (lw-complex-log-ramp-start index log-error) 0))
                   (right (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                            (lw-complex-laplace-point rate height)))
                   (left-error delta) (right-error delta) (sum-error delta))
                 (:instance lw-eae-multiply-order
                   (a (+ (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index log-error) 0))
                         (lw-complex-exp-cap
                           (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                             (lw-complex-laplace-point rate height))) 2))
                   (b (lw-complex-log-ramp-cap rate height index)) (factor delta))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-mul
                     (lw-complex-exp-value (cons (lw-complex-log-ramp-start index log-error) 0) delta)
                     (lw-complex-log-ramp-independent-exp rate height index log-error delta)))
                   (right (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta))
                   (radius
                     (+ (* (lw-complex-exp-cap
                             (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                               (lw-complex-laplace-point rate height))) delta)
                        (* (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index log-error) 0)) delta)
                        (* 2 delta))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                     (lw-complex-mul
                       (lw-complex-exp-value (cons (lw-complex-log-ramp-start index log-error) 0) delta)
                       (lw-complex-log-ramp-independent-exp rate height index log-error delta))))
                   (radius
                     (+ (* (lw-complex-exp-cap
                             (lw-complex-scale (lw-complex-log-ramp-start index log-error)
                                               (lw-complex-laplace-point rate height))) delta)
                        (* (lw-complex-exp-cap (cons (lw-complex-log-ramp-start index log-error) 0)) delta)
                        (* 2 delta)))
                   (cap (* (lw-complex-log-ramp-cap rate height index) delta)))
                 (:instance lw-complex-exp-damped-cap
                   (value (* rate (lw-complex-log-ramp-start index log-error)))
                   (angle (- (* height (lw-complex-log-ramp-start index log-error)))) (error delta))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-log-ramp-independent-exp rate height index log-error delta))
                   (radius (+ 1 delta)) (cap 2))
                 (:instance lw-eae-real-difference-disk
                   (a (car (lw-exp-bounds (lw-complex-log-ramp-start index log-error) delta)))
                   (b index) (error (+ (* (lw-exp-lipschitz-cap index) log-error) (* 2 delta))))
                 (:instance lw-eae-residual-disk
                   (a (lw-complex-exp-value (cons (lw-complex-log-ramp-start index log-error) 0) delta))
                   (b (lw-complex-log-ramp-independent-exp rate height index log-error delta))
                   (c (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta))
                   (radius (* (lw-complex-log-ramp-cap rate height index) delta))
                   (real-error (+ (* (lw-exp-lipschitz-cap index) log-error) (* 2 delta))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-log-ramp-independent-exp (- rate 1) height index log-error delta)
                     (lw-complex-scale index (lw-complex-log-ramp-independent-exp rate height index log-error delta))))
                   (radius (+ (* (lw-complex-log-ramp-cap rate height index) delta)
                              (* 2 (+ (* (lw-exp-lipschitz-cap index) log-error) (* 2 delta)))))
                   (cap (+ (* (+ (lw-complex-log-ramp-cap rate height index) 4) delta) (* 2 (lw-exp-lipschitz-cap index) log-error)))))
           :in-theory
           (e/d (lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start lw-intervalp)
                (lw-eae-start-data lw-eae-point-data lw-exp-log-inverse-error lw-exp-bounds-valid
                 lw-exp-lipschitz-cap-valid lw-complex-exp-cap-uniform lw-complex-exp-value-multiplication
                 lw-complex-exp-damped-cap lw-complex-sub-add-first))
           :nonlinearp nil :do-not-induct t)))
