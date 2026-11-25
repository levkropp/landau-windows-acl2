(in-package "ACL2")

(include-book "complex-kernel-agreement")

; A damping-aware multiplication law. The coefficient of the left
; evaluation error is one, using the actual damped sampler's unit disk.
; The right argument's magnitude cap enters only an auxiliary precision.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-exp-value lw-complex-exp-cap lw-complex-l1
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-lipschitz-cap
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-disk-enlarge lw-disk-enlarge lw-disk-gap-error lw-complex-norm-square
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract
                 lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-dpp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-dpp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-dpp-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-dpp-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-dpp-times-negative (a b) (b a)))
                         :in-theory (disable lw-dpp-times-negative)))))
(local (defthm lw-dpp-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-dpp-double
         (equal (+ a a) (* 2 a))
         :hints (("Goal" :cases ((acl2-numberp a))))))
(local (defthm lw-dpp-add-double
         (equal (+ a (+ a b)) (+ (* 2 a) b))
         :hints (("Goal" :cases ((acl2-numberp a))))))
(local (defthm lw-dpp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dpp-product-difference
         (equal
          (lw-complex-sub (lw-complex-mul a d) (lw-complex-mul b r))
          (lw-complex-add (lw-complex-mul (lw-complex-sub a b) d)
                          (lw-complex-mul b (lw-complex-sub d r))))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-mul)))
         :rule-classes nil))

(local (defthm lw-dpp-product-bound
         (implies
          (and (lw-complex-diskp (lw-complex-sub a b) left-error)
               (lw-complex-diskp d 1) (lw-complex-diskp b cap)
               (lw-complex-diskp (lw-complex-sub d r) right-error))
          (lw-complex-diskp (lw-complex-sub (lw-complex-mul a d) (lw-complex-mul b r))
                            (+ left-error (* cap right-error))))
         :hints (("Goal"
                  :use (lw-dpp-product-difference
                        (:instance lw-complex-mul-disk (left (lw-complex-sub a b)) (right d)
                          (radius left-error) (other-radius 1))
                        (:instance lw-complex-mul-disk (left b) (right (lw-complex-sub d r))
                          (radius cap) (other-radius right-error))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-mul (lw-complex-sub a b) d))
                          (right (lw-complex-mul b (lw-complex-sub d r)))
                          (radius left-error) (other-radius (* cap right-error))))
                  :in-theory (disable lw-complex-mul-disk lw-complex-add-disk)
                  :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-dpp-three-comparisons
         (implies
          (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (lw-complex-diskp (lw-complex-sub a b) first)
               (lw-complex-diskp (lw-complex-sub b c) second)
               (lw-complex-diskp (lw-complex-sub c d) third))
          (lw-complex-diskp (lw-complex-sub a d) (+ first second third)))
         :hints (("Goal"
                  :use ((:instance lw-complex-difference-triangle
                          (left a) (middle b) (right c) (radius first) (other-radius second))
                        (:instance lw-complex-difference-triangle
                          (left a) (middle c) (right d) (radius (+ first second)) (other-radius third)))
                  :in-theory (disable lw-complex-difference-triangle) :do-not-induct t))
         :rule-classes nil))

(defun lw-complex-damped-product (left value angle left-error negative-error phase-error)
  (lw-complex-mul (lw-complex-exp-value left left-error)
                  (lw-damped-phase-sample value angle negative-error phase-error)))

(defun lw-complex-damped-product-factor (left value angle)
  (+ 4 (* 2 (lw-complex-exp-cap left)) (lw-complex-exp-cap (cons (- value) angle))))

(defthm lw-complex-damped-product-rational
  (implies (and (lw-complexp left) (rationalp value) (<= 0 value) (rationalp angle)
                (rationalp left-error) (< 0 left-error))
           (lw-complexp (lw-complex-damped-product left value angle left-error negative-error phase-error)))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-value-rational (point left) (error left-error))
                 lw-damped-phase-sample-rational)
           :in-theory (disable lw-complex-exp-value-rational lw-damped-phase-sample-rational)
           :do-not-induct t)))

(defthm lw-complex-damped-product-factor-valid
  (implies (and (lw-complexp left) (rationalp value) (rationalp angle))
           (and (rationalp (lw-complex-damped-product-factor left value angle))
                (<= 1 (lw-complex-damped-product-factor left value angle))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-cap-valid (point left))
                 (:instance lw-complex-exp-cap-valid (point (cons (- value) angle))))
           :in-theory (disable lw-complex-exp-cap-valid) :do-not-induct t)))

(local (in-theory (disable lw-complex-damped-product lw-complex-damped-product-factor)))

(defthm lw-complex-damped-product-auxiliary
  (implies
   (and (lw-complexp left) (rationalp value) (<= 0 value) (rationalp angle)
        (rationalp left-error) (< 0 left-error) (rationalp negative-error) (< 0 negative-error)
        (rationalp phase-error) (< 0 phase-error) (rationalp complex-error) (< 0 complex-error)
        (rationalp auxiliary-error) (< 0 auxiliary-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-damped-product left value angle left-error negative-error phase-error)
     (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error))
    (+ left-error (* (lw-complex-exp-cap left) (+ negative-error phase-error)) complex-error
       (* (lw-complex-damped-product-factor left value angle) auxiliary-error))))
  :hints (("Goal"
           :use
           (lw-complex-damped-product-rational
            lw-damped-phase-sample-rational lw-damped-phase-sample-unit
            (:instance lw-complex-exp-value-rational (point left) (error auxiliary-error))
            (:instance lw-complex-exp-value-rational (point (cons (- value) angle)) (error auxiliary-error))
            (:instance lw-complex-exp-value-rational
              (point (lw-complex-add left (cons (- value) angle))) (error auxiliary-error))
            (:instance lw-complex-exp-value-rational
              (point (lw-complex-add left (cons (- value) angle))) (error complex-error))
            (:instance lw-complex-exp-value-cauchy
              (point left) (left-error left-error) (right-error auxiliary-error))
            (:instance lw-complex-exp-value-cap (point left) (error auxiliary-error))
            (:instance lw-complex-exp-kernel-agreement (complex-error auxiliary-error))
            (:instance lw-dpp-product-bound
              (a (lw-complex-exp-value left left-error))
              (b (lw-complex-exp-value left auxiliary-error))
              (d (lw-damped-phase-sample value angle negative-error phase-error))
              (r (lw-complex-exp-value (cons (- value) angle) auxiliary-error))
              (left-error (+ left-error auxiliary-error)) (cap (lw-complex-exp-cap left))
              (right-error (+ negative-error phase-error auxiliary-error)))
            (:instance lw-complex-exp-value-multiplication
              (right (cons (- value) angle))
              (left-error auxiliary-error) (right-error auxiliary-error) (sum-error auxiliary-error))
            (:instance lw-complex-exp-value-cauchy
              (point (lw-complex-add left (cons (- value) angle)))
              (left-error auxiliary-error) (right-error complex-error))
            (:instance lw-dpp-three-comparisons
              (a (lw-complex-damped-product left value angle left-error negative-error phase-error))
              (b (lw-complex-mul (lw-complex-exp-value left auxiliary-error)
                                 (lw-complex-exp-value (cons (- value) angle) auxiliary-error)))
              (c (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) auxiliary-error))
              (d (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error))
              (first (+ left-error auxiliary-error
                        (* (lw-complex-exp-cap left) (+ negative-error phase-error auxiliary-error))))
              (second (+ (* (lw-complex-exp-cap (cons (- value) angle)) auxiliary-error)
                         (* (lw-complex-exp-cap left) auxiliary-error) (* 2 auxiliary-error)))
              (third (+ auxiliary-error complex-error))))
           :in-theory
           (e/d (lw-complex-damped-product lw-complex-damped-product-factor)
                (lw-complex-damped-product-rational lw-damped-phase-sample-rational lw-damped-phase-sample-unit
                 lw-complex-exp-value-rational lw-complex-exp-value-cauchy lw-complex-exp-value-cap
                 lw-complex-exp-kernel-agreement lw-complex-exp-value-multiplication))
           :nonlinearp nil :do-not-induct t)))

(defun lw-complex-damped-product-bound (left left-error negative-error phase-error complex-error)
  (+ left-error (* (lw-complex-exp-cap left) (+ negative-error phase-error)) complex-error))

(defun lw-complex-damped-product-precision (left value angle margin)
  (/ margin (+ 1 (lw-complex-damped-product-factor left value angle))))

(local (defthm lw-dpp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-damped-product-bound-valid
  (implies (and (lw-complexp left) (rationalp left-error) (< 0 left-error)
                (rationalp negative-error) (< 0 negative-error) (rationalp phase-error) (< 0 phase-error)
                (rationalp complex-error) (< 0 complex-error))
           (and (rationalp (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error))
                (< 0 (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-cap-valid (point left))
                 (:instance lw-dpp-positive-product
                   (a (lw-complex-exp-cap left)) (b (+ negative-error phase-error))))
           :in-theory (disable lw-complex-exp-cap-valid) :nonlinearp nil :do-not-induct t)))

(local (defthm lw-dpp-precision-scalar
         (implies (and (rationalp factor) (<= 0 factor) (rationalp margin) (< 0 margin))
                  (and (rationalp (/ margin (+ 1 factor))) (< 0 (/ margin (+ 1 factor)))
                       (<= (* factor (/ margin (+ 1 factor))) margin)))
         :hints (("Goal"
                  :use ((:instance lw-positive-division-bound
                          (numerator (* factor margin)) (divisor (+ 1 factor)) (bound margin)))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-damped-product-precision-valid
  (implies (and (lw-complexp left) (rationalp value) (rationalp angle) (rationalp margin) (< 0 margin))
           (and (rationalp (lw-complex-damped-product-precision left value angle margin))
                (< 0 (lw-complex-damped-product-precision left value angle margin))
                (<= (* (lw-complex-damped-product-factor left value angle)
                       (lw-complex-damped-product-precision left value angle margin)) margin)))
  :hints (("Goal"
           :use (lw-complex-damped-product-factor-valid
                 (:instance lw-dpp-precision-scalar (factor (lw-complex-damped-product-factor left value angle))))
           :in-theory (disable lw-complex-damped-product-factor-valid)
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-complex-damped-product-bound lw-complex-damped-product-precision)))

(defthm lw-complex-damped-product-with-margin
  (implies
   (and (lw-complexp left) (rationalp value) (<= 0 value) (rationalp angle)
        (rationalp left-error) (< 0 left-error) (rationalp negative-error) (< 0 negative-error)
        (rationalp phase-error) (< 0 phase-error) (rationalp complex-error) (< 0 complex-error)
        (rationalp margin) (< 0 margin))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-damped-product left value angle left-error negative-error phase-error)
     (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error))
    (+ (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error) margin)))
  :hints (("Goal"
           :use (lw-complex-damped-product-precision-valid lw-complex-damped-product-bound-valid
                 (:instance lw-complex-damped-product-auxiliary
                   (auxiliary-error (lw-complex-damped-product-precision left value angle margin)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-damped-product left value angle left-error negative-error phase-error)
                     (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error)))
                   (radius (+ (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error)
                              (* (lw-complex-damped-product-factor left value angle)
                                 (lw-complex-damped-product-precision left value angle margin))))
                   (cap (+ (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error) margin))))
           :in-theory
           (e/d (lw-complex-damped-product-bound)
                (lw-complex-damped-product-precision-valid lw-complex-damped-product-bound-valid
                 lw-complex-damped-product-auxiliary))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-dpp-sum-complex
         (implies (and (lw-complexp left) (rationalp value) (rationalp angle))
                  (lw-complexp (lw-complex-add left (cons (- value) angle))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))
(local (defthm lw-dpp-sub-complex
         (implies (and (lw-complexp a) (lw-complexp b)) (lw-complexp (lw-complex-sub a b)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(defthm lw-complex-damped-product-agreement
  (implies
   (and (lw-complexp left) (rationalp value) (<= 0 value) (rationalp angle)
        (rationalp left-error) (< 0 left-error) (rationalp negative-error) (< 0 negative-error)
        (rationalp phase-error) (< 0 phase-error) (rationalp complex-error) (< 0 complex-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-damped-product left value angle left-error negative-error phase-error)
     (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error))
    (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error)))
  :hints (("Goal"
           :cases ((lw-complex-diskp
                    (lw-complex-sub
                     (lw-complex-damped-product left value angle left-error negative-error phase-error)
                     (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error))
                    (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error)))
           :use (lw-complex-damped-product-rational lw-complex-damped-product-bound-valid
                 (:instance lw-complex-exp-value-rational
                   (point (lw-complex-add left (cons (- value) angle))) (error complex-error))
                 (:instance lw-complex-disk-gap-excludes
                   (point (lw-complex-sub
                     (lw-complex-damped-product left value angle left-error negative-error phase-error)
                     (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error)))
                   (radius (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error)))
                 (:instance lw-complex-damped-product-with-margin
                   (margin (lw-disk-gap-error
                     (lw-complex-norm-square
                       (lw-complex-sub
                        (lw-complex-damped-product left value angle left-error negative-error phase-error)
                        (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) complex-error)))
                     (lw-complex-damped-product-bound left left-error negative-error phase-error complex-error)))))
           :in-theory (disable lw-complex-damped-product-rational lw-complex-damped-product-bound-valid
                               lw-complex-exp-value-rational lw-complex-disk-gap-excludes
                               lw-complex-damped-product-with-margin)
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-dpp-real-product
         (equal (lw-complex-mul (cons scalar 0) point) (lw-complex-scale scalar point))
         :hints (("Goal" :in-theory (enable lw-complex-mul lw-complex-scale)))))

(defthm lw-exp-times-damped-phase-agreement
  (implies
   (and (rationalp exponent) (<= 0 exponent) (rationalp value) (<= 0 value) (rationalp angle)
        (rationalp exp-error) (< 0 exp-error) (rationalp negative-error) (< 0 negative-error)
        (rationalp phase-error) (< 0 phase-error) (rationalp complex-error) (< 0 complex-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-scale (car (lw-exp-bounds exponent exp-error))
                       (lw-damped-phase-sample value angle negative-error phase-error))
     (lw-complex-exp-value (cons (- exponent value) angle) complex-error))
    (+ exp-error (* (lw-exp-lipschitz-cap exponent) (+ negative-error phase-error)) complex-error)))
  :hints (("Goal"
           :use ((:instance lw-complex-damped-product-agreement (left (cons exponent 0)) (left-error exp-error)))
           :in-theory
           (e/d (lw-complex-damped-product lw-complex-damped-product-bound
                 lw-complex-add lw-complex-exp-cap lw-complex-l1 lw-exp-lipschitz-cap)
                (lw-complex-damped-product-agreement))
           :nonlinearp nil :do-not-induct t)))
