(in-package "ACL2")

(include-book "cauchy-resolvents")

; Sample the actual rational function, compare with its computed Taylor
; polynomial, and recover its coefficients without an infinite-series rule.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-conjugate lw-complex-norm-square lw-complex-diskp lw-diskp
                 lw-complex-reciprocal lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-coefficient-at lw-complex-l1
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-cauchy-moment-count lw-cauchy-orbit-moment
                 lw-cauchy-moment-expansion lw-cauchy-correlation-expansion lw-cauchy-residual-expansion
                 lw-complex-correlation-sum lw-complex-signed-power lw-complex-geometric-average
                 lw-complex-geometric-sum lw-cauchy-evaluation-sum lw-cauchy-polynomial-average
                 lw-cauchy-evaluation-sum-expansion lw-cauchy-evaluation-sum-first
                 lw-complex-conjugate-power lw-complex-power-power lw-complex-power-add
                 lw-cauchy-polynomial-average-moments lw-cauchy-scaled-expansion
                 lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-resolvent-value lw-resolvent-coefficients lw-resolvent-polynomial-evaluation
                 lw-resolvent-truncation-count lw-geometric-index lw-geometric-threshold)))

(local (defthm lw-rs-zero-times (equal (* 0 a) 0)))
(local (defthm lw-rs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-rs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-rs-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defun lw-rs-countdown (count)
         (declare (xargs :measure (nfix count)))
         (if (zp count) 0 (lw-rs-countdown (- count 1)))))

(defthm lw-complex-sub-products-right
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp weight))
           (equal (lw-complex-sub (lw-complex-mul a weight) (lw-complex-mul b weight))
                  (lw-complex-mul (lw-complex-sub a b) weight)))
  :hints (("Goal" :use ((:instance lw-complex-mul-subtract
                          (a weight) (b a) (c b)))
                  :in-theory (disable lw-complex-mul-subtract))))

(defun lw-cauchy-resolvent-sum (ratio point target count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (lw-resolvent-value ratio (lw-complex-power point (- count 1)))
      (lw-complex-conjugate
       (lw-complex-power (lw-complex-power point (- count 1)) target)))
     (lw-cauchy-resolvent-sum ratio point target (- count 1)))))

(defthm lw-cauchy-resolvent-sum-rational
  (implies (and (lw-complexp ratio) (lw-complexp point) (natp target) (natp count))
           (lw-complexp (lw-cauchy-resolvent-sum ratio point target count))))

(local (in-theory (disable lw-cauchy-resolvent-sum)))

(defthm lw-cauchy-resolvent-sum-truncation
  (implies (and (lw-complex-diskp ratio radius) (< radius 1)
                (lw-complex-diskp point 1) (natp target) (natp terms) (natp count)
                (rationalp error) (< 0 error)
                (<= (lw-resolvent-truncation-count radius error) terms))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-resolvent-sum ratio point target count)
             (lw-cauchy-evaluation-sum (lw-resolvent-coefficients ratio 0 terms)
                                       point target 0 count))
            (* count error)))
  :hints (("Goal" :induct (lw-rs-countdown count)
                  :in-theory (e/d (lw-cauchy-resolvent-sum lw-cauchy-evaluation-sum)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes
                                   lw-complex-mul-commutative lw-complex-sub-add-first)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-unit-power (index (- count 1)))
                        (:instance lw-resolvent-computed-polynomial-error
                          (point (lw-complex-power point (- count 1))) (count terms))
                        (:instance lw-cauchy-unit-weight-bound (index (- count 1)))
                        (:instance lw-complex-mul-disk
                          (left (lw-complex-sub
                                 (lw-resolvent-value ratio (lw-complex-power point (- count 1)))
                                 (lw-complex-polynomial
                                  (lw-resolvent-coefficients ratio 0 terms)
                                  (lw-complex-power point (- count 1)) 0)))
                          (radius error)
                          (right (lw-complex-conjugate
                                  (lw-complex-power (lw-complex-power point (- count 1)) target)))
                          (other-radius 1))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-mul
                                 (lw-complex-sub
                                  (lw-resolvent-value ratio (lw-complex-power point (- count 1)))
                                  (lw-complex-polynomial
                                   (lw-resolvent-coefficients ratio 0 terms)
                                   (lw-complex-power point (- count 1)) 0))
                                 (lw-complex-conjugate
                                  (lw-complex-power (lw-complex-power point (- count 1)) target))))
                          (radius error)
                          (right (lw-complex-sub
                                  (lw-cauchy-resolvent-sum ratio point target (- count 1))
                                  (lw-cauchy-evaluation-sum (lw-resolvent-coefficients ratio 0 terms)
                                                            point target 0 (- count 1))))
                          (other-radius (* (- count 1) error))))
                 :in-theory (disable lw-cauchy-resolvent-sum lw-cauchy-evaluation-sum
                                     lw-complex-add-commutative lw-complex-add-left-commutes
                                     lw-complex-mul-commutative lw-complex-sub-add-first
                                     lw-complex-mul-disk lw-complex-add-disk
                                     lw-resolvent-computed-polynomial-error
                                     lw-cauchy-unit-weight-bound)))))

(defthm lw-complex-sub-scales
  (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
           (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                  (lw-complex-scale factor (lw-complex-sub a b))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale))))

(defun lw-cauchy-resolvent-average (ratio degree target count)
  (lw-complex-scale
   (/ count) (lw-cauchy-resolvent-sum ratio (lw-cauchy-orbit-rotation degree) target count)))

(defthm lw-cauchy-resolvent-average-rational
  (implies (and (lw-complexp ratio) (natp degree) (natp target) (posp count))
           (lw-complexp (lw-cauchy-resolvent-average ratio degree target count))))

(defthm lw-cauchy-polynomial-average-rational
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (natp target) (posp count))
           (lw-complexp (lw-cauchy-polynomial-average coefficients degree target count)))
  :hints (("Goal" :in-theory (enable lw-cauchy-polynomial-average))))

(local (defthm lw-rs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* (/ divisor) (* divisor coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x (/ divisor)) (y divisor) (z coefficient))
                              (:instance commutativity-of-* (x (/ divisor)) (y divisor))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defthm lw-cauchy-resolvent-average-truncation
  (implies (and (lw-complex-diskp ratio radius) (< radius 1)
                (natp degree) (natp target) (natp terms) (posp count)
                (rationalp error) (< 0 error)
                (<= (lw-resolvent-truncation-count radius error) terms))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-resolvent-average ratio degree target count)
             (lw-cauchy-polynomial-average (lw-resolvent-coefficients ratio 0 terms)
                                            degree target count)) error))
  :hints (("Goal" :use (lw-cauchy-orbit-data
                        (:instance lw-rs-inverse-factor (divisor count) (coefficient error))
                        (:instance lw-cauchy-resolvent-sum-truncation
                          (point (lw-cauchy-orbit-rotation degree)))
                        (:instance lw-complex-scale-disk
                          (point (lw-complex-sub
                                  (lw-cauchy-resolvent-sum ratio (lw-cauchy-orbit-rotation degree) target count)
                                  (lw-cauchy-evaluation-sum (lw-resolvent-coefficients ratio 0 terms)
                                                            (lw-cauchy-orbit-rotation degree) target 0 count)))
                          (radius (* count error)) (factor (/ count))))
                  :in-theory (e/d (lw-cauchy-polynomial-average)
                                  (lw-cauchy-resolvent-sum-truncation lw-complex-scale-disk
                                   lw-complex-scale-add lw-rs-inverse-factor)))))

(defun lw-resolvent-cauchy-order (radius target error)
  (max (+ 1 (nfix target)) (lw-resolvent-truncation-count radius (/ error 2))))

(defthm lw-resolvent-cauchy-order-data
  (implies (natp target)
           (and (natp (lw-resolvent-cauchy-order radius target error))
                (< 0 (lw-resolvent-cauchy-order radius target error))
                (natp (- (lw-resolvent-cauchy-order radius target error) 1))
                (< target (lw-resolvent-cauchy-order radius target error))
                (<= (lw-resolvent-truncation-count radius (/ error 2))
                    (lw-resolvent-cauchy-order radius target error))))
  :hints (("Goal" :use ((:instance lw-resolvent-truncation-count-natural (error (/ error 2)))))))

(defun lw-resolvent-cauchy-count (ratio radius target error)
  (let ((terms (lw-resolvent-cauchy-order radius target error)))
    (lw-cauchy-coefficient-count (lw-resolvent-coefficients ratio 0 terms) (- terms 1) (/ error 2))))

(defthm lw-resolvent-cauchy-count-natural
  (and (natp (lw-resolvent-cauchy-count ratio radius target error))
       (< 0 (lw-resolvent-cauchy-count ratio radius target error)))
  :rule-classes (:rewrite :type-prescription))

(local (in-theory (disable lw-cauchy-resolvent-average lw-resolvent-cauchy-order
                           lw-complex-coefficient-mass)))

(defthm lw-cauchy-computed-resolvent-coefficient
  (implies (and (lw-complex-diskp ratio radius) (< radius 1)
                (natp target) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-resolvent-average
              ratio (- (lw-resolvent-cauchy-order radius target error) 1) target
              (lw-resolvent-cauchy-count ratio radius target error))
             (lw-complex-power ratio target)) error))
  :hints (("Goal" :use (lw-resolvent-cauchy-order-data
                        (:instance lw-resolvent-coefficients-valid
                          (offset 0) (count (lw-resolvent-cauchy-order radius target error)))
                        (:instance lw-resolvent-coefficient-nth
                          (offset 0) (index target) (count (lw-resolvent-cauchy-order radius target error)))
                        (:instance lw-cauchy-resolvent-average-truncation
                          (degree (- (lw-resolvent-cauchy-order radius target error) 1))
                          (terms (lw-resolvent-cauchy-order radius target error))
                          (count (lw-resolvent-cauchy-count ratio radius target error))
                          (error (/ error 2)))
                        (:instance lw-cauchy-computed-coefficient-recovery
                          (coefficients (lw-resolvent-coefficients ratio 0
                                                                  (lw-resolvent-cauchy-order radius target error)))
                          (degree (- (lw-resolvent-cauchy-order radius target error) 1))
                          (error (/ error 2)))
                        (:instance lw-complex-difference-triangle
                          (left (lw-cauchy-resolvent-average
                                 ratio (- (lw-resolvent-cauchy-order radius target error) 1) target
                                 (lw-resolvent-cauchy-count ratio radius target error)))
                          (middle (lw-cauchy-polynomial-average
                                   (lw-resolvent-coefficients ratio 0
                                                             (lw-resolvent-cauchy-order radius target error))
                                   (- (lw-resolvent-cauchy-order radius target error) 1) target
                                   (lw-resolvent-cauchy-count ratio radius target error)))
                          (right (lw-complex-power ratio target))
                          (radius (/ error 2)) (other-radius (/ error 2))))
                  :in-theory (disable lw-resolvent-cauchy-order-data
                                      lw-resolvent-coefficients-valid lw-resolvent-coefficient-nth
                                      lw-cauchy-resolvent-average-truncation
                                      lw-cauchy-computed-coefficient-recovery
                                      lw-complex-difference-triangle))))

; Exact evaluations exercise the complex truncation and weighting signs.
(assert-event
 (and (equal (lw-resolvent-value (cons 1/2 0) (cons 0 1)) (cons 4/5 2/5))
      (equal (lw-complex-polynomial
              (lw-resolvent-coefficients (cons 1/2 0) 0 3) (cons 0 1) 0)
             (cons 3/4 1/2))
      (equal (lw-cauchy-resolvent-average (cons 1/2 0) 1 1 2)
             (cons 119886/61685 -832/61685))))
