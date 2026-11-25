(in-package "ACL2")

(include-book "dirichlet-series-ratio")
(include-book "mellin-dirichlet-series")

; Normalize the proved zeta-series ratio by the actual Mellin transform
; factors and correction terms. This composes the arithmetic series
; identity with the existing improper Mellin evaluator.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul
 lw-complex-scale lw-complex-diskp lw-diskp lw-complex-reciprocal
 lw-complex-scale-product lw-complex-sub-add lw-complex-sub-add-first lw-complex-sub-add-cancel
 lw-dirichlet-transform lw-dirichlet-transform-value lw-euler-bounds
 lw-complex-dirichlet-series-value lw-complex-zeta-log-quotient-value
 lw-mellin-integral lw-dirichlet-series-ratio-precision
 lw-dirichlet-series-product-left-cap lw-dirichlet-series-product-right-cap)))

(local (defthm lw-mzr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mzr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mzr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mzr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mzr-times-negative (a b) (b a)))
                 :in-theory (disable lw-mzr-times-negative)))))

(local (defthm lw-mzr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mzr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mzr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mzr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mzr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mzr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mzr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mzr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mzr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mzr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mzr-left-commutes)))))

(local (defthm lw-mzr-euler-rational
 (implies (and (rationalp error) (< 0 error)) (rationalp (car (lw-euler-bounds error))))
 :hints (("Goal" :use ((:instance lw-euler-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-euler-bounds-interval))))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-mellin-zeta-ratio-request (rate height error)
 (lw-dirichlet-series-ratio-precision rate height (* 1/2 error)))

(defthm lw-mellin-zeta-ratio-request-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (and (rationalp (lw-mellin-zeta-ratio-request rate height error)) (< 0 (lw-mellin-zeta-ratio-request rate height error)) (<= (lw-mellin-zeta-ratio-request rate height error) 1)
       (<= (* 4 (lw-mellin-zeta-ratio-request rate height error)) (* 1/2 error))))
 :hints (("Goal"
  :use (lw-dirichlet-series-product-caps-valid
        (:instance lw-dirichlet-series-ratio-precision-valid (error (* 1/2 error)))
        (:instance lw-mzr-multiply-order
         (a 4)
         (b (+ (* 4 (lw-dirichlet-series-product-right-cap rate height))
               (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1))))
         (factor (lw-mellin-zeta-ratio-request rate height error))))
  :in-theory (disable lw-dirichlet-series-product-caps-valid lw-dirichlet-series-ratio-precision-valid)
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-zeta-ratio-request)))

(defun lw-mellin-zeta-ratio-value (rate height error)
 (lw-dirichlet-transform rate height (lw-complex-zeta-log-quotient-value rate height (lw-mellin-zeta-ratio-request rate height error)) (car (lw-euler-bounds (lw-mellin-zeta-ratio-request rate height error)))))

(defthm lw-mellin-zeta-ratio-value-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-mellin-zeta-ratio-value rate height error)))
 :hints (("Goal" :use (lw-mellin-zeta-ratio-request-valid)
                 :in-theory (disable lw-mellin-zeta-ratio-request-valid)
                 :do-not-induct t)))

(defthm lw-mellin-zeta-ratio-normalization-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-dirichlet-transform-value rate height (* 4 (lw-mellin-zeta-ratio-request rate height error))) (lw-mellin-zeta-ratio-value rate height error))
   (* 1/2 error)))
 :hints (("Goal"
  :use (lw-mellin-zeta-ratio-request-valid
        (:instance lw-complex-dirichlet-series-ratio-computed-agreement (error (* 1/2 error)))
        (:instance lw-dirichlet-transform-transport
         (left (lw-complex-dirichlet-series-value rate height (lw-mellin-zeta-ratio-request rate height error)))
         (right (lw-complex-zeta-log-quotient-value rate height (lw-mellin-zeta-ratio-request rate height error)))
         (left-gamma (car (lw-euler-bounds (lw-mellin-zeta-ratio-request rate height error)))) (right-gamma (car (lw-euler-bounds (lw-mellin-zeta-ratio-request rate height error))))
         (prime-error (* 1/2 error)) (gamma-error 0)))
  :in-theory (e/d (lw-mellin-zeta-ratio-value lw-mellin-zeta-ratio-request lw-dirichlet-transform-value)
   (lw-mellin-zeta-ratio-request-valid lw-complex-dirichlet-series-ratio-computed-agreement
    lw-dirichlet-transform-transport))
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-zeta-ratio-value)))

(defthm lw-mellin-zeta-ratio-value-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-zeta-ratio-value rate height left-error) (lw-mellin-zeta-ratio-value rate height right-error))
   (+ left-error right-error)))
 :hints (("Goal"
  :use
  ((:instance lw-mellin-zeta-ratio-request-valid (error left-error))
   (:instance lw-mellin-zeta-ratio-request-valid (error right-error))
   (:instance lw-complex-zeta-log-quotient-value-cauchy
    (left-error (lw-mellin-zeta-ratio-request rate height left-error)) (right-error (lw-mellin-zeta-ratio-request rate height right-error)))
   (:instance lw-euler-lower-cauchy
    (left-error (lw-mellin-zeta-ratio-request rate height left-error)) (right-error (lw-mellin-zeta-ratio-request rate height right-error)))
   (:instance lw-dirichlet-transform-transport
    (left (lw-complex-zeta-log-quotient-value rate height (lw-mellin-zeta-ratio-request rate height left-error))) (right (lw-complex-zeta-log-quotient-value rate height (lw-mellin-zeta-ratio-request rate height right-error)))
    (left-gamma (car (lw-euler-bounds (lw-mellin-zeta-ratio-request rate height left-error)))) (right-gamma (car (lw-euler-bounds (lw-mellin-zeta-ratio-request rate height right-error))))
    (prime-error (+ (lw-mellin-zeta-ratio-request rate height left-error) (lw-mellin-zeta-ratio-request rate height right-error)))
    (gamma-error (+ (lw-mellin-zeta-ratio-request rate height left-error) (lw-mellin-zeta-ratio-request rate height right-error))))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub (lw-mellin-zeta-ratio-value rate height left-error) (lw-mellin-zeta-ratio-value rate height right-error)))
    (radius (* 2 (+ (lw-mellin-zeta-ratio-request rate height left-error) (lw-mellin-zeta-ratio-request rate height right-error))))
    (cap (+ left-error right-error))))
  :in-theory (e/d (lw-mellin-zeta-ratio-value)
   (lw-mellin-zeta-ratio-request-valid lw-complex-zeta-log-quotient-value-cauchy
    lw-euler-lower-cauchy lw-dirichlet-transform-transport lw-complex-disk-enlarge))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-zeta-series-ratio-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-ratio-value rate height right-error))
   (+ (* 5 left-error) right-error)))
 :hints (("Goal"
  :use
  ((:instance lw-mellin-zeta-ratio-request-valid (error right-error))
   (:instance lw-mellin-integral-rational (sigma rate) (index 0) (error left-error))
   (:instance lw-mellin-dirichlet-series-comparison (right-error (* 4 (lw-mellin-zeta-ratio-request rate height right-error))))
   (:instance lw-mellin-zeta-ratio-normalization-comparison (error right-error))
   (:instance lw-complex-difference-triangle
    (left (lw-mellin-integral rate height 0 left-error))
    (middle (lw-dirichlet-transform-value rate height (* 4 (lw-mellin-zeta-ratio-request rate height right-error)))) (right (lw-mellin-zeta-ratio-value rate height right-error))
    (radius (+ (* 5 left-error) (* 4 (lw-mellin-zeta-ratio-request rate height right-error)))) (other-radius (* 1/2 right-error)))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub (lw-mellin-integral rate height 0 left-error) (lw-mellin-zeta-ratio-value rate height right-error)))
    (radius (+ (* 5 left-error) (* 4 (lw-mellin-zeta-ratio-request rate height right-error)) (* 1/2 right-error)))
    (cap (+ (* 5 left-error) right-error))))
  :in-theory (disable lw-mellin-zeta-ratio-request-valid lw-mellin-integral-rational
                      lw-mellin-dirichlet-series-comparison lw-mellin-zeta-ratio-normalization-comparison
                      lw-complex-difference-triangle lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t)))

