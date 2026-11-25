(in-package "ACL2")

(include-book "complex-laplace-basis")

; The ramp (exp(u)-1)*exp(-s*u) is a difference of two damped
; exponentials. Prove the pointwise decomposition with its numerical
; error, then normalize the difference of their computed quadratures.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-laplace-grid lw-complex-laplace-point
                 lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (defthm lw-cramp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cramp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cramp-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cramp-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cramp-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cramp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cramp-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cramp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cramp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-cramp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))
(local (defthm lw-cramp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cramp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cramp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cramp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cramp-left-commutes)))))
(local (defthm lw-cramp-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-cramp-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))


(defun lw-complex-exp-ramp-precision (left right error)
  (/ error (* 4 (+ 1 (lw-complex-exp-cap left) (lw-complex-exp-cap right)))))

(defun lw-complex-exp-ramp-product (left right error)
  (let ((delta (lw-complex-exp-ramp-precision left right error)))
    (lw-complex-mul (lw-complex-sub (lw-complex-exp-value left delta) (cons 1 0))
                     (lw-complex-exp-value right delta))))

(defun lw-complex-exp-ramp-difference (left right error)
  (let ((delta (lw-complex-exp-ramp-precision left right error)))
    (lw-complex-sub (lw-complex-exp-value (lw-complex-add left right) delta)
                     (lw-complex-exp-value right delta))))

(local (defthm lw-cramp-scalar-precision
         (implies (and (rationalp a) (<= 1 a) (rationalp b) (<= 1 b)
                       (rationalp error) (< 0 error))
                  (let ((delta (/ error (* 4 (+ 1 a b)))))
                    (and (rationalp delta) (< 0 delta)
                         (<= (* (+ a b 2) delta) error))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x (* 4 (+ 1 a b))))
                        (:instance lw-positive-division-bound
                          (numerator (* (+ a b 2) error)) (divisor (* 4 (+ 1 a b))) (bound error)))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(defthm lw-complex-exp-ramp-precision-adequate
  (implies (and (lw-complexp left) (lw-complexp right) (rationalp error) (< 0 error))
           (let ((delta (lw-complex-exp-ramp-precision left right error)))
             (and (rationalp delta) (< 0 delta)
                  (<= (* (+ (lw-complex-exp-cap left) (lw-complex-exp-cap right) 2) delta) error))))
  :hints (("Goal" :use ((:instance lw-complex-exp-cap-valid (point left))
                         (:instance lw-complex-exp-cap-valid (point right))
                         (:instance lw-cramp-scalar-precision
                           (a (lw-complex-exp-cap left)) (b (lw-complex-exp-cap right))))
                   :in-theory (disable lw-complex-exp-cap-valid)
                   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cramp-product-defect
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
                  (equal
                   (lw-complex-sub
                     (lw-complex-mul (lw-complex-sub a (cons 1 0)) b)
                     (lw-complex-sub c b))
                   (lw-complex-sub (lw-complex-mul a b) c)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-mul)))))

(defthm lw-complex-exp-ramp-computed-decomposition
  (implies (and (lw-complexp left) (lw-complexp right) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-ramp-product left right error)
                            (lw-complex-exp-ramp-difference left right error))
            error))
  :hints (("Goal"
           :use (lw-complex-exp-ramp-precision-adequate
                 (:instance lw-complex-exp-value-multiplication
                   (left-error (lw-complex-exp-ramp-precision left right error))
                   (right-error (lw-complex-exp-ramp-precision left right error))
                   (sum-error (lw-complex-exp-ramp-precision left right error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-ramp-product left right error)
                     (lw-complex-exp-ramp-difference left right error)))
                   (radius (* (+ (lw-complex-exp-cap left) (lw-complex-exp-cap right) 2)
                              (lw-complex-exp-ramp-precision left right error)))
                   (cap error)))
           :in-theory (disable lw-complex-exp-ramp-precision
                               lw-complex-exp-ramp-precision-adequate
                               lw-complex-exp-value-multiplication)
           :nonlinearp nil :do-not-induct t)))

(defun lw-complex-laplace-ramp-value (rate height error)
  (lw-complex-sub (lw-complex-laplace-grid (- rate 1) height (* 1/4 error))
                  (lw-complex-laplace-grid rate height (* 1/4 error))))

(defthm lw-complex-laplace-ramp-value-rational
  (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-laplace-ramp-value rate height error))))

(local (defthm lw-cramp-rate-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height))
                  (and (lw-complexp (cons rate height)) (lw-complexp (cons (- rate 1) height))
                       (not (equal (cons rate height) (cons 0 0)))
                       (not (equal (cons (- rate 1) height) (cons 0 0)))
                       (equal (lw-complex-sub (cons rate height) (cons (- rate 1) height))
                              (cons 1 0))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(defthm lw-complex-laplace-ramp-reciprocal-identity
  (implies (and (rationalp rate) (< 1 rate) (rationalp height))
           (equal
            (lw-complex-sub (lw-complex-reciprocal (cons (- rate 1) height))
                            (lw-complex-reciprocal (cons rate height)))
            (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))
  :hints (("Goal"
           :use ((:instance lw-complex-reciprocal-difference
                   (a (cons (- rate 1) height)) (b (cons rate height))))
           :in-theory (disable lw-complex-reciprocal-difference))))

(local (defthm lw-cramp-subtract-differences
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
                  (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-sub c d))
                         (lw-complex-sub (lw-complex-sub a c) (lw-complex-sub b d))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(defthm lw-complex-laplace-ramp-reciprocal
  (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))
             (lw-complex-laplace-ramp-value rate height error))
            error))
  :hints (("Goal"
           :use ((:instance lw-complex-laplace-grid-reciprocal
                   (rate (- rate 1)) (error (* 1/4 error)))
                 (:instance lw-complex-laplace-grid-reciprocal (error (* 1/4 error)))
                 lw-complex-laplace-ramp-reciprocal-identity
                 (:instance lw-cramp-subtract-differences
                   (a (lw-complex-reciprocal (cons (- rate 1) height)))
                   (b (lw-complex-reciprocal (cons rate height)))
                   (c (lw-complex-laplace-grid (- rate 1) height (* 1/4 error)))
                   (d (lw-complex-laplace-grid rate height (* 1/4 error))))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-sub
                     (lw-complex-reciprocal (cons (- rate 1) height))
                     (lw-complex-laplace-grid (- rate 1) height (* 1/4 error))))
                   (right (lw-complex-sub (lw-complex-reciprocal (cons rate height))
                     (lw-complex-laplace-grid rate height (* 1/4 error))))
                   (radius (* 1/4 error)) (other-radius (* 1/4 error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))
                     (lw-complex-laplace-ramp-value rate height error)))
                   (radius (* 1/2 error)) (cap error)))
           :in-theory (disable lw-complex-laplace-grid-reciprocal lw-cramp-subtract-differences
                               lw-complex-laplace-ramp-reciprocal-identity
                               lw-complex-sub-disk lw-complex-sub-add-first)
           :do-not-induct t)))
