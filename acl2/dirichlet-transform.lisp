(in-package "ACL2")

(include-book "dirichlet-series")

; Normalize the computed Mangoldt Dirichlet series and Euler constant
; by the same rational factors used in the finite Mellin model.

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

(local (defthm lw-dtr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dtr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dtr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dtr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dtr-times-negative (a b) (b a)))
                 :in-theory (disable lw-dtr-times-negative)))))

(local (defthm lw-dtr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dtr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dtr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dtr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dtr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dtr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dtr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dtr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dtr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dtr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dtr-left-commutes)))))

(local (in-theory (disable lw-euler-bounds lw-dirichlet-series-count
                          lw-complex-dirichlet-series-value)))

(local (defthm lw-dtr-square-nonnegative
 (implies (rationalp x) (<= 0 (* x x)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dtr-real-point-data
 (implies (and (rationalp real) (<= 1 real) (rationalp height))
  (and (lw-complexp (cons real height))
       (<= 1 (lw-complex-norm-square (cons real height)))))
 :hints (("Goal"
  :use ((:instance lw-dtr-square-nonnegative (x height)))
  :in-theory (enable lw-complexp lw-complex-norm-square)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dtr-factor-norms
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (lw-complexp (cons (- rate 1) height)) (lw-complexp (lw-complex-mul (cons (- rate 1) height) (cons rate height)))
       (<= 1 (lw-complex-norm-square (cons (- rate 1) height)))
       (<= 1 (lw-complex-norm-square (lw-complex-mul (cons (- rate 1) height) (cons rate height))))))
 :hints (("Goal"
  :use ((:instance lw-dtr-real-point-data (real rate))
        (:instance lw-dtr-real-point-data (real (- rate 1)))
        (:instance lw-complex-norm-square-product (left (cons (- rate 1) height)) (right (cons rate height)))
        (:instance lw-dtr-multiply-order
         (a 1) (b (lw-complex-norm-square (cons (- rate 1) height)))
         (factor (lw-complex-norm-square (cons rate height)))))
  :in-theory (disable lw-complex-norm-square-product)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dtr-unit-factors
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (lw-complexp (lw-complex-reciprocal (cons (- rate 1) height))) (lw-complexp (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
       (lw-complex-diskp (lw-complex-reciprocal (cons (- rate 1) height)) 1) (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))) 1)))
 :hints (("Goal"
  :use (lw-dtr-factor-norms
        (:instance lw-complex-reciprocal-disk-bound (point (cons (- rate 1) height)) (lower 1))
        (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-mul (cons (- rate 1) height) (cons rate height))) (lower 1)))
  :in-theory (disable lw-complex-reciprocal-disk-bound)
  :do-not-induct t))
 :rule-classes nil))

(defun lw-dirichlet-transform (rate height prime-value gamma-value)
 (lw-complex-add
  (lw-complex-sub (lw-complex-mul prime-value (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))) (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height)) (lw-complex-reciprocal (cons (- rate 1) height))))
  (lw-complex-scale (+ 1 gamma-value) (lw-complex-reciprocal (cons (- rate 1) height)))))

(local (in-theory (disable lw-dirichlet-transform)))

(local (defthm lw-dtr-transform-difference
 (implies (and (lw-complexp left) (lw-complexp right)
               (rationalp left-gamma) (rationalp right-gamma)
               (rationalp rate) (rationalp height))
  (equal
   (lw-complex-sub (lw-dirichlet-transform rate height left left-gamma)
                   (lw-dirichlet-transform rate height right right-gamma))
   (lw-complex-add (lw-complex-mul (lw-complex-sub left right) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))
                   (lw-complex-scale (- left-gamma right-gamma) (lw-complex-reciprocal (cons (- rate 1) height))))))
 :hints (("Goal"
  :in-theory (enable lw-dirichlet-transform lw-complex-add lw-complex-sub
                     lw-complex-mul lw-complex-scale)))
 :rule-classes nil))

(defthm lw-dirichlet-transform-transport
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-complexp left) (lw-complexp right)
               (rationalp left-gamma) (rationalp right-gamma)
               (lw-complex-diskp (lw-complex-sub left right) prime-error)
               (rationalp gamma-error) (<= 0 gamma-error)
               (<= (abs (- left-gamma right-gamma)) gamma-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-dirichlet-transform rate height left left-gamma)
                   (lw-dirichlet-transform rate height right right-gamma))
   (+ prime-error gamma-error)))
 :hints (("Goal"
  :use (lw-dtr-unit-factors lw-dtr-transform-difference
        (:instance lw-complex-mul-disk
         (left (lw-complex-sub left right)) (right (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))) (radius prime-error) (other-radius 1))
        (:instance lw-complex-scale-disk
         (point (lw-complex-reciprocal (cons (- rate 1) height))) (factor (- left-gamma right-gamma)) (radius 1))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (- left-gamma right-gamma) (lw-complex-reciprocal (cons (- rate 1) height))))
         (radius (abs (- left-gamma right-gamma))) (cap gamma-error))
        (:instance lw-complex-add-disk
         (left (lw-complex-mul (lw-complex-sub left right) (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))
         (right (lw-complex-scale (- left-gamma right-gamma) (lw-complex-reciprocal (cons (- rate 1) height))))
         (radius prime-error) (other-radius gamma-error)))
  :in-theory (disable lw-complex-mul-disk lw-complex-scale-disk lw-complex-add-disk)
  :do-not-induct t)))

(defun lw-dirichlet-transform-value (rate height error)
 (lw-dirichlet-transform rate height
  (lw-complex-dirichlet-series-value rate height (* 1/4 error))
  (car (lw-euler-bounds (* 1/4 error)))))

(local (in-theory (disable lw-dirichlet-transform-value)))

(local (defthm lw-dtr-euler-rational
 (implies (and (rationalp error) (< 0 error))
  (rationalp (car (lw-euler-bounds error))))
 :hints (("Goal" :use ((:instance lw-euler-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-euler-bounds-interval))
                 :do-not-induct t))
 :rule-classes nil))

(defthm lw-dirichlet-transform-value-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-dirichlet-transform-value rate height error)))
 :hints (("Goal"
  :use (lw-dtr-unit-factors
        (:instance lw-dtr-euler-rational (error (* 1/4 error)))
        (:instance lw-complex-dirichlet-series-value-rational (error (* 1/4 error))))
  :in-theory (e/d (lw-dirichlet-transform-value lw-dirichlet-transform)
                  (lw-complex-dirichlet-series-value-rational))
  :do-not-induct t)))

(defthm lw-dirichlet-transform-value-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error)
               (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-dirichlet-transform-value rate height left-error) (lw-dirichlet-transform-value rate height right-error))
                   (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-complex-dirichlet-series-value-rational (error (* 1/4 left-error)))
        (:instance lw-complex-dirichlet-series-value-rational (error (* 1/4 right-error)))
        (:instance lw-dtr-euler-rational (error (* 1/4 left-error)))
        (:instance lw-dtr-euler-rational (error (* 1/4 right-error)))
        (:instance lw-complex-dirichlet-series-value-cauchy
         (left-error (* 1/4 left-error)) (right-error (* 1/4 right-error)))
        (:instance lw-euler-lower-cauchy
         (left-error (* 1/4 left-error)) (right-error (* 1/4 right-error)))
        (:instance lw-dirichlet-transform-transport
         (left (lw-complex-dirichlet-series-value rate height (* 1/4 left-error))) (right (lw-complex-dirichlet-series-value rate height (* 1/4 right-error)))
         (left-gamma (car (lw-euler-bounds (* 1/4 left-error)))) (right-gamma (car (lw-euler-bounds (* 1/4 right-error))))
         (prime-error (+ (* 1/4 left-error) (* 1/4 right-error))) (gamma-error (+ (* 1/4 left-error) (* 1/4 right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-dirichlet-transform-value rate height left-error) (lw-dirichlet-transform-value rate height right-error)))
         (radius (+ (+ (* 1/4 left-error) (* 1/4 right-error)) (+ (* 1/4 left-error) (* 1/4 right-error)))) (cap (+ left-error right-error))))
  :in-theory (e/d (lw-dirichlet-transform-value)
    (lw-dirichlet-transform-transport lw-complex-dirichlet-series-value-rational
     lw-complex-dirichlet-series-value-cauchy lw-euler-lower-cauchy))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-dirichlet-transform-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (lw-complexp prime-value) (rationalp gamma-value))
  (lw-complexp (lw-dirichlet-transform rate height prime-value gamma-value)))
 :hints (("Goal" :use (lw-dtr-unit-factors)
                 :in-theory (enable lw-dirichlet-transform)
                 :do-not-induct t)))



