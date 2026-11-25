(in-package "ACL2")

(include-book "log-multiplication")
(include-book "dirichlet-term-transport")

; Multiplication of the actual computed n^(-s) samples. Logarithm
; and exponential requests on the three terms remain independent.

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

(local (defthm lw-dpm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dpm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dpm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dpm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dpm-times-negative (a b) (b a)))
                 :in-theory (disable lw-dpm-times-negative)))))

(local (defthm lw-dpm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dpm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dpm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dpm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dpm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dpm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dpm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dpm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dpm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dpm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dpm-left-commutes)))))

(local (in-theory
 (disable lw-log-bounds-nonnegative lw-log-bounds-lower-coarse
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (defthm lw-dpm-log-point-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (rationalp index) (< 1 index) (rationalp error) (< 0 error))
  (and (rationalp (car (lw-log-bounds index error))) (<= 0 (car (lw-log-bounds index error)))
       (lw-complexp (lw-complex-scale (car (lw-log-bounds index error)) (lw-complex-laplace-point rate height)))
       (rationalp (* (+ rate (abs height)) index))
       (<= 0 (* (+ rate (abs height)) index))
       (<= (lw-complex-l1 (lw-complex-scale (car (lw-log-bounds index error)) (lw-complex-laplace-point rate height))) (* (+ rate (abs height)) index))))
 :hints (("Goal"
  :cases ((<= 0 height))
  :use ((:instance lw-log-bounds-interval (value index) (epsilon error))
        (:instance lw-log-bounds-lower-coarse (value index) (epsilon error)))
  :in-theory (e/d (lw-intervalp lw-complexp lw-complex-scale lw-complex-laplace-point lw-complex-l1)
                  (lw-log-bounds-interval lw-log-bounds-lower-coarse))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dpm-product-above-one
 (implies (and (rationalp left) (< 1 left) (rationalp right) (< 1 right))
  (and (rationalp (* left right)) (< 1 (* left right))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dpm-add-scaled
 (equal (lw-complex-add (lw-complex-scale a point) (lw-complex-scale b point))
        (lw-complex-scale (+ a b) point))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-scale)))))

(defun lw-dirichlet-product-cap (rate height index)
 (lw-complex-exp-uniform-cap (* (+ rate (abs height)) index)))

(local (in-theory (disable lw-dirichlet-product-cap)))

(defthm lw-dirichlet-product-cap-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (rationalp index) (< 1 index))
  (and (rationalp (lw-dirichlet-product-cap rate height index))
       (<= 1 (lw-dirichlet-product-cap rate height index))))
 :hints (("Goal"
  :use ((:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index))))
  :in-theory (enable lw-dirichlet-product-cap)
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-dpm-exponential-product
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
       (rationalp left) (< 1 left) (rationalp right) (< 1 right)
       (rationalp left-log-error) (< 0 left-log-error)
       (rationalp right-log-error) (< 0 right-log-error)
       (rationalp product-log-error) (< 0 product-log-error)
       (rationalp left-error) (< 0 left-error)
       (rationalp right-error) (< 0 right-error)
       (rationalp product-error) (< 0 product-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left left-log-error left-error) (lw-complex-log-ramp-independent-exp rate height right right-log-error right-error)) (lw-complex-exp-value (lw-complex-scale (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (lw-complex-laplace-point rate height)) product-error)) (+ (* (lw-dirichlet-product-cap rate height right) left-error) (* (lw-dirichlet-product-cap rate height left) right-error) (* 2 product-error))))
 :hints (("Goal"
  :use ((:instance lw-dpm-log-point-data (index left) (error left-log-error))
        (:instance lw-dpm-log-point-data (index right) (error right-log-error))
        (:instance lw-dirichlet-product-cap-valid (index left))
        (:instance lw-dirichlet-product-cap-valid (index right))
        (:instance lw-complex-exp-cap-valid (point (lw-complex-scale (car (lw-log-bounds left left-log-error)) (lw-complex-laplace-point rate height))))
        (:instance lw-complex-exp-cap-valid (point (lw-complex-scale (car (lw-log-bounds right right-log-error)) (lw-complex-laplace-point rate height))))
        (:instance lw-complex-exp-cap-uniform (point (lw-complex-scale (car (lw-log-bounds left left-log-error)) (lw-complex-laplace-point rate height))) (argument-cap (* (+ rate (abs height)) left)))
        (:instance lw-complex-exp-cap-uniform (point (lw-complex-scale (car (lw-log-bounds right right-log-error)) (lw-complex-laplace-point rate height))) (argument-cap (* (+ rate (abs height)) right)))
        (:instance lw-dpm-multiply-order (a (lw-complex-exp-cap (lw-complex-scale (car (lw-log-bounds right right-log-error)) (lw-complex-laplace-point rate height)))) (b (lw-dirichlet-product-cap rate height right)) (factor left-error))
        (:instance lw-dpm-multiply-order (a (lw-complex-exp-cap (lw-complex-scale (car (lw-log-bounds left left-log-error)) (lw-complex-laplace-point rate height)))) (b (lw-dirichlet-product-cap rate height left)) (factor right-error))
        (:instance lw-complex-exp-value-multiplication (left (lw-complex-scale (car (lw-log-bounds left left-log-error)) (lw-complex-laplace-point rate height))) (right (lw-complex-scale (car (lw-log-bounds right right-log-error)) (lw-complex-laplace-point rate height))) (sum-error product-error))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left left-log-error left-error) (lw-complex-log-ramp-independent-exp rate height right right-log-error right-error)) (lw-complex-exp-value (lw-complex-scale (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (lw-complex-laplace-point rate height)) product-error)))
         (radius (+ (* (lw-complex-exp-cap (lw-complex-scale (car (lw-log-bounds right right-log-error)) (lw-complex-laplace-point rate height))) left-error) (* (lw-complex-exp-cap (lw-complex-scale (car (lw-log-bounds left left-log-error)) (lw-complex-laplace-point rate height))) right-error) (* 2 product-error))) (cap (+ (* (lw-dirichlet-product-cap rate height right) left-error) (* (lw-dirichlet-product-cap rate height left) right-error) (* 2 product-error)))))
  :in-theory (e/d (lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start lw-dirichlet-product-cap)
    (lw-dirichlet-product-cap-valid lw-complex-exp-cap-valid
     lw-complex-exp-cap-uniform lw-complex-exp-value-multiplication))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dpm-log-sum-transport
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
       (rationalp left) (< 1 left) (rationalp right) (< 1 right)
       (rationalp left-log-error) (< 0 left-log-error)
       (rationalp right-log-error) (< 0 right-log-error)
       (rationalp product-log-error) (< 0 product-log-error)
       (rationalp left-error) (< 0 left-error)
       (rationalp right-error) (< 0 right-error)
       (rationalp product-error) (< 0 product-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-value (lw-complex-scale (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (lw-complex-laplace-point rate height)) product-error) (lw-complex-log-ramp-independent-exp rate height (* left right) product-log-error product-error)) (+ (* (* 2 (+ rate (abs height))) (+ left-log-error right-log-error product-log-error)) (* 64 product-error))))
 :hints (("Goal"
  :use (lw-dpm-product-above-one
        (:instance lw-dpm-log-point-data (index left) (error left-log-error))
        (:instance lw-dpm-log-point-data (index right) (error right-log-error))
        (:instance lw-dpm-log-point-data (index (* left right)) (error product-log-error))
        (:instance lw-log-lower-multiplication
         (left-error left-log-error) (right-error right-log-error) (product-error product-log-error))
        (:instance lw-complex-laplace-spatial-cauchy
         (left (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error)))) (right (car (lw-log-bounds (* left right) product-log-error)))
         (left-error product-error) (right-error product-error))
        (:instance lw-dpm-multiply-order
         (a (abs (- (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (car (lw-log-bounds (* left right) product-log-error))))) (b (+ left-log-error right-log-error product-log-error)) (factor (* 2 (+ rate (abs height)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-exp-value (lw-complex-scale (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (lw-complex-laplace-point rate height)) product-error) (lw-complex-log-ramp-independent-exp rate height (* left right) product-log-error product-error)))
         (radius (+ (* (* 2 (+ rate (abs height))) (abs (- (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (car (lw-log-bounds (* left right) product-log-error))))) (* 32 (+ product-error product-error)))) (cap (+ (* (* 2 (+ rate (abs height))) (+ left-log-error right-log-error product-log-error)) (* 64 product-error)))))
  :in-theory (e/d (lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start)
    (lw-log-lower-multiplication lw-complex-laplace-spatial-cauchy))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dpm-scale-point-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp start))
  (lw-complexp (lw-complex-scale start (lw-complex-laplace-point rate height))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-laplace-point)))
 :rule-classes nil))

(defthm lw-complex-dirichlet-product-multiplication
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
       (rationalp left) (< 1 left) (rationalp right) (< 1 right)
       (rationalp left-log-error) (< 0 left-log-error)
       (rationalp right-log-error) (< 0 right-log-error)
       (rationalp product-log-error) (< 0 product-log-error)
       (rationalp left-error) (< 0 left-error)
       (rationalp right-error) (< 0 right-error)
       (rationalp product-error) (< 0 product-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left left-log-error left-error) (lw-complex-log-ramp-independent-exp rate height right right-log-error right-error)) (lw-complex-log-ramp-independent-exp rate height (* left right) product-log-error product-error)) (+ (* (lw-dirichlet-product-cap rate height right) left-error) (* (lw-dirichlet-product-cap rate height left) right-error) (* (* 2 (+ rate (abs height))) (+ left-log-error right-log-error product-log-error)) (* 66 product-error))))
 :hints (("Goal"
  :use (lw-dpm-product-above-one lw-dpm-exponential-product lw-dpm-log-sum-transport
        (:instance lw-dpm-scale-point-rational
         (start (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error)))))
        (:instance lw-dirichlet-product-cap-valid (index left))
        (:instance lw-dirichlet-product-cap-valid (index right))
        (:instance lw-dpm-log-point-data (index left) (error left-log-error))
        (:instance lw-dpm-log-point-data (index right) (error right-log-error))
        (:instance lw-complex-log-ramp-independent-exp-rational (index left) (log-error left-log-error) (delta left-error))
        (:instance lw-complex-log-ramp-independent-exp-rational (index right) (log-error right-log-error) (delta right-error))
        (:instance lw-complex-log-ramp-independent-exp-rational (index (* left right)) (log-error product-log-error) (delta product-error))
        (:instance lw-complex-exp-value-rational (point (lw-complex-scale (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (lw-complex-laplace-point rate height))) (error product-error))
        (:instance lw-complex-difference-triangle (left (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left left-log-error left-error) (lw-complex-log-ramp-independent-exp rate height right right-log-error right-error))) (middle (lw-complex-exp-value (lw-complex-scale (+ (car (lw-log-bounds left left-log-error)) (car (lw-log-bounds right right-log-error))) (lw-complex-laplace-point rate height)) product-error)) (right (lw-complex-log-ramp-independent-exp rate height (* left right) product-log-error product-error))
         (radius (+ (* (lw-dirichlet-product-cap rate height right) left-error) (* (lw-dirichlet-product-cap rate height left) right-error) (* 2 product-error))) (other-radius (+ (* (* 2 (+ rate (abs height))) (+ left-log-error right-log-error product-log-error)) (* 64 product-error))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left left-log-error left-error) (lw-complex-log-ramp-independent-exp rate height right right-log-error right-error)) (lw-complex-log-ramp-independent-exp rate height (* left right) product-log-error product-error)))
         (radius (+ (+ (* (lw-dirichlet-product-cap rate height right) left-error) (* (lw-dirichlet-product-cap rate height left) right-error) (* 2 product-error)) (+ (* (* 2 (+ rate (abs height))) (+ left-log-error right-log-error product-log-error)) (* 64 product-error)))) (cap (+ (* (lw-dirichlet-product-cap rate height right) left-error) (* (lw-dirichlet-product-cap rate height left) right-error) (* (* 2 (+ rate (abs height))) (+ left-log-error right-log-error product-log-error)) (* 66 product-error)))))
  :in-theory (disable lw-dirichlet-product-cap-valid lw-complex-log-ramp-independent-exp-rational
                      lw-complex-exp-value-rational lw-complex-difference-triangle)
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-dpm-precision-scalar
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((precision (/ error (+ 1 cost))))
   (and (rationalp precision) (< 0 precision) (<= (* cost precision) error))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound (numerator (* cost error)) (divisor (+ 1 cost)) (bound error)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-dirichlet-product-precision (rate height left right error)
 (/ error (+ 1 (+ (lw-dirichlet-product-cap rate height left) (lw-dirichlet-product-cap rate height right) 66 (* 6 (+ rate (abs height)))))))

(local (in-theory (disable lw-dirichlet-product-precision)))

(defthm lw-dirichlet-product-precision-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (rationalp left) (< 1 left) (rationalp right) (< 1 right)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-dirichlet-product-precision rate height left right error)) (< 0 (lw-dirichlet-product-precision rate height left right error)) (<= (* (+ (lw-dirichlet-product-cap rate height left) (lw-dirichlet-product-cap rate height right) 66 (* 6 (+ rate (abs height)))) (lw-dirichlet-product-precision rate height left right error)) error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-product-cap-valid (index left))
        (:instance lw-dirichlet-product-cap-valid (index right))
        (:instance lw-dpm-precision-scalar (cost (+ (lw-dirichlet-product-cap rate height left) (lw-dirichlet-product-cap rate height right) 66 (* 6 (+ rate (abs height)))))))
  :in-theory (e/d (lw-dirichlet-product-precision) (lw-dirichlet-product-cap-valid))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-dirichlet-computed-product
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (rationalp left) (< 1 left) (rationalp right) (< 1 right)
               (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error)) (lw-complex-log-ramp-independent-exp rate height right (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error))) (lw-complex-log-ramp-independent-exp rate height (* left right) (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error))) error))
 :hints (("Goal"
  :use (lw-dirichlet-product-precision-valid
        (:instance lw-dirichlet-product-cap-valid (index left))
        (:instance lw-dirichlet-product-cap-valid (index right))
        (:instance lw-complex-dirichlet-product-multiplication
         (left-log-error (lw-dirichlet-product-precision rate height left right error)) (right-log-error (lw-dirichlet-product-precision rate height left right error)) (product-log-error (lw-dirichlet-product-precision rate height left right error))
         (left-error (lw-dirichlet-product-precision rate height left right error)) (right-error (lw-dirichlet-product-precision rate height left right error)) (product-error (lw-dirichlet-product-precision rate height left right error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height left (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error)) (lw-complex-log-ramp-independent-exp rate height right (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error))) (lw-complex-log-ramp-independent-exp rate height (* left right) (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error)))) (radius (+ (* (lw-dirichlet-product-cap rate height right) (lw-dirichlet-product-precision rate height left right error)) (* (lw-dirichlet-product-cap rate height left) (lw-dirichlet-product-precision rate height left right error)) (* (* 2 (+ rate (abs height))) (+ (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error) (lw-dirichlet-product-precision rate height left right error))) (* 66 (lw-dirichlet-product-precision rate height left right error)))) (cap error)))
  :in-theory (disable lw-dirichlet-product-precision-valid lw-dirichlet-product-cap-valid
                      lw-complex-dirichlet-product-multiplication)
  :nonlinearp nil :do-not-induct t)))



