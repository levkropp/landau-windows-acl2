(in-package "ACL2")

(include-book "dirichlet-series-product")
(include-book "zeta-log-quotient")

; The actual Mangoldt Cauchy series and the existing zeta-series ratio
; represent the same value in the right half-plane, with explicit
; independent-error bounds and a computed common refinement.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul
 lw-complex-scale lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
 lw-complex-scale-product lw-complex-sub-add lw-complex-sub-add-first lw-complex-sub-add-cancel
 lw-complex-dirichlet-series-value lw-complex-zeta-series-value lw-complex-zeta-log-quotient-value
 lw-zeta-log-quotient-precision lw-dirichlet-series-product-left-cap
 lw-dirichlet-series-product-right-cap lw-dirichlet-series-product-radius)))

(local (defthm lw-dsr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dsr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dsr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dsr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dsr-times-negative (a b) (b a)))
                 :in-theory (disable lw-dsr-times-negative)))))

(local (defthm lw-dsr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dsr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dsr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dsr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dsr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dsr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dsr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dsr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dsr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dsr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dsr-left-commutes)))))

(local (defthm lw-dsr-divide-identity
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (not (equal b (cons 0 0))) (equal (lw-complex-mul c b) d))
  (equal (lw-complex-sub a c)
         (lw-complex-mul (lw-complex-reciprocal b) (lw-complex-sub (lw-complex-mul a b) d))))
 :hints (("Goal"
  :use ((:instance lw-complex-mul-subtract (a b) (b a) (c c))
        (:instance lw-complex-linear-solve
         (a b) (b (lw-complex-sub a c)) (c (lw-complex-sub (lw-complex-mul a b) d))))
  :in-theory (disable lw-complex-mul-subtract)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dsr-divide-error
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (not (equal b (cons 0 0))) (equal (lw-complex-mul c b) d)
               (lw-complex-diskp (lw-complex-reciprocal b) 4)
               (lw-complex-diskp (lw-complex-sub (lw-complex-mul a b) d) error))
  (lw-complex-diskp (lw-complex-sub a c) (* 4 error)))
 :hints (("Goal"
  :use (lw-dsr-divide-identity
        (:instance lw-complex-mul-disk
         (left (lw-complex-reciprocal b)) (radius 4)
         (right (lw-complex-sub (lw-complex-mul a b) d)) (other-radius error)))
  :in-theory (disable lw-complex-mul-disk)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-series-ratio-precision-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error) (<= mangoldt-error 1)
               (rationalp ratio-error) (< 0 ratio-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-series-value rate height mangoldt-error) (lw-complex-zeta-log-quotient-value rate height ratio-error))
   (* 4 (+ (* (lw-dirichlet-series-product-right-cap rate height) mangoldt-error) (* (+ (lw-dirichlet-series-product-left-cap rate height) 1) (lw-zeta-log-quotient-precision ratio-error))))))
 :hints (("Goal"
  :use
  ((:instance lw-zeta-log-quotient-precision-valid (error ratio-error))
   (:instance lw-complex-dirichlet-series-product (ordinary-error (lw-zeta-log-quotient-precision ratio-error)) (log-error (lw-zeta-log-quotient-precision ratio-error)))
   (:instance lw-complex-zeta-log-quotient-value-rational (error ratio-error))
   (:instance lw-complex-zeta-log-quotient-value-product (error ratio-error))
   (:instance lw-complex-zeta-series-clearance (error (lw-zeta-log-quotient-precision ratio-error)))
   (:instance lw-complex-zeta-series-reciprocal-cap (error (lw-zeta-log-quotient-precision ratio-error)))
   (:instance lw-dsr-divide-error (a (lw-complex-dirichlet-series-value rate height mangoldt-error)) (b (lw-complex-zeta-series-value nil rate height (lw-zeta-log-quotient-precision ratio-error))) (c (lw-complex-zeta-log-quotient-value rate height ratio-error)) (d (lw-complex-zeta-series-value t rate height (lw-zeta-log-quotient-precision ratio-error))) (error (lw-dirichlet-series-product-radius rate height mangoldt-error (lw-zeta-log-quotient-precision ratio-error) (lw-zeta-log-quotient-precision ratio-error)))))
  :in-theory (e/d (lw-dirichlet-series-product-radius)
   (lw-zeta-log-quotient-precision-valid lw-complex-dirichlet-series-product
    lw-complex-zeta-log-quotient-value-rational lw-complex-zeta-log-quotient-value-product
    lw-complex-zeta-series-clearance lw-complex-zeta-series-reciprocal-cap))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-zeta-log-quotient-precision-small
 (implies (and (rationalp error) (< 0 error))
  (<= (lw-zeta-log-quotient-precision error) error))
 :hints (("Goal" :use (lw-zeta-log-quotient-precision-valid)
                 :in-theory (disable lw-zeta-log-quotient-precision-valid)
                 :do-not-induct t)))

(defthm lw-complex-dirichlet-series-ratio-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error) (<= mangoldt-error 1)
               (rationalp ratio-error) (< 0 ratio-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-series-value rate height mangoldt-error) (lw-complex-zeta-log-quotient-value rate height ratio-error))
   (+ (* 4 (lw-dirichlet-series-product-right-cap rate height) mangoldt-error) (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1) ratio-error))))
 :hints (("Goal"
  :use (lw-complex-dirichlet-series-ratio-precision-agreement
        lw-dirichlet-series-product-caps-valid
        (:instance lw-zeta-log-quotient-precision-small (error ratio-error))
        (:instance lw-dsr-multiply-order
         (a (lw-zeta-log-quotient-precision ratio-error)) (b ratio-error) (factor (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-dirichlet-series-value rate height mangoldt-error) (lw-complex-zeta-log-quotient-value rate height ratio-error)))
         (radius (* 4 (+ (* (lw-dirichlet-series-product-right-cap rate height) mangoldt-error) (* (+ (lw-dirichlet-series-product-left-cap rate height) 1) (lw-zeta-log-quotient-precision ratio-error)))))
         (cap (+ (* 4 (lw-dirichlet-series-product-right-cap rate height) mangoldt-error) (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1) ratio-error)))))
  :in-theory (disable lw-complex-dirichlet-series-ratio-precision-agreement
                      lw-dirichlet-series-product-caps-valid lw-zeta-log-quotient-precision-small
                      lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t)))

(defun lw-dirichlet-series-ratio-precision (rate height error)
 (min 1 (/ error (+ 1 (* 4 (lw-dirichlet-series-product-right-cap rate height)) (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1))))))

(local (defthm lw-dsr-refinement-algebra
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((request (min 1 (/ error (+ 1 cost)))))
   (and (rationalp request) (< 0 request) (<= request 1) (<= (* cost request) error))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound (numerator (* cost error)) (divisor (+ 1 cost)) (bound error))
        (:instance lw-dsr-multiply-order
         (a (min 1 (/ error (+ 1 cost)))) (b (/ error (+ 1 cost))) (factor cost)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-dirichlet-series-ratio-precision-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-series-ratio-precision rate height error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= (+ (* 4 (lw-dirichlet-series-product-right-cap rate height) request) (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1) request)) error))))
 :hints (("Goal"
  :use (lw-dirichlet-series-product-caps-valid
        (:instance lw-dsr-refinement-algebra (cost (+ (* 4 (lw-dirichlet-series-product-right-cap rate height)) (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1))))))
  :in-theory (disable lw-dirichlet-series-product-caps-valid)
  :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-series-ratio-precision)))

(defthm lw-complex-dirichlet-series-ratio-computed-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-series-ratio-precision rate height error)))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-dirichlet-series-value rate height request)
                    (lw-complex-zeta-log-quotient-value rate height request))
    error)))
 :hints (("Goal"
  :use (lw-dirichlet-series-ratio-precision-valid
        (:instance lw-complex-dirichlet-series-ratio-agreement
         (mangoldt-error (lw-dirichlet-series-ratio-precision rate height error))
         (ratio-error (lw-dirichlet-series-ratio-precision rate height error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-dirichlet-series-value rate height (lw-dirichlet-series-ratio-precision rate height error))
          (lw-complex-zeta-log-quotient-value rate height (lw-dirichlet-series-ratio-precision rate height error))))
         (radius (+ (* 4 (lw-dirichlet-series-product-right-cap rate height) (lw-dirichlet-series-ratio-precision rate height error))
                    (* 4 (+ (lw-dirichlet-series-product-left-cap rate height) 1) (lw-dirichlet-series-ratio-precision rate height error))))
         (cap error)))
  :in-theory (disable lw-dirichlet-series-ratio-precision-valid
                      lw-complex-dirichlet-series-ratio-agreement lw-complex-disk-enlarge)
  :do-not-induct t)))

