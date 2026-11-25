(in-package "ACL2")

(include-book "resolvent-sampling")

; Convert an actual rational principal part into the certified resolvent
; evaluator. The variable is z-R*w, so its coefficient has Landau's sign.

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
                 lw-resolvent-truncation-count lw-geometric-index lw-geometric-threshold
                 lw-cauchy-resolvent-sum lw-cauchy-resolvent-average lw-resolvent-cauchy-order
                 lw-resolvent-cauchy-count lw-complex-coefficient-mass)))

(local (defthm lw-pr-norm-zero
         (equal (lw-complex-norm-square (cons 0 0)) 0)
         :hints (("Goal" :in-theory (enable lw-complex-norm-square)))))

(defthm lw-complex-product-nonzero
  (implies (and (lw-complexp a) (lw-complexp b)
                (not (equal a (cons 0 0))) (not (equal b (cons 0 0))))
           (not (equal (lw-complex-mul a b) (cons 0 0))))
  :hints (("Goal" :use ((:instance lw-complex-norm-square-positive (point a))
                        (:instance lw-complex-norm-square-positive (point b))
                        (:instance lw-complex-norm-square-product (left a) (right b)))
                  :in-theory (disable lw-complex-norm-square-positive lw-complex-norm-square-product)
                  :nonlinearp t)))

(defthm lw-complex-reciprocal-product
  (implies (and (lw-complexp a) (lw-complexp b)
                (not (equal a (cons 0 0))) (not (equal b (cons 0 0))))
           (equal (lw-complex-reciprocal (lw-complex-mul a b))
                  (lw-complex-mul (lw-complex-reciprocal a) (lw-complex-reciprocal b))))
  :hints (("Goal" :use ((:instance lw-complex-reciprocal-inverse (point (lw-complex-mul a b)))
                        (:instance lw-complex-linear-solve
                          (b (lw-complex-mul b (lw-complex-reciprocal (lw-complex-mul a b))))
                          (c (cons 1 0)))
                        (:instance lw-complex-linear-solve
                          (a b) (b (lw-complex-reciprocal (lw-complex-mul a b)))
                          (c (lw-complex-reciprocal a)))
                        (:instance lw-complex-mul-commutative
                          (left (lw-complex-reciprocal a)) (right (lw-complex-reciprocal b))))
                  :in-theory (disable lw-complex-mul-commutative lw-complex-mul-left-commutes
                                      lw-complex-reciprocal-inverse))))

(defun lw-pole-resolvent-ratio (offset radius)
  (lw-complex-mul (cons radius 0) (lw-complex-reciprocal offset)))

(defun lw-pole-resolvent-factor (residue offset)
  (lw-complex-mul residue (lw-complex-reciprocal offset)))

(defun lw-pole-unit-value (residue offset radius point)
  (lw-complex-mul
   residue (lw-complex-reciprocal
            (lw-complex-sub offset (lw-complex-mul (cons radius 0) point)))))

(defthm lw-pole-resolvent-data
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp radius))
           (and (lw-complexp (lw-pole-resolvent-ratio offset radius))
                (lw-complexp (lw-pole-resolvent-factor residue offset))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-reciprocal
                                     lw-complex-scale lw-complex-conjugate lw-complex-norm-square))))

(defthm lw-pole-unit-value-rational
  (implies (and (lw-complexp residue) (lw-complexp offset)
                (rationalp radius) (lw-complexp point))
           (lw-complexp (lw-pole-unit-value residue offset radius point)))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-sub lw-complex-reciprocal
                                     lw-complex-scale lw-complex-conjugate lw-complex-norm-square))))

(local (defthm lw-pr-real-complex
         (implies (rationalp radius) (lw-complexp (cons radius 0)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(defthm lw-pole-denominator-factorization
  (implies (and (lw-complexp offset) (not (equal offset (cons 0 0)))
                (rationalp radius) (lw-complexp point))
           (equal
            (lw-complex-mul
             offset (lw-complex-sub (cons 1 0)
                                     (lw-complex-mul (lw-pole-resolvent-ratio offset radius) point)))
            (lw-complex-sub offset (lw-complex-mul (cons radius 0) point))))
  :hints (("Goal" :use ((:instance lw-complex-reciprocal-cancel-product
                          (a offset) (b (lw-complex-mul (cons radius 0) point))))
                  :in-theory (disable lw-complex-reciprocal-cancel-product))))

(local (in-theory (disable lw-pole-resolvent-ratio lw-pole-resolvent-factor lw-pole-unit-value)))

(defthm lw-pole-unit-value-as-resolvent
  (implies (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
                (rationalp radius)
                (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) cap) (< cap 1)
                (lw-complex-diskp point 1))
           (equal (lw-pole-unit-value residue offset radius point)
                  (lw-complex-mul (lw-pole-resolvent-factor residue offset)
                                  (lw-resolvent-value (lw-pole-resolvent-ratio offset radius) point))))
  :hints (("Goal" :use ((:instance lw-complex-mul-disk
                          (left (lw-pole-resolvent-ratio offset radius)) (radius cap)
                          (right point) (other-radius 1))
                        (:instance lw-complex-disk-excludes-one
                          (point (lw-complex-mul (lw-pole-resolvent-ratio offset radius) point)) (radius cap))
                        (:instance lw-complex-one-minus-nonzero
                          (point (lw-complex-mul (lw-pole-resolvent-ratio offset radius) point)))
                        lw-pole-denominator-factorization
                        (:instance lw-complex-reciprocal-product
                          (a offset)
                          (b (lw-complex-sub (cons 1 0)
                                             (lw-complex-mul (lw-pole-resolvent-ratio offset radius) point)))))
                  :in-theory (e/d (lw-pole-unit-value lw-pole-resolvent-factor lw-resolvent-value)
                                  (lw-pole-denominator-factorization lw-complex-reciprocal-product
                                   lw-complex-mul-disk lw-complex-mul-commutative
                                   lw-complex-mul-left-commutes)))))

(local (defun lw-pr-countdown (count)
         (declare (xargs :measure (nfix count)))
         (if (zp count) 0 (lw-pr-countdown (- count 1)))))

(defun lw-cauchy-pole-sum (residue offset radius point target count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (lw-pole-unit-value residue offset radius (lw-complex-power point (- count 1)))
      (lw-complex-conjugate
       (lw-complex-power (lw-complex-power point (- count 1)) target)))
     (lw-cauchy-pole-sum residue offset radius point target (- count 1)))))

(defthm lw-cauchy-pole-sum-rational
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp radius)
                (lw-complexp point) (natp target) (natp count))
           (lw-complexp (lw-cauchy-pole-sum residue offset radius point target count))))

(defthm lw-cauchy-pole-sum-as-resolvent
  (implies (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
                (rationalp radius)
                (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) cap) (< cap 1)
                (lw-complex-diskp point 1) (natp target) (natp count))
           (equal (lw-cauchy-pole-sum residue offset radius point target count)
                  (lw-complex-mul
                   (lw-pole-resolvent-factor residue offset)
                   (lw-cauchy-resolvent-sum (lw-pole-resolvent-ratio offset radius) point target count))))
  :hints (("Goal" :induct (lw-pr-countdown count)
                  :in-theory (e/d (lw-cauchy-resolvent-sum)
                                  (lw-complex-mul-commutative lw-complex-mul-left-commutes
                                   lw-complex-add-commutative lw-complex-add-left-commutes)))))

(defun lw-cauchy-pole-average (residue offset radius degree target count)
  (lw-complex-scale
   (/ count) (lw-cauchy-pole-sum residue offset radius (lw-cauchy-orbit-rotation degree) target count)))

(local (in-theory (disable lw-cauchy-pole-sum)))

(defthm lw-cauchy-pole-average-as-resolvent
  (implies (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
                (rationalp radius)
                (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) cap) (< cap 1)
                (natp degree) (natp target) (posp count))
           (equal (lw-cauchy-pole-average residue offset radius degree target count)
                  (lw-complex-mul
                   (lw-pole-resolvent-factor residue offset)
                   (lw-cauchy-resolvent-average (lw-pole-resolvent-ratio offset radius) degree target count))))
  :hints (("Goal" :use (lw-cauchy-orbit-data)
                  :in-theory (e/d (lw-cauchy-resolvent-average)
                                  (lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(defun lw-pole-unit-coefficient (residue offset radius target)
  (lw-complex-mul
   (lw-pole-resolvent-factor residue offset)
   (lw-complex-power (lw-pole-resolvent-ratio offset radius) target)))

(defun lw-pole-coefficient-precision (residue offset error)
  (lw-cauchy-coefficient-precision (list (lw-pole-resolvent-factor residue offset)) error))

(defthm lw-pole-coefficient-precision-adequate
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp error) (< 0 error))
           (and (rationalp (lw-pole-coefficient-precision residue offset error))
                (< 0 (lw-pole-coefficient-precision residue offset error))
                (<= (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset))
                       (lw-pole-coefficient-precision residue offset error)) error)))
  :hints (("Goal" :use ((:instance lw-cauchy-coefficient-precision-adequate
                          (coefficients (list (lw-pole-resolvent-factor residue offset)))))
                  :in-theory (e/d (lw-complex-coefficientsp lw-complex-coefficient-mass
                                   lw-pole-resolvent-factor)
                                  (lw-cauchy-coefficient-precision-adequate)))))

(defthm lw-complex-left-product-error
  (implies (and (lw-complex-diskp factor cap) (lw-complexp a) (lw-complexp b)
                (lw-complex-diskp (lw-complex-sub a b) error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-mul factor a) (lw-complex-mul factor b)) (* cap error)))
  :hints (("Goal" :use ((:instance lw-complex-mul-disk
                          (left factor) (radius cap) (right (lw-complex-sub a b)) (other-radius error)))
                  :in-theory (disable lw-complex-mul-disk lw-complex-mul-commutative
                                      lw-complex-sub-products-right))))

(local (in-theory (disable lw-cauchy-pole-average lw-pole-unit-coefficient lw-pole-coefficient-precision)))

(defthm lw-cauchy-computed-pole-coefficient
  (implies (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
                (rationalp radius)
                (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) cap) (< cap 1)
                (natp target) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-pole-average
              residue offset radius
              (- (lw-resolvent-cauchy-order cap target (lw-pole-coefficient-precision residue offset error)) 1)
              target (lw-resolvent-cauchy-count (lw-pole-resolvent-ratio offset radius) cap target
                                               (lw-pole-coefficient-precision residue offset error)))
             (lw-pole-unit-coefficient residue offset radius target)) error))
  :hints (("Goal" :use (lw-pole-coefficient-precision-adequate
                        (:instance lw-resolvent-cauchy-order-data
                          (radius cap) (error (lw-pole-coefficient-precision residue offset error)))
                        (:instance lw-cauchy-computed-resolvent-coefficient
                          (ratio (lw-pole-resolvent-ratio offset radius)) (radius cap)
                          (error (lw-pole-coefficient-precision residue offset error)))
                        (:instance lw-cauchy-pole-average-as-resolvent
                          (degree (- (lw-resolvent-cauchy-order cap target
                                                               (lw-pole-coefficient-precision residue offset error)) 1))
                          (count (lw-resolvent-cauchy-count
                                  (lw-pole-resolvent-ratio offset radius) cap target
                                  (lw-pole-coefficient-precision residue offset error))))
                        (:instance lw-complex-l1-bound (point (lw-pole-resolvent-factor residue offset)))
                        (:instance lw-complex-left-product-error
                          (factor (lw-pole-resolvent-factor residue offset))
                          (cap (lw-complex-l1 (lw-pole-resolvent-factor residue offset)))
                          (a (lw-cauchy-resolvent-average
                              (lw-pole-resolvent-ratio offset radius)
                              (- (lw-resolvent-cauchy-order cap target
                                                           (lw-pole-coefficient-precision residue offset error)) 1)
                              target (lw-resolvent-cauchy-count
                                      (lw-pole-resolvent-ratio offset radius) cap target
                                      (lw-pole-coefficient-precision residue offset error))))
                          (b (lw-complex-power (lw-pole-resolvent-ratio offset radius) target))
                          (error (lw-pole-coefficient-precision residue offset error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-cauchy-pole-average
                                   residue offset radius
                                   (- (lw-resolvent-cauchy-order cap target
                                                                (lw-pole-coefficient-precision residue offset error)) 1)
                                   target (lw-resolvent-cauchy-count
                                           (lw-pole-resolvent-ratio offset radius) cap target
                                           (lw-pole-coefficient-precision residue offset error)))
                                  (lw-pole-unit-coefficient residue offset radius target)))
                          (radius (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset))
                                     (lw-pole-coefficient-precision residue offset error)))
                          (cap error)))
                  :in-theory (e/d (lw-pole-unit-coefficient)
                                  (lw-pole-coefficient-precision-adequate lw-resolvent-cauchy-order-data
                                   lw-cauchy-computed-resolvent-coefficient lw-cauchy-pole-average-as-resolvent
                                   lw-complex-l1-bound lw-complex-left-product-error
                                   lw-complex-sub-products-right lw-complex-mul-commutative
                                   lw-complex-disk-enlarge)))))

(local (defthm lw-pr-zero-times (equal (* 0 a) 0)))

(defthm lw-complex-real-product
  (implies (and (rationalp factor) (lw-complexp point))
           (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale))))

(defthm lw-complex-real-power
  (implies (and (rationalp radius) (natp target))
           (equal (lw-complex-power (cons radius 0) target)
                  (cons (lw-rational-power radius target) 0)))
  :hints (("Goal" :induct (lw-pr-countdown target)
                  :in-theory (enable lw-complex-power lw-rational-power lw-complex-mul lw-complex-scale))))

(defthm lw-pole-unit-coefficient-formula
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp radius) (natp target))
           (equal (lw-pole-unit-coefficient residue offset radius target)
                  (lw-complex-scale
                   (lw-rational-power radius target)
                   (lw-complex-mul residue
                                   (lw-complex-power (lw-complex-reciprocal offset) (+ 1 target))))))
  :hints (("Goal" :use ((:instance lw-complex-power-product
                          (left (cons radius 0)) (right (lw-complex-reciprocal offset)) (index target)))
                  :in-theory (enable lw-pole-unit-coefficient lw-pole-resolvent-factor lw-pole-resolvent-ratio))))

; c=(1+2*i), a=(3+4*i), R=1/2: direct principal-part and second
; coefficient evaluations check the radius power and Landau sign.
(assert-event
 (and (equal (lw-pole-unit-value (cons 1 2) (cons 3 4) 1/2 (cons 1 0))
             (cons 42/89 4/89))
      (equal (lw-pole-unit-coefficient (cons 1 2) (cons 3 4) 1/2 2)
             (cons -29/62500 -139/31250))))

(local (defthm lw-pr-strict-multiply
         (implies (and (rationalp a) (rationalp b) (< a b)
                       (rationalp factor) (< 0 factor))
                  (< (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-pr-small-quotient
         (implies (and (rationalp numerator) (<= 0 numerator)
                       (rationalp denominator) (< 0 denominator) (< numerator denominator))
                  (and (rationalp (/ numerator denominator))
                       (<= 0 (/ numerator denominator)) (< (/ numerator denominator) 1)))
         :hints (("Goal" :use ((:instance inverse-of-* (x denominator))
                              (:instance lw-pr-strict-multiply
                                (a numerator) (b denominator) (factor (/ denominator))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-pr-real-disk
         (implies (and (rationalp radius) (<= 0 radius))
                  (lw-complex-diskp (cons radius 0) radius))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-pole-resolvent-clearance-bound
  (implies (and (lw-complexp offset) (rationalp lower) (< 0 lower)
                (<= (* lower lower) (lw-complex-norm-square offset))
                (rationalp radius) (<= 0 radius) (< radius lower))
           (and (not (equal offset (cons 0 0)))
                (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) (/ radius lower))
                (rationalp (/ radius lower)) (<= 0 (/ radius lower)) (< (/ radius lower) 1)))
  :hints (("Goal" :use ((:instance lw-complex-norm-lower-nonzero (point offset))
                        (:instance lw-complex-reciprocal-disk-bound (point offset))
                        (:instance lw-pr-small-quotient (numerator radius) (denominator lower))
                        (:instance lw-pr-real-disk)
                        (:instance lw-complex-mul-disk
                          (left (cons radius 0)) (radius radius)
                          (right (lw-complex-reciprocal offset)) (other-radius (/ lower))))
                  :in-theory (e/d (lw-pole-resolvent-ratio)
                                  (lw-complex-mul-disk lw-complex-reciprocal-disk-bound)))))
