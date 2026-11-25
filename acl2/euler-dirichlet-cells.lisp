(in-package "ACL2")

(include-book "complex-euler-cell")
(include-book "dirichlet-dyadic-decay")

; Actual adjacent n^(-s) samples, with all logarithm and exponential
; errors charged to a computed finite coefficient.

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

(local (in-theory
 (disable lw-log-bounds-nonnegative lw-log-bounds-lower-coarse
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (in-theory (disable lw-dirichlet-product-cap lw-complex-euler-cell-factor)))

(local (defthm lw-edc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edc-times-negative (a b) (b a)))
                 :in-theory (disable lw-edc-times-negative)))))

(local (defthm lw-edc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edc-left-commutes)))))

(local (defthm lw-edc-triple
 (implies (rationalp a) (equal (+ a a a) (* 3 a)))))

(local (defthm lw-edc-one-plus-double
 (implies (rationalp a) (equal (+ a (* 2 a)) (* 3 a)))))

(local (defthm lw-edc-successor-product
 (implies (posp index) (equal (* index (+ 1 (/ index))) (+ 1 index)))
 :hints (("Goal" :use ((:instance lw-edc-inverse-factor (divisor index) (coefficient 1)))
                 :in-theory (disable lw-edc-inverse-factor)))))

(defun lw-euler-dirichlet-product-cost (rate height index)
 (* (+ 1 index)
    (+ (lw-dirichlet-product-cap rate height index)
       (lw-dirichlet-product-cap rate height (+ 1 (/ index)))
       66 (* 6 (+ rate (abs height))))))

(defun lw-complex-euler-dirichlet-cell (rate height index error)
 (let ((here (lw-complex-log-ramp-independent-exp rate height index error error))
       (next (lw-complex-log-ramp-independent-exp rate height (+ 1 index) error error)))
  (lw-complex-add
   (lw-complex-mul (cons rate height) here)
   (lw-complex-scale (+ 1 index) (lw-complex-sub next here)))))

(local (in-theory (disable lw-euler-dirichlet-product-cost lw-complex-euler-dirichlet-cell)))

(defthm lw-euler-dirichlet-product-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp index) (< 1 index))
  (and (rationalp (lw-euler-dirichlet-product-cost rate height index))
       (< 0 (lw-euler-dirichlet-product-cost rate height index))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-product-cap-valid)
        (:instance lw-dirichlet-product-cap-valid (index (+ 1 (/ index))))
        (:instance lw-edc-positive-product (a (+ 1 index))
         (b (+ (lw-dirichlet-product-cap rate height index)
               (lw-dirichlet-product-cap rate height (+ 1 (/ index)))
               66 (* 6 (+ rate (abs height)))))))
  :in-theory (e/d (lw-euler-dirichlet-product-cost) (lw-dirichlet-product-cap-valid))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-dirichlet-cell-rational
 (implies (and (rationalp rate) (rationalp height) (posp index) (< 1 index)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-dirichlet-cell rate height index error)))
 :hints (("Goal"
  :use ((:instance lw-complex-log-ramp-independent-exp-rational (log-error error) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-rational (index (+ 1 index)) (log-error error) (delta error)))
  :in-theory (e/d (lw-complex-euler-dirichlet-cell lw-complexp)
                  (lw-complex-log-ramp-independent-exp-rational))
  :do-not-induct t)))

(local (defthm lw-edc-factor-exp
 (implies (and (rationalp rate) (rationalp height) (posp index)
               (rationalp error) (< 0 error))
  (equal (lw-complex-euler-cell-factor (cons rate height) index error)
   (lw-complex-add (cons rate height)
    (lw-complex-scale (+ 1 index)
     (lw-complex-sub
      (lw-complex-log-ramp-independent-exp rate height (+ 1 (/ index)) error error)
      (cons 1 0))))))
 :hints (("Goal" :in-theory (enable lw-complex-euler-cell-factor
  lw-complex-log-ramp-independent-exp lw-complex-log-ramp-start
  lw-complex-scale lw-complex-laplace-point))) :rule-classes nil))

(local (defthm lw-edc-factor-residual
 (implies (and (lw-complexp point) (lw-complexp here) (lw-complexp next)
               (lw-complexp ratio) (rationalp index))
  (equal
   (lw-complex-sub
    (lw-complex-add (lw-complex-mul point here)
     (lw-complex-scale (+ 1 index) (lw-complex-sub next here)))
    (lw-complex-mul here
     (lw-complex-add point
      (lw-complex-scale (+ 1 index) (lw-complex-sub ratio (cons 1 0))))))
   (lw-complex-scale (+ 1 index)
    (lw-complex-sub next (lw-complex-mul here ratio)))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)
                 :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-complex-euler-dirichlet-cell-factor-comparison
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (posp index) (< 1 index)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-euler-dirichlet-cell rate height index error)
    (lw-complex-mul
     (lw-complex-log-ramp-independent-exp rate height index error error)
     (lw-complex-euler-cell-factor (cons rate height) index error)))
   (* (lw-euler-dirichlet-product-cost rate height index) error)))
 :hints (("Goal"
  :use ((:instance lw-complex-dirichlet-product-multiplication
         (left index) (right (+ 1 (/ index)))
         (left-log-error error) (right-log-error error) (product-log-error error)
         (left-error error) (right-error error) (product-error error))
        (:instance lw-dirichlet-product-cap-valid)
        (:instance lw-dirichlet-product-cap-valid (index (+ 1 (/ index))))
        (:instance lw-complex-log-ramp-independent-exp-rational (log-error error) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-rational
         (index (+ 1 index)) (log-error error) (delta error))
        (:instance lw-complex-log-ramp-independent-exp-rational
         (index (+ 1 (/ index))) (log-error error) (delta error))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-mul
          (lw-complex-log-ramp-independent-exp rate height index error error)
          (lw-complex-log-ramp-independent-exp rate height (+ 1 (/ index)) error error)))
         (right (lw-complex-log-ramp-independent-exp rate height (+ 1 index) error error))
         (radius (* (+ (lw-dirichlet-product-cap rate height index)
                       (lw-dirichlet-product-cap rate height (+ 1 (/ index)))
                       66 (* 6 (+ rate (abs height)))) error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub
          (lw-complex-log-ramp-independent-exp rate height (+ 1 index) error error)
          (lw-complex-mul
           (lw-complex-log-ramp-independent-exp rate height index error error)
           (lw-complex-log-ramp-independent-exp rate height (+ 1 (/ index)) error error))))
         (factor (+ 1 index))
         (radius (* (+ (lw-dirichlet-product-cap rate height index)
                       (lw-dirichlet-product-cap rate height (+ 1 (/ index)))
                       66 (* 6 (+ rate (abs height)))) error)))
        lw-edc-factor-exp
        (:instance lw-edc-factor-residual (point (cons rate height))
         (here (lw-complex-log-ramp-independent-exp rate height index error error))
         (next (lw-complex-log-ramp-independent-exp rate height (+ 1 index) error error))
         (ratio (lw-complex-log-ramp-independent-exp rate height (+ 1 (/ index)) error error))))
  :in-theory (e/d (lw-complex-euler-dirichlet-cell lw-euler-dirichlet-product-cost lw-complexp)
   (lw-complex-dirichlet-product-multiplication lw-dirichlet-product-cap-valid
    lw-complex-log-ramp-independent-exp-rational lw-complex-scale-disk))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-edc-mixed-radius
 (implies (and (rationalp a) (<= 0 a) (rationalp c) (<= 0 c)
               (rationalp g) (<= 0 g) (rationalp error) (< 0 error)
               (posp index) (rationalp b) (<= 0 b) (<= b 2) (<= b (+ a (* 3 error))))
  (<= (* b (+ (* c (/ index)) (* g error)))
      (+ (* a c (/ index)) (* (+ (* 3 c (/ index)) (* 2 g)) error))))
 :hints (("Goal"
  :use ((:instance lw-edc-multiply-order (a b) (b (+ a (* 3 error))) (factor (* c (/ index))))
        (:instance lw-edc-multiply-order (a b) (b 2) (factor (* g error))))
  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-edc-mixed-product
 (implies (and (rationalp a) (<= 0 a) (rationalp c) (<= 0 c)
               (rationalp g) (<= 0 g) (rationalp error) (< 0 error) (posp index)
               (lw-complex-diskp left 2) (lw-complex-diskp left (+ a (* 3 error)))
               (lw-complex-diskp right (+ (* c (/ index)) (* g error))))
  (lw-complex-diskp (lw-complex-mul left right)
   (+ (* a c (/ index)) (* (+ (* 3 c (/ index)) (* 2 g)) error))))
 :hints (("Goal"
  :use ((:instance lw-complex-mul-disk
         (radius (min 2 (+ a (* 3 error)))) (other-radius (+ (* c (/ index)) (* g error))))
        (:instance lw-edc-mixed-radius (b (min 2 (+ a (* 3 error)))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-mul left right))
         (radius (* (min 2 (+ a (* 3 error))) (+ (* c (/ index)) (* g error))))
         (cap (+ (* a c (/ index)) (* (+ (* 3 c (/ index)) (* 2 g)) error)))))
  :in-theory (enable min)
  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defun lw-euler-dirichlet-cell-cap (rate height)
 (let ((cap (+ rate (abs height))))
  (+ cap (* 2 cap cap))))

(defun lw-euler-dirichlet-cell-rounding (rate height index)
 (+ (* 3 (lw-euler-dirichlet-cell-cap rate height) (/ index))
    (* 2 (+ rate (abs height) 1) (+ 1 index))
    (lw-euler-dirichlet-product-cost rate height index)))

(local (in-theory (disable lw-euler-dirichlet-cell-cap lw-euler-dirichlet-cell-rounding)))

(defthm lw-euler-dirichlet-cell-cap-valid
 (implies (and (rationalp rate) (< 0 rate) (rationalp height))
  (and (rationalp (lw-euler-dirichlet-cell-cap rate height))
       (< 0 (lw-euler-dirichlet-cell-cap rate height))))
 :hints (("Goal" :in-theory (enable lw-euler-dirichlet-cell-cap) :nonlinearp t)))

(defthm lw-euler-dirichlet-cell-rounding-valid
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (posp index) (< 1 index))
  (and (rationalp (lw-euler-dirichlet-cell-rounding rate height index))
       (< 0 (lw-euler-dirichlet-cell-rounding rate height index))))
 :hints (("Goal"
  :use (lw-euler-dirichlet-cell-cap-valid lw-euler-dirichlet-product-cost-valid)
  :in-theory (e/d (lw-euler-dirichlet-cell-rounding)
   (lw-euler-dirichlet-cell-cap-valid lw-euler-dirichlet-product-cost-valid))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-edc-point-l1
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (equal (lw-complex-l1 (cons rate height)) (+ rate (abs height))))
 :hints (("Goal" :in-theory (enable lw-complex-l1)))))

(local (defthm lw-edc-add-residual
 (implies (and (lw-complexp point) (lw-complexp other))
  (equal (lw-complex-add (lw-complex-sub point other) other) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(defthm lw-complex-euler-dirichlet-cell-dyadic-bound
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (posp index) (< 1 index) (<= (+ rate (abs height)) index)
               (rationalp error) (< 0 error) (<= error 1)
               (natp block) (<= 2 block) (<= (lw-rational-power 2 block) index))
  (lw-complex-diskp (lw-complex-euler-dirichlet-cell rate height index error)
   (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
            (/ rate) (/ rate) (/ block) (/ block) (/ index))
      (* (lw-euler-dirichlet-cell-rounding rate height index) error))))
 :hints (("Goal"
  :use (lw-euler-dirichlet-cell-cap-valid lw-euler-dirichlet-product-cost-valid
        lw-complex-euler-dirichlet-cell-rational
        (:instance lw-complex-l1-bound (point (cons rate height)))
        (:instance lw-complex-euler-cell-factor-bound
         (point (cons rate height)) (cap (+ rate (abs height))))
        (:instance lw-complex-euler-cell-factor-rational (point (cons rate height)))
        lw-complex-dirichlet-dyadic-decay
        (:instance lw-complex-log-ramp-independent-exp-unit-cap (log-error error))
        (:instance lw-edc-mixed-product
         (left (lw-complex-log-ramp-independent-exp rate height index error error))
         (right (lw-complex-euler-cell-factor (cons rate height) index error))
         (a (* 32 (/ rate) (/ rate) (/ block) (/ block)))
         (c (lw-euler-dirichlet-cell-cap rate height))
         (g (* (+ rate (abs height) 1) (+ 1 index))))
        lw-complex-euler-dirichlet-cell-factor-comparison
        (:instance lw-complex-add-disk
         (left (lw-complex-sub
          (lw-complex-euler-dirichlet-cell rate height index error)
          (lw-complex-mul (lw-complex-log-ramp-independent-exp rate height index error error)
           (lw-complex-euler-cell-factor (cons rate height) index error))))
         (right (lw-complex-mul
          (lw-complex-log-ramp-independent-exp rate height index error error)
          (lw-complex-euler-cell-factor (cons rate height) index error)))
         (radius (* (lw-euler-dirichlet-product-cost rate height index) error))
         (other-radius
          (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
                   (/ rate) (/ rate) (/ block) (/ block) (/ index))
             (* (+ (* 3 (lw-euler-dirichlet-cell-cap rate height) (/ index))
                   (* 2 (+ rate (abs height) 1) (+ 1 index))) error)))))
  :in-theory (e/d (lw-euler-dirichlet-cell-cap lw-euler-dirichlet-cell-rounding lw-complexp)
   (lw-euler-dirichlet-cell-cap-valid lw-euler-dirichlet-product-cost-valid
    lw-complex-euler-dirichlet-cell-rational lw-complex-euler-cell-factor-bound
    lw-complex-euler-cell-factor-rational lw-complex-dirichlet-dyadic-decay
    lw-complex-log-ramp-independent-exp-unit-cap
    lw-complex-euler-dirichlet-cell-factor-comparison lw-complex-add-disk))
  :nonlinearp nil :do-not-induct t)))



