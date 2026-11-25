(in-package "ACL2")

(include-book "dirichlet-family-precision")
(include-book "dirichlet-tails")

; Varying-count Cauchy control for the computed finite Dirichlet values.
; An auxiliary node precision is chosen after the larger count is known.

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

(local (defthm lw-dfc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dfc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dfc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dfc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dfc-times-negative (a b) (b a)))
                 :in-theory (disable lw-dfc-times-negative)))))

(local (defthm lw-dfc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dfc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dfc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dfc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dfc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dfc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dfc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dfc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dfc-left-commutes)))))

(local (in-theory
 (disable lw-dirichlet-cubic-cost lw-dirichlet-cubic-node-cost
          lw-complex-dirichlet-prime-sum lw-complex-dirichlet-finite-value
          lw-dirichlet-finite-model-precision lw-dirichlet-finite-coefficient-precision
          lw-dirichlet-finite-node-precision lw-dirichlet-finite-precisions-valid
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (defthm lw-dfc-count-mass-data
 (implies (natp count)
  (and (rationalp (* count (+ 1 count))) (<= 0 (* count (+ 1 count)))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfc-precision-scalar
 (implies
  (and (rationalp slope) (<= 0 slope) (rationalp mass) (<= 0 mass)
       (rationalp cost) (<= 0 cost) (natp count)
       (rationalp error) (< 0 error))
  (let ((model (min 1 (/ error (+ 1 slope))))
        (coefficient (/ error (* 8 (+ 1 count))))
        (node (min 1 (/ error (* 64 (+ 1 mass cost))))))
   (and (rationalp model) (< 0 model) (<= model 1) (<= model error)
        (rationalp coefficient) (< 0 coefficient)
        (rationalp node) (< 0 node) (<= node 1)
        (<= (+ (* slope 1/16 model) (* 16 mass node) (* 2 count coefficient)) error)
        (<= (+ (* cost node) (* 3/8 model)) error))))
 :hints (("Goal"
  :use ((:instance lw-dfc-multiply-order
         (a (min 1 (/ error (+ 1 slope)))) (b (/ error (+ 1 slope))) (factor (* 1/16 slope)))
        (:instance lw-positive-division-bound
         (numerator (* 1/16 slope error)) (divisor (+ 1 slope)) (bound (* 1/16 error)))
        (:instance lw-positive-division-bound
         (numerator error) (divisor (+ 1 slope)) (bound error))
        (:instance lw-dfc-multiply-order
         (a (min 1 (/ error (* 64 (+ 1 mass cost))))) (b (/ error (* 64 (+ 1 mass cost))))
         (factor (* 16 mass)))
        (:instance lw-positive-division-bound
         (numerator (* 16 mass error)) (divisor (* 64 (+ 1 mass cost))) (bound (* 1/4 error)))
        (:instance lw-dfc-multiply-order
         (a (min 1 (/ error (* 64 (+ 1 mass cost))))) (b (/ error (* 64 (+ 1 mass cost))))
         (factor cost))
        (:instance lw-positive-division-bound
         (numerator (* cost error)) (divisor (* 64 (+ 1 mass cost))) (bound (* 1/64 error)))
        (:instance lw-positive-division-bound
         (numerator (* 2 count error)) (divisor (* 8 (+ 1 count))) (bound (* 1/4 error))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-dirichlet-tail-node-precision (rate height count error)
 (min 1 (/ error (* 64 (+ 1 (* count (+ 1 count))
                          (lw-dirichlet-cubic-cost rate height count))))))

(local (in-theory (disable lw-dirichlet-tail-node-precision)))

(defthm lw-dirichlet-tail-precisions-valid
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
       (rationalp error) (< 0 error))
  (let ((model (lw-dirichlet-finite-model-precision rate height error))
        (coefficient (lw-dirichlet-finite-coefficient-precision count error))
        (node (lw-dirichlet-tail-node-precision rate height count error)))
   (and (rationalp model) (< 0 model) (<= model 1) (<= model error)
        (rationalp coefficient) (< 0 coefficient)
        (rationalp node) (< 0 node) (<= node 1)
        (<= (+ (* (* 2 (+ rate (abs height))) 1/16 model)
               (* 16 (* count (+ 1 count)) node) (* 2 count coefficient)) error)
        (<= (+ (* (lw-dirichlet-cubic-cost rate height count) node) (* 3/8 model)) error))))
 :hints (("Goal"
  :use (lw-dfc-count-mass-data lw-dirichlet-cubic-cost-valid
        (:instance lw-dfc-precision-scalar
         (slope (* 2 (+ rate (abs height)))) (mass (* count (+ 1 count)))
         (cost (lw-dirichlet-cubic-cost rate height count))))
  :in-theory (e/d (lw-dirichlet-finite-model-precision
                   lw-dirichlet-finite-coefficient-precision lw-dirichlet-tail-node-precision)
                  (lw-dirichlet-cubic-cost-valid))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-dirichlet-tail-value (rate height count total error)
 (lw-complex-dirichlet-prime-sum rate height count total
  (lw-dirichlet-finite-model-precision rate height error)
  (lw-dirichlet-finite-coefficient-precision total error)
  (lw-dirichlet-tail-node-precision rate height total error)))

(local (in-theory (disable lw-complex-dirichlet-tail-value lw-dirichlet-tail-precisions-valid)))

(local (defthm lw-dfc-prefix-budget
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (natp count) (natp total) (<= count total) (rationalp error) (< 0 error))
  (<= (+ (* (* 2 (+ rate (abs height))) 1/16
            (lw-dirichlet-finite-model-precision rate height error))
         (* 16 (* count (+ 1 count))
            (lw-dirichlet-tail-node-precision rate height total error))
         (* 2 count (lw-dirichlet-finite-coefficient-precision total error)))
      error))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-dfc-multiply-order
         (a (* count (+ 1 count))) (b (* total (+ 1 total)))
         (factor (* 16 (lw-dirichlet-tail-node-precision rate height total error))))
        (:instance lw-dfc-multiply-order (a count) (b total)
         (factor (* 2 (lw-dirichlet-finite-coefficient-precision total error)))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dfc-tail-rational
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp count) (natp total)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-dirichlet-tail-value rate height count total error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-complex-dirichlet-prime-sum-rational
         (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision total error)) (delta (lw-dirichlet-tail-node-precision rate height total error))))
  :in-theory (e/d (lw-complex-dirichlet-tail-value)
                  (lw-complex-dirichlet-prime-sum-rational))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dfc-prefix-comparison
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (natp count) (natp total) (<= count total)
       (rationalp error) (< 0 error) (rationalp finite-error) (< 0 finite-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-tail-value rate height count total error) (lw-complex-dirichlet-finite-value rate height count finite-error))
                    (+ error finite-error)))
 :hints (("Goal"
  :use (lw-dfc-prefix-budget
        (:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-complex-dirichlet-prime-sum-finite-comparison
         (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision total error)) (delta (lw-dirichlet-tail-node-precision rate height total error)) (error finite-error))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count total (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision total error) (lw-dirichlet-tail-node-precision rate height total error)) (lw-complex-dirichlet-finite-value rate height count finite-error)))
         (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (lw-dirichlet-finite-model-precision rate height error)) (* 16 (* count (+ 1 count)) (lw-dirichlet-tail-node-precision rate height total error)) (* 2 count (lw-dirichlet-finite-coefficient-precision total error)) finite-error)) (cap (+ error finite-error))))
  :in-theory (e/d (lw-complex-dirichlet-tail-value)
                  (lw-complex-dirichlet-prime-sum-finite-comparison))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dfc-auxiliary-tail
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-dirichlet-tail-value rate height count count error) (lw-complex-dirichlet-tail-value rate height start count error))
   (+ (* 2 (/ start)) error)))
 :hints (("Goal"
  :use (lw-dirichlet-tail-precisions-valid
        (:instance lw-complex-dirichlet-uniform-tail (total count)
         (model-error (lw-dirichlet-finite-model-precision rate height error))
         (primitive-error (lw-dirichlet-finite-coefficient-precision count error))
         (error (lw-dirichlet-tail-node-precision rate height count error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-dirichlet-tail-value rate height count count error) (lw-complex-dirichlet-tail-value rate height start count error)))
         (radius (+ (* 2 (/ start))
                    (* (lw-dirichlet-cubic-cost rate height count)
                       (lw-dirichlet-tail-node-precision rate height count error))
                    (* 3/8 (lw-dirichlet-finite-model-precision rate height error))))
         (cap (+ (* 2 (/ start)) error))))
  :in-theory (e/d (lw-complex-dirichlet-tail-value)
                  (lw-complex-dirichlet-uniform-tail))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dfc-four-point
 (implies
  (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
       (lw-complex-diskp (lw-complex-sub b a) ra)
       (lw-complex-diskp (lw-complex-sub b c) rb)
       (lw-complex-diskp (lw-complex-sub c d) rc))
  (lw-complex-diskp (lw-complex-sub a d) (+ (+ ra rb) rc)))
 :hints (("Goal"
  :use ((:instance lw-complex-difference-symmetric (left b) (right a) (radius ra))
        (:instance lw-complex-difference-triangle
         (left a) (middle b) (right c) (radius ra) (other-radius rb))
        (:instance lw-complex-difference-triangle
         (left a) (middle c) (right d) (radius (+ ra rb)) (other-radius rc)))
  :in-theory (disable lw-complex-difference-triangle)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-finite-value-truncation-cauchy
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-finite-value rate height count left-error) (lw-complex-dirichlet-finite-value rate height start right-error))
   (+ (* 2 (/ start)) (* 4 (+ left-error right-error)))))
 :hints (("Goal"
  :use ((:instance lw-dfc-tail-rational (total count) (error (+ left-error right-error)))
        (:instance lw-dfc-tail-rational (count start) (total count) (error (+ left-error right-error)))
        (:instance lw-complex-dirichlet-finite-value-rational (error left-error))
        (:instance lw-complex-dirichlet-finite-value-rational (count start) (error right-error))
        (:instance lw-dfc-prefix-comparison (total count) (error (+ left-error right-error)) (finite-error left-error))
        (:instance lw-dfc-prefix-comparison (count start) (total count) (error (+ left-error right-error)) (finite-error right-error))
        (:instance lw-dfc-auxiliary-tail (error (+ left-error right-error)))
        (:instance lw-dfc-four-point (a (lw-complex-dirichlet-finite-value rate height count left-error)) (b (lw-complex-dirichlet-tail-value rate height count count (+ left-error right-error))) (c (lw-complex-dirichlet-tail-value rate height start count (+ left-error right-error))) (d (lw-complex-dirichlet-finite-value rate height start right-error))
         (ra (+ (+ left-error right-error) left-error)) (rb (+ (* 2 (/ start)) (+ left-error right-error))) (rc (+ (+ left-error right-error) right-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-dirichlet-finite-value rate height count left-error) (lw-complex-dirichlet-finite-value rate height start right-error)))
         (radius (+ (+ (+ (+ left-error right-error) left-error) (+ (* 2 (/ start)) (+ left-error right-error))) (+ (+ left-error right-error) right-error)))
         (cap (+ (* 2 (/ start)) (* 4 (+ left-error right-error))))))
  :in-theory (disable lw-complex-dirichlet-finite-value-rational)
  :nonlinearp nil :do-not-induct t)))



