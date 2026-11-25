(in-package "ACL2")

(include-book "dirichlet-term-transport")

; Precision stability for the actual finite Dirichlet family. Frozen
; logarithm error sums uniformly in the finite count. Node/coefficient
; rounding terms keep their explicit count dependence.

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

(local (defthm lw-dfp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dfp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dfp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dfp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dfp-times-negative (a b) (b a)))
                 :in-theory (disable lw-dfp-times-negative)))))

(local (defthm lw-dfp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dfp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dfp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dfp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dfp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dfp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dfp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dfp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dfp-left-commutes)))))

(local (in-theory (disable lw-complex-dirichlet-prime-sum
 lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error)))

(local (defthm lw-dfp-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(defun lw-dirichlet-family-precision-radius (rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)
 (+ (* (* 2 (+ rate (abs height))) count (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error)))
    (* 16 count (+ 1 count) (+ left-error right-error))
    (* 2 count (+ left-primitive-error right-primitive-error))))

(local (in-theory (disable lw-dirichlet-family-precision-radius)))

(local (defthm lw-dfp-radius-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (and (rationalp (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)) (<= 0 (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-dfp-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-dfp-unit-data (total right-total) (model-error right-model-error)))
  :in-theory (enable lw-dirichlet-family-precision-radius)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dfp-radius-step
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (< 1 count))
  (equal (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error) (+ (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error))) (lw-dirichlet-family-precision-radius rate height (- count 1) left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-dfp-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-dfp-unit-data (total right-total) (model-error right-model-error)))
  :in-theory (enable lw-dirichlet-family-precision-radius)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dfp-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))
(local (defthm lw-dfp-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-dfp-zero-disk
 (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-dfp-radius-zero
 (equal (lw-dirichlet-family-precision-radius rate height 0 left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error) 0)
 :hints (("Goal" :in-theory (enable lw-dirichlet-family-precision-radius)))))

(local (defthm lw-dfp-one-zero-disk
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (cons 0 0) (lw-dirichlet-family-precision-radius rate height 1 left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)))
 :hints (("Goal" :use ((:instance lw-dfp-radius-data (count 1))) :do-not-induct t))))

(defthm lw-complex-dirichlet-prime-sum-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (<= right-error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-dirichlet-prime-sum rate height count right-total right-model-error right-primitive-error right-error)) (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)))
 :hints (("Goal"
  :induct (lw-complex-dirichlet-prime-sum rate height count left-total left-model-error left-primitive-error left-error)
  :in-theory (enable (:induction lw-complex-dirichlet-prime-sum) (:definition lw-complex-dirichlet-prime-sum)))
  (and stable-under-simplificationp
   '(:use (lw-dfp-radius-data lw-dfp-radius-step
           lw-complex-dirichlet-term-precision-cauchy
           (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count left-primitive-error)) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count left-total left-model-error) left-error)) (lw-complex-scale (car (lw-mangoldt-bounds count right-primitive-error)) (lw-complex-log-ramp-independent-exp rate height count (lw-smoothed-ramp-log-error count right-total right-model-error) right-error)))) (right (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height (- count 1) left-total left-model-error left-primitive-error left-error) (lw-complex-dirichlet-prime-sum rate height (- count 1) right-total right-model-error right-primitive-error right-error)))
            (radius (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error)))) (other-radius (lw-dirichlet-family-precision-radius rate height (- count 1) left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)))
           (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-dirichlet-prime-sum rate height count right-total right-model-error right-primitive-error right-error))) (radius (+ (+ (+ (* (* 2 (+ rate (abs height))) (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error))) (* 32 count (+ left-error right-error))) (* 2 (+ left-primitive-error right-primitive-error))) (lw-dirichlet-family-precision-radius rate height (- count 1) left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))) (cap (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error))))
     :in-theory (disable lw-complex-dirichlet-prime-sum lw-complex-dirichlet-term-precision-cauchy
                         lw-complex-add-disk)
     :nonlinearp nil :do-not-induct t))))

(local (defthm lw-dfp-count-log-budget
 (implies (and (natp count) (natp total) (<= count total)
               (rationalp model-error) (< 0 model-error))
  (<= (* count (lw-smoothed-ramp-unit-error total model-error)) (* 1/16 model-error)))
 :hints (("Goal"
  :use ((:instance lw-dfp-multiply-order (a count) (b (+ 1 total)) (factor model-error))
        (:instance lw-positive-division-bound
         (numerator (* count model-error)) (divisor (+ 1 total)) (bound model-error)))
  :in-theory (enable lw-smoothed-ramp-unit-error)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-prime-sum-uniform-precision-cauchy
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp left-total) (natp right-total)
       (rationalp left-model-error) (< 0 left-model-error) (rationalp right-model-error) (< 0 right-model-error)
       (rationalp left-primitive-error) (< 0 left-primitive-error) (rationalp right-primitive-error) (< 0 right-primitive-error)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (<= count left-total) (<= count right-total) (<= right-error 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-dirichlet-prime-sum rate height count right-total right-model-error right-primitive-error right-error)) (+ (* (* 2 (+ rate (abs height))) 1/16 (+ left-model-error right-model-error))
     (* 16 count (+ 1 count) (+ left-error right-error))
     (* 2 count (+ left-primitive-error right-primitive-error)))))
 :hints (("Goal"
  :use (lw-complex-dirichlet-prime-sum-precision-cauchy
        (:instance lw-dfp-unit-data (total left-total) (model-error left-model-error))
        (:instance lw-dfp-unit-data (total right-total) (model-error right-model-error))
        (:instance lw-dfp-count-log-budget (total left-total) (model-error left-model-error))
        (:instance lw-dfp-count-log-budget (total right-total) (model-error right-model-error))
        (:instance lw-dfp-multiply-order
         (a (* count (+ (lw-smoothed-ramp-unit-error left-total left-model-error) (lw-smoothed-ramp-unit-error right-total right-model-error)))) (b (* 1/16 (+ left-model-error right-model-error))) (factor (* 2 (+ rate (abs height)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count left-total left-model-error left-primitive-error left-error) (lw-complex-dirichlet-prime-sum rate height count right-total right-model-error right-primitive-error right-error))) (radius (lw-dirichlet-family-precision-radius rate height count left-total right-total left-model-error right-model-error left-primitive-error right-primitive-error left-error right-error)) (cap (+ (* (* 2 (+ rate (abs height))) 1/16 (+ left-model-error right-model-error))
     (* 16 count (+ 1 count) (+ left-error right-error))
     (* 2 count (+ left-primitive-error right-primitive-error))))))
  :in-theory (e/d (lw-dirichlet-family-precision-radius)
    (lw-complex-dirichlet-prime-sum-precision-cauchy))
  :nonlinearp nil :do-not-induct t)))

(defun lw-dirichlet-finite-model-precision (rate height error)
 (min 1 (/ error (+ 1 (* 2 (+ rate (abs height)))))))

(defun lw-dirichlet-finite-coefficient-precision (count error)
 (/ error (* 8 (+ 1 count))))

(defun lw-dirichlet-finite-node-precision (count error)
 (min 1 (/ error (* 64 (+ 1 (* count (+ 1 count)))))))

(local (in-theory (disable lw-dirichlet-finite-model-precision
 lw-dirichlet-finite-coefficient-precision lw-dirichlet-finite-node-precision)))

(local (defthm lw-dfp-count-mass-data
 (implies (natp count) (and (rationalp (* count (+ 1 count))) (<= 0 (* count (+ 1 count)))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dfp-precisions-scalar
 (implies
  (and (rationalp slope) (<= 0 slope) (rationalp mass) (<= 0 mass) (natp count)
       (rationalp error) (< 0 error))
  (let ((model (min 1 (/ error (+ 1 slope))))
        (coefficient (/ error (* 8 (+ 1 count))))
        (node (min 1 (/ error (* 64 (+ 1 mass))))))
   (and (rationalp model) (< 0 model) (<= model 1)
        (rationalp coefficient) (< 0 coefficient)
        (rationalp node) (< 0 node) (<= node 1)
        (<= (+ (* slope 1/16 model) (* 16 mass node) (* 2 count coefficient)) error))))
 :hints (("Goal"
  :use ((:instance lw-dfp-multiply-order
         (a (min 1 (/ error (+ 1 slope)))) (b (/ error (+ 1 slope))) (factor (* 1/16 slope)))
        (:instance lw-positive-division-bound
         (numerator (* 1/16 slope error)) (divisor (+ 1 slope)) (bound (* 1/16 error)))
        (:instance lw-dfp-multiply-order
         (a (min 1 (/ error (* 64 (+ 1 mass))))) (b (/ error (* 64 (+ 1 mass)))) (factor (* 16 mass)))
        (:instance lw-positive-division-bound
         (numerator (* 16 mass error)) (divisor (* 64 (+ 1 mass))) (bound (* 1/4 error)))
        (:instance lw-positive-division-bound
         (numerator (* 2 count error)) (divisor (* 8 (+ 1 count))) (bound (* 1/4 error))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-dirichlet-finite-precisions-valid
 (implies
  (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
       (rationalp error) (< 0 error))
  (and (rationalp (lw-dirichlet-finite-model-precision rate height error)) (< 0 (lw-dirichlet-finite-model-precision rate height error)) (<= (lw-dirichlet-finite-model-precision rate height error) 1)
       (rationalp (lw-dirichlet-finite-coefficient-precision count error)) (< 0 (lw-dirichlet-finite-coefficient-precision count error))
       (rationalp (lw-dirichlet-finite-node-precision count error)) (< 0 (lw-dirichlet-finite-node-precision count error)) (<= (lw-dirichlet-finite-node-precision count error) 1)
       (<= (+ (* (* 2 (+ rate (abs height))) 1/16 (lw-dirichlet-finite-model-precision rate height error)) (* 16 (* count (+ 1 count)) (lw-dirichlet-finite-node-precision count error)) (* 2 count (lw-dirichlet-finite-coefficient-precision count error))) error)))
 :hints (("Goal"
  :use (lw-dfp-count-mass-data
        (:instance lw-dfp-precisions-scalar (slope (* 2 (+ rate (abs height)))) (mass (* count (+ 1 count)))))
  :in-theory (enable lw-dirichlet-finite-model-precision
                     lw-dirichlet-finite-coefficient-precision lw-dirichlet-finite-node-precision)
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-dirichlet-finite-value (rate height count error)
 (lw-complex-dirichlet-prime-sum rate height count count (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision count error) (lw-dirichlet-finite-node-precision count error)))

(local (in-theory (disable lw-complex-dirichlet-finite-value)))

(defthm lw-complex-dirichlet-finite-value-rational
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-dirichlet-finite-value rate height count error)))
 :hints (("Goal"
  :use (lw-dirichlet-finite-precisions-valid
        (:instance lw-complex-dirichlet-prime-sum-rational
         (total count) (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision count error)) (delta (lw-dirichlet-finite-node-precision count error))))
  :in-theory (e/d (lw-complex-dirichlet-finite-value)
    (lw-dirichlet-finite-precisions-valid lw-complex-dirichlet-prime-sum-rational))
  :do-not-induct t)))

(defthm lw-complex-dirichlet-finite-value-cauchy
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-finite-value rate height count left-error) (lw-complex-dirichlet-finite-value rate height count right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-finite-precisions-valid (error left-error))
        (:instance lw-dirichlet-finite-precisions-valid (error right-error))
        (:instance lw-complex-dirichlet-prime-sum-uniform-precision-cauchy (left-total count) (right-total count)
         (left-model-error (lw-dirichlet-finite-model-precision rate height left-error)) (right-model-error (lw-dirichlet-finite-model-precision rate height right-error))
         (left-primitive-error (lw-dirichlet-finite-coefficient-precision count left-error)) (right-primitive-error (lw-dirichlet-finite-coefficient-precision count right-error))
         (left-error (lw-dirichlet-finite-node-precision count left-error)) (right-error (lw-dirichlet-finite-node-precision count right-error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-dirichlet-finite-value rate height count left-error) (lw-complex-dirichlet-finite-value rate height count right-error))) (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (+ (lw-dirichlet-finite-model-precision rate height left-error) (lw-dirichlet-finite-model-precision rate height right-error)))
   (* 16 count (+ 1 count) (+ (lw-dirichlet-finite-node-precision count left-error) (lw-dirichlet-finite-node-precision count right-error)))
   (* 2 count (+ (lw-dirichlet-finite-coefficient-precision count left-error) (lw-dirichlet-finite-coefficient-precision count right-error))))) (cap (+ left-error right-error))))
  :in-theory (e/d (lw-complex-dirichlet-finite-value)
    (lw-dirichlet-finite-precisions-valid lw-complex-dirichlet-prime-sum-uniform-precision-cauchy))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-dirichlet-prime-sum-finite-comparison
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total) (<= count total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta) (lw-complex-dirichlet-finite-value rate height count error)) (+ (* (* 2 (+ rate (abs height))) 1/16 model-error) (* 16 (* count (+ 1 count)) delta) (* 2 count primitive-error) error)))
 :hints (("Goal"
  :use (lw-dirichlet-finite-precisions-valid
        (:instance lw-complex-dirichlet-prime-sum-uniform-precision-cauchy (left-total total) (right-total count)
         (left-model-error model-error) (right-model-error (lw-dirichlet-finite-model-precision rate height error))
         (left-primitive-error primitive-error) (right-primitive-error (lw-dirichlet-finite-coefficient-precision count error))
         (left-error delta) (right-error (lw-dirichlet-finite-node-precision count error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta) (lw-complex-dirichlet-finite-value rate height count error)))
         (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (+ model-error (lw-dirichlet-finite-model-precision rate height error))) (* 16 count (+ 1 count) (+ delta (lw-dirichlet-finite-node-precision count error))) (* 2 count (+ primitive-error (lw-dirichlet-finite-coefficient-precision count error))))) (cap (+ (* (* 2 (+ rate (abs height))) 1/16 model-error) (* 16 (* count (+ 1 count)) delta) (* 2 count primitive-error) error))))
  :in-theory (e/d (lw-complex-dirichlet-finite-value)
    (lw-dirichlet-finite-precisions-valid lw-complex-dirichlet-prime-sum-uniform-precision-cauchy))
  :nonlinearp nil :do-not-induct t)))
