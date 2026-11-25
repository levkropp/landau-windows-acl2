(in-package "ACL2")

(include-book "euler-uniform-polynomial")

; Keep the truncation and the shared point request independently refinable.
; The caller chooses the polynomial degree after choosing that request.

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

(local (in-theory (disable lw-exp-mixturep lw-exp-mixture-common-value
 lw-exp-mixture-affine-polynomial lw-euler-dirichlet-nodes lw-euler-boundary-nodes
 lw-complex-polynomial lw-polynomial-add lw-polynomial-add-constant
 lw-polynomial-multiply-linear lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope)))

(local (in-theory (disable lw-euler-polynomial-argument-cap lw-euler-polynomial-factor-cap
 lw-euler-polynomial-ordinary-error lw-euler-polynomial-rounding-cost lw-euler-polynomial-precision)))

(local (in-theory (disable lw-euler-uniform-polynomial-block lw-euler-uniform-polynomial-count
 lw-euler-uniform-polynomial-request lw-euler-uniform-polynomial)))

(local (defthm lw-erp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erp-times-negative (a b) (b a)))
                 :in-theory (disable lw-erp-times-negative)))))

(local (defthm lw-erp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erp-left-commutes)))))

(local (defthm lw-erp-power-two-natural
 (natp (lw-rational-power 2 index))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-block-prefix-count (block)
 (- (lw-rational-power 2 block) 1))

(local (in-theory (disable lw-euler-block-prefix-count)))

(defthm lw-euler-block-prefix-count-data
 (implies (and (natp block) (<= 2 block))
  (and (natp (lw-rational-power 2 block))
       (<= (+ 1 block) (lw-rational-power 2 block))
       (posp (lw-euler-block-prefix-count block))))
 :hints (("Goal"
  :use ((:instance lw-erp-power-two-natural (index block))
        (:instance lw-rational-power-bernoulli (base 2) (exponent block)))
  :in-theory (union-theories
 '(lw-euler-block-prefix-count lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-refined-polynomial-request (rate height radius block error)
 (min (lw-euler-rounding-precision (lw-euler-disk-transport-cost rate height radius block) (/ error 2))
      (lw-euler-polynomial-precision rate height radius (lw-euler-block-prefix-count block) (/ error 2))))

(local (in-theory (disable lw-euler-refined-polynomial-request)))

(defthm lw-euler-refined-polynomial-request-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-refined-polynomial-request rate height radius block error)) (< 0 (lw-euler-refined-polynomial-request rate height radius block error)) (<= (lw-euler-refined-polynomial-request rate height radius block error) 1)
       (<= (lw-euler-refined-polynomial-request rate height radius block error) (lw-euler-rounding-precision (lw-euler-disk-transport-cost rate height radius block) (/ error 2)))
       (<= (lw-euler-refined-polynomial-request rate height radius block error) (lw-euler-polynomial-precision rate height radius (lw-euler-block-prefix-count block) (/ error 2)))))
 :hints (("Goal"
  :use (lw-euler-block-prefix-count-data
        (:instance lw-euler-disk-constructors-valid (error (/ error 2)))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-disk-transport-cost rate height radius block)) (error (/ error 2)))
        (:instance lw-euler-polynomial-budget-valid (count (lw-euler-block-prefix-count block)) (error (/ error 2))))
  :in-theory (union-theories
 '(lw-euler-refined-polynomial-request min lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-refined-polynomial (rate height radius block request target error)
 (lw-euler-prefix-polynomial rate height (lw-euler-block-prefix-count block) request
  (lw-euler-polynomial-argument-cap rate height radius) target
  (lw-euler-polynomial-ordinary-error rate height radius (/ error 2)) (/ error 8)))

(local (in-theory (disable lw-euler-refined-polynomial)))

(defthm lw-euler-refined-polynomial-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (rationalp request) (< 0 request) (natp block) (<= 2 block) (natp target) (rationalp error) (< 0 error))
  (lw-complex-coefficientsp (lw-euler-refined-polynomial rate height radius block request target error)))
 :hints (("Goal"
  :use (lw-euler-block-prefix-count-data
        lw-euler-polynomial-caps-positive
        (:instance lw-euler-polynomial-budget-valid (error (/ error 2))
         (count (lw-euler-block-prefix-count block)))
        (:instance lw-euler-prefix-polynomial-components-valid
         (count (lw-euler-block-prefix-count block))
         (request request)
         (argument-cap (lw-euler-polynomial-argument-cap rate height radius))
         (ordinary-error (lw-euler-polynomial-ordinary-error rate height radius (/ error 2)))
         (boundary-error (/ error 8))))
  :in-theory (union-theories
   '(lw-euler-refined-polynomial lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-refined-polynomial-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (rationalp request) (< 0 request) (natp block) (<= 2 block) (natp target)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block error))
               (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request target error) point 0)
    (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
   (+ error (* 1/4 value-error))))
 :hints (("Goal"
  :use (lw-euler-block-prefix-count-data lw-euler-refined-polynomial-request-data
        lw-euler-refined-polynomial-valid
        (:instance lw-euler-disk-point-data (offset point))
        (:instance lw-complex-disk-data)
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-refined-polynomial rate height radius block request target error)))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car point))) (height (+ height (cdr point))) (error value-error))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (rate (+ rate (car point))) (height (+ height (cdr point)))
         (count block)
         (error request))
        (:instance lw-complex-euler-prefix-polynomial-computed (error (/ error 2))
         (count (lw-euler-block-prefix-count block))
         (request request))
        (:instance lw-complex-euler-disk-fixed-truncation (offset point) (target-error (/ error 2))
         (error value-error) (block block)
         (request request))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
         (right (lw-complex-euler-dyadic-prefix (+ rate (car point)) (+ height (cdr point))
          block
          request))
         (radius (+ (/ error 2) (* 1/4 value-error))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request target error) point 0))
         (middle (lw-complex-euler-dyadic-prefix (+ rate (car point)) (+ height (cdr point))
          block
          request))
         (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
         (radius (/ error 2)) (other-radius (+ (/ error 2) (* 1/4 value-error)))))
  :in-theory (union-theories
   '(lw-euler-refined-polynomial lw-euler-block-prefix-count lw-complex-euler-dyadic-prefix lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-refined-uniform-comparison-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ left-error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block left-error))
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error margin)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data)
        (:instance lw-euler-disk-point-data (offset point))
        (:instance lw-euler-refined-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-refined-polynomial rate height radius block request left-target left-error)))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius right-target right-error)))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car point))) (height (+ height (cdr point))) (error (* 2 margin)))
        (:instance lw-complex-euler-refined-polynomial-comparison (target left-target) (error left-error)
         (value-error (* 2 margin)))
        (:instance lw-complex-euler-uniform-polynomial-comparison (target right-target) (error right-error)
         (value-error (* 2 margin)))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (* 2 margin))) (radius (+ right-error (* 1/2 margin))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0)) (middle (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (* 2 margin))) (right (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0))
         (radius (+ left-error (* 1/2 margin))) (other-radius (+ right-error (* 1/2 margin)))))
  :in-theory (union-theories
   '( lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-refined-uniform-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (natp block) (<= 2 block) (rationalp request) (< 0 request)
               (<= (lw-euler-disk-block-cutoff rate height radius (/ left-error 2)) block)
               (<= request (lw-euler-refined-polynomial-request rate height radius block left-error))
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error)))
  :use ((:instance lw-complex-disk-data)
        (:instance lw-euler-refined-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-refined-polynomial rate height radius block request left-target left-error)))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius right-target right-error)))
        (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0)) (right (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0))) (radius (+ left-error right-error)) (cost 1))
        (:instance lw-complex-euler-refined-uniform-comparison-with-margin
         (margin (lw-disk-gap-refinement
          (lw-complex-sub (lw-complex-polynomial (lw-euler-refined-polynomial rate height radius block request left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error) 1))))
  :in-theory (union-theories
   '( lw-erp-left-commutes lw-erp-left-distributes lw-erp-fold-constants lw-erp-times-negative lw-erp-negative-times lw-erp-zero-times lw-erp-minus-one lw-erp-double-negative lw-erp-add-cancel lw-erp-double lw-erp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

