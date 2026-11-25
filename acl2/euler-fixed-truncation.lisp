(in-package "ACL2")

(include-book "zeta-euler-value")

; Compare any requested Euler value with one fixed dyadic prefix.
; The prefix cutoff is independent of that value's internal accuracy.

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

(local (in-theory (disable lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope
 lw-complex-euler-dyadic-prefix lw-complex-euler-continuation-value
 lw-euler-continuation-cutoff lw-euler-continuation-comparison-cost
 lw-euler-continuation-tail-cap lw-euler-dyadic-tail-rounding
 lw-euler-dyadic-transport-cost lw-euler-rounding-precision lw-disk-gap-refinement
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-eft-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eft-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eft-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eft-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eft-times-negative (a b) (b a)))
                 :in-theory (disable lw-eft-times-negative)))))

(local (defthm lw-eft-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eft-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eft-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eft-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eft-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eft-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eft-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eft-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eft-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eft-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eft-left-commutes)))))

(defun lw-euler-truncation-common-count (rate height block error)
 (max block (lw-euler-continuation-cutoff rate height error)))

(local (in-theory (disable lw-euler-truncation-common-count)))

(defthm lw-euler-truncation-common-count-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp block) (<= 2 block) (rationalp error) (< 0 error))
  (let ((count (lw-euler-truncation-common-count rate height block error)))
   (and (natp count) (<= 2 count) (<= block count)
        (<= (lw-euler-continuation-cutoff rate height error) count))))
 :hints (("Goal"
  :use (lw-euler-continuation-constructor-data)
  :in-theory (union-theories
   '(lw-euler-truncation-common-count max lw-eft-left-commutes lw-eft-left-distributes lw-eft-fold-constants lw-eft-times-negative lw-eft-negative-times lw-eft-zero-times lw-eft-minus-one lw-eft-double-negative lw-eft-add-cancel lw-eft-double lw-eft-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-truncation-common-cost (rate height block error)
 (let ((count (lw-euler-truncation-common-count rate height block error)))
  (+ (lw-euler-continuation-comparison-cost rate height count error)
     (lw-euler-dyadic-tail-rounding rate height count block)
     (lw-euler-dyadic-transport-cost rate height block))))

(defun lw-euler-truncation-refinement (rate height block error margin)
 (lw-euler-rounding-precision (lw-euler-truncation-common-cost rate height block error) (* 2 margin)))

(local (in-theory (disable lw-euler-truncation-common-cost lw-euler-truncation-refinement)))

(defthm lw-euler-truncation-refinement-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (natp block) (<= 2 block)
               (rationalp error) (< 0 error) (rationalp margin) (< 0 margin))
  (let ((cost (lw-euler-truncation-common-cost rate height block error))
        (request (lw-euler-truncation-refinement rate height block error margin)))
   (and (rationalp cost) (< 0 cost) (rationalp request) (< 0 request) (<= request 1)
        (<= (* cost request) margin))))
 :hints (("Goal"
  :use (lw-euler-truncation-common-count-data
        (:instance lw-euler-continuation-comparison-cost-valid
         (count (lw-euler-truncation-common-count rate height block error)))
        (:instance lw-euler-dyadic-tail-rounding-nonnegative
         (count (lw-euler-truncation-common-count rate height block error)) (start block))
        (:instance lw-euler-dyadic-transport-cost-valid (count block))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-truncation-common-cost rate height block error)) (error (* 2 margin))))
  :in-theory (union-theories
   '(lw-euler-truncation-common-cost lw-euler-truncation-refinement lw-eft-left-commutes lw-eft-left-distributes lw-eft-fold-constants lw-eft-times-negative lw-eft-negative-times lw-eft-zero-times lw-eft-minus-one lw-eft-double-negative lw-eft-add-cancel lw-eft-double lw-eft-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-fixed-truncation-with-margin
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp block) (<= 2 block) (<= (+ rate (abs height)) (lw-rational-power 2 block))
               (rationalp error) (< 0 error) (rationalp request) (< 0 request)
               (rationalp margin) (< 0 margin))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                   (lw-complex-euler-dyadic-prefix rate height block request))
   (+ (* 1/4 error)
      (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
      (* (lw-euler-dyadic-transport-cost rate height block) request) margin)))
 :hints (("Goal"
  :use (lw-euler-truncation-common-count-data lw-euler-truncation-refinement-data
        lw-complex-euler-continuation-value-rational lw-euler-continuation-tail-cap-valid
        lw-euler-dirichlet-cell-cap-valid
        (:instance lw-euler-dyadic-transport-cost-valid (count block))
        (:instance lw-euler-continuation-comparison-cost-valid
         (count (lw-euler-truncation-common-count rate height block error)))
        (:instance lw-euler-dyadic-tail-rounding-nonnegative
         (count (lw-euler-truncation-common-count rate height block error)) (start block))
        (:instance lw-complex-euler-dyadic-prefix-rational (count block) (error request))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (count block) (error (lw-euler-truncation-refinement rate height block error margin)))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (count (lw-euler-truncation-common-count rate height block error))
         (error (lw-euler-truncation-refinement rate height block error margin)))
        (:instance lw-complex-euler-continuation-prefix-comparison
         (count (lw-euler-truncation-common-count rate height block error))
         (request (lw-euler-truncation-refinement rate height block error margin)))
        (:instance lw-complex-euler-dyadic-prefix-tail-bound
         (count (lw-euler-truncation-common-count rate height block error)) (start block)
         (error (lw-euler-truncation-refinement rate height block error margin)))
        (:instance lw-complex-euler-dyadic-prefix-precision-cauchy (count block)
         (left-error (lw-euler-truncation-refinement rate height block error margin)) (right-error request))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-continuation-value rate height error))
         (middle (lw-complex-euler-dyadic-prefix rate height
          (lw-euler-truncation-common-count rate height block error)
          (lw-euler-truncation-refinement rate height block error margin)))
         (right (lw-complex-euler-dyadic-prefix rate height block
          (lw-euler-truncation-refinement rate height block error margin)))
         (radius (+ (* 1/4 error)
          (* (lw-euler-continuation-comparison-cost rate height
              (lw-euler-truncation-common-count rate height block error) error)
             (lw-euler-truncation-refinement rate height block error margin))))
         (other-radius
          (+ (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
             (* (lw-euler-dyadic-tail-rounding rate height
                 (lw-euler-truncation-common-count rate height block error) block)
                (lw-euler-truncation-refinement rate height block error margin)))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-continuation-value rate height error))
         (middle (lw-complex-euler-dyadic-prefix rate height block
          (lw-euler-truncation-refinement rate height block error margin)))
         (right (lw-complex-euler-dyadic-prefix rate height block request))
         (radius (+ (* 1/4 error)
          (* (lw-euler-continuation-comparison-cost rate height
              (lw-euler-truncation-common-count rate height block error) error)
             (lw-euler-truncation-refinement rate height block error margin))
          (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
          (* (lw-euler-dyadic-tail-rounding rate height
              (lw-euler-truncation-common-count rate height block error) block)
             (lw-euler-truncation-refinement rate height block error margin))))
         (other-radius (* (lw-euler-dyadic-transport-cost rate height block)
          (+ (lw-euler-truncation-refinement rate height block error margin) request))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                                (lw-complex-euler-dyadic-prefix rate height block request)))
         (radius (+ (* 1/4 error)
          (* (lw-euler-continuation-comparison-cost rate height
              (lw-euler-truncation-common-count rate height block error) error)
             (lw-euler-truncation-refinement rate height block error margin))
          (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
          (* (lw-euler-dyadic-tail-rounding rate height
              (lw-euler-truncation-common-count rate height block error) block)
             (lw-euler-truncation-refinement rate height block error margin))
          (* (lw-euler-dyadic-transport-cost rate height block)
             (+ (lw-euler-truncation-refinement rate height block error margin) request))))
         (cap (+ (* 1/4 error)
          (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
          (* (lw-euler-dyadic-transport-cost rate height block) request) margin))))
  :in-theory (union-theories
   '(lw-euler-truncation-common-cost lw-euler-continuation-tail-cap lw-eft-left-commutes lw-eft-left-distributes lw-eft-fold-constants lw-eft-times-negative lw-eft-negative-times lw-eft-zero-times lw-eft-minus-one lw-eft-double-negative lw-eft-add-cancel lw-eft-double lw-eft-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-fixed-truncation
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp block) (<= 2 block) (<= (+ rate (abs height)) (lw-rational-power 2 block))
               (rationalp error) (< 0 error) (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                   (lw-complex-euler-dyadic-prefix rate height block request))
   (+ (* 1/4 error)
      (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
      (* (lw-euler-dyadic-transport-cost rate height block) request))))
 :hints (("Goal"
  :cases ((lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                   (lw-complex-euler-dyadic-prefix rate height block request))
   (+ (* 1/4 error) (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
      (* (lw-euler-dyadic-transport-cost rate height block) request))))
  :use (lw-complex-euler-continuation-value-rational lw-euler-continuation-tail-cap-valid
        (:instance lw-euler-dyadic-transport-cost-valid (count block))
        (:instance lw-complex-euler-dyadic-prefix-rational (count block) (error request))
        (:instance lw-complex-operations-rational
         (left (lw-complex-euler-continuation-value rate height error))
         (right (lw-complex-euler-dyadic-prefix rate height block request)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                                (lw-complex-euler-dyadic-prefix rate height block request)))
         (radius (+ (* 1/4 error) (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
                    (* (lw-euler-dyadic-transport-cost rate height block) request)))
         (cost 1))
        (:instance lw-complex-euler-fixed-truncation-with-margin
         (margin (lw-disk-gap-refinement
          (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                          (lw-complex-euler-dyadic-prefix rate height block request))
          (+ (* 1/4 error) (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
             (* (lw-euler-dyadic-transport-cost rate height block) request)) 1))))
  :in-theory (union-theories
   '( lw-eft-left-commutes lw-eft-left-distributes lw-eft-fold-constants lw-eft-times-negative lw-eft-negative-times lw-eft-zero-times lw-eft-minus-one lw-eft-double-negative lw-eft-add-cancel lw-eft-double lw-eft-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-euler-fixed-truncation-computed
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp error) (< 0 error) (rationalp target-error) (< 0 target-error)
               (natp block) (<= (lw-euler-continuation-block-cutoff rate height target-error) block)
               (rationalp request) (< 0 request)
               (<= request (lw-euler-rounding-precision
                (lw-euler-dyadic-transport-cost rate height block) target-error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                   (lw-complex-euler-dyadic-prefix rate height block request))
   (+ (* 1/4 error) target-error)))
 :hints (("Goal"
  :use ((:instance lw-euler-continuation-tail-cutoff-sufficient (error target-error) (start block))
        (:instance lw-euler-dyadic-transport-cost-valid (count block))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-dyadic-transport-cost rate height block)) (error target-error))
        (:instance lw-eft-multiply-order
         (a request)
         (b (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost rate height block) target-error))
         (factor (lw-euler-dyadic-transport-cost rate height block)))
        lw-complex-euler-fixed-truncation
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height error)
                                (lw-complex-euler-dyadic-prefix rate height block request)))
         (radius (+ (* 1/4 error) (* (lw-euler-continuation-tail-cap rate height) (/ (- block 1)))
                    (* (lw-euler-dyadic-transport-cost rate height block) request)))
         (cap (+ (* 1/4 error) target-error))))
  :in-theory (union-theories
   '( lw-eft-left-commutes lw-eft-left-distributes lw-eft-fold-constants lw-eft-times-negative lw-eft-negative-times lw-eft-zero-times lw-eft-minus-one lw-eft-double-negative lw-eft-add-cancel lw-eft-double lw-eft-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

