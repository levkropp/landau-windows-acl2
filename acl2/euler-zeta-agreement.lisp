(in-package "ACL2")

(include-book "euler-zeta-budget")

; Identification of the actual Euler and pole-removed native zeta names.
; Rational disk-gap refinement removes the last auxiliary error.

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
 lw-complex-zeta-pole-removed-series-value lw-complex-zeta-series-value
 lw-euler-zeta-boundary-cost lw-euler-continuation-cutoff
 lw-euler-continuation-comparison-cost lw-euler-zeta-comparison-cutoff
 lw-euler-zeta-comparison-cost lw-euler-zeta-comparison-request
 lw-euler-rounding-precision lw-disk-gap-refinement
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-eza-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eza-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eza-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eza-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eza-times-negative (a b) (b a)))
                 :in-theory (disable lw-eza-times-negative)))))

(local (defthm lw-eza-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eza-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eza-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eza-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eza-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eza-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eza-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eza-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eza-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eza-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eza-left-commutes)))))

(local (defthm lw-eza-size-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (and (rationalp (abs height)) (<= 0 (abs height))
       (rationalp (+ rate (abs height))) (<= 0 (+ rate (abs height)))))
 :rule-classes nil))

(defthm lw-complex-euler-zeta-agreement-with-margin
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height euler-error)
                   (lw-complex-zeta-pole-removed-series-value rate height series-error))
   (+ (* 1/4 euler-error) (* 3/8 (+ rate (abs height) 1) series-error)
      (* (+ rate (abs height) 3) margin))))
 :hints (("Goal"
  :use (lw-eza-size-data lw-euler-zeta-comparison-cutoff-data lw-euler-zeta-comparison-request-data
        (:instance lw-complex-euler-continuation-value-rational (error euler-error))
        (:instance lw-complex-zeta-pole-removed-series-rational (error series-error))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))
         (error (lw-euler-zeta-comparison-request rate height euler-error series-error margin)))
        (:instance lw-euler-continuation-comparison-cost-valid (error euler-error)
         (count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
        (:instance lw-euler-zeta-boundary-cost-valid
         (index (lw-rational-power 2
          (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))))
        (:instance lw-complex-euler-continuation-prefix-comparison (error euler-error)
         (count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))
         (request (lw-euler-zeta-comparison-request rate height euler-error series-error margin)))
        (:instance lw-complex-euler-prefix-zeta-series-comparison (error series-error)
         (count (- (lw-rational-power 2
          (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)) 1))
         (target-error margin)
         (request (lw-euler-zeta-comparison-request rate height euler-error series-error margin)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-continuation-value rate height euler-error))
         (middle (lw-complex-euler-dyadic-prefix rate height
          (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)
          (lw-euler-zeta-comparison-request rate height euler-error series-error margin)))
         (right (lw-complex-zeta-pole-removed-series-value rate height series-error))
         (radius
          (+ (* 1/4 euler-error)
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin) euler-error)
                (lw-euler-zeta-comparison-request rate height euler-error series-error margin))))
         (other-radius
          (+ (* (+ rate (abs height) 1) (+ (* 3/8 series-error) margin))
             (* 2 (/ (lw-rational-power 2
                       (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
                  (/ (lw-rational-power 2
                       (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))))
             (* (lw-euler-zeta-boundary-cost rate height
                 (lw-rational-power 2
                  (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
                (lw-euler-zeta-comparison-request rate height euler-error series-error margin)))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height euler-error)
                                (lw-complex-zeta-pole-removed-series-value rate height series-error)))
         (radius
          (+ (* 1/4 euler-error)
             (* (lw-euler-continuation-comparison-cost rate height
                 (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin) euler-error)
                (lw-euler-zeta-comparison-request rate height euler-error series-error margin))
             (* (+ rate (abs height) 1) (+ (* 3/8 series-error) margin))
             (* 2 (/ (lw-rational-power 2
                       (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
                  (/ (lw-rational-power 2
                       (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))))
             (* (lw-euler-zeta-boundary-cost rate height
                 (lw-rational-power 2
                  (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
                (lw-euler-zeta-comparison-request rate height euler-error series-error margin))))
         (cap (+ (* 1/4 euler-error) (* 3/8 (+ rate (abs height) 1) series-error)
                 (* (+ rate (abs height) 3) margin)))))
  :in-theory (union-theories
   '(lw-complex-euler-dyadic-prefix lw-euler-zeta-comparison-cost lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-zeta-series-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height euler-error)
                   (lw-complex-zeta-pole-removed-series-value rate height series-error))
   (+ (* 1/4 euler-error) (* 3/8 (+ rate (abs height) 1) series-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value rate height euler-error)
                   (lw-complex-zeta-pole-removed-series-value rate height series-error))
   (+ (* 1/4 euler-error) (* 3/8 (+ rate (abs height) 1) series-error))))
  :use (lw-eza-size-data
        (:instance lw-complex-euler-continuation-value-rational (error euler-error))
        (:instance lw-complex-zeta-pole-removed-series-rational (error series-error))
        (:instance lw-complex-operations-rational
         (left (lw-complex-euler-continuation-value rate height euler-error))
         (right (lw-complex-zeta-pole-removed-series-value rate height series-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-continuation-value rate height euler-error)
                                (lw-complex-zeta-pole-removed-series-value rate height series-error)))
         (radius (+ (* 1/4 euler-error) (* 3/8 (+ rate (abs height) 1) series-error)))
         (cost (+ rate (abs height) 3)))
        (:instance lw-complex-euler-zeta-agreement-with-margin
         (margin (lw-disk-gap-refinement
          (lw-complex-sub (lw-complex-euler-continuation-value rate height euler-error)
                          (lw-complex-zeta-pole-removed-series-value rate height series-error))
          (+ (* 1/4 euler-error) (* 3/8 (+ rate (abs height) 1) series-error))
          (+ rate (abs height) 3)))))
  :in-theory (union-theories
   '( lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defun lw-euler-zeta-agreement-precision (rate height error)
 (lw-euler-rounding-precision (+ 1/4 (* 3/8 (+ rate (abs height) 1))) error))

(local (in-theory (disable lw-euler-zeta-agreement-precision)))

(defthm lw-euler-zeta-agreement-precision-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((request (lw-euler-zeta-agreement-precision rate height error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= (+ (* 1/4 request) (* 3/8 (+ rate (abs height) 1) request)) error))))
 :hints (("Goal"
  :use (lw-eza-size-data
        (:instance lw-euler-rounding-precision-valid
         (cost (+ 1/4 (* 3/8 (+ rate (abs height) 1))))))
  :in-theory (union-theories
   '(lw-euler-zeta-agreement-precision lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-zeta-computed-agreement
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (let ((request (lw-euler-zeta-agreement-precision rate height error)))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-euler-continuation-value rate height request)
                    (lw-complex-zeta-pole-removed-series-value rate height request))
    error)))
 :hints (("Goal"
  :use (lw-euler-zeta-agreement-precision-valid
        (:instance lw-complex-euler-zeta-series-agreement
         (euler-error (lw-euler-zeta-agreement-precision rate height error))
         (series-error (lw-euler-zeta-agreement-precision rate height error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-euler-continuation-value rate height (lw-euler-zeta-agreement-precision rate height error))
          (lw-complex-zeta-pole-removed-series-value rate height (lw-euler-zeta-agreement-precision rate height error))))
         (radius (+ (* 1/4 (lw-euler-zeta-agreement-precision rate height error))
                    (* 3/8 (+ rate (abs height) 1) (lw-euler-zeta-agreement-precision rate height error))))
         (cap error)))
  :in-theory (union-theories
   '( lw-eza-left-commutes lw-eza-left-distributes lw-eza-fold-constants lw-eza-times-negative lw-eza-negative-times lw-eza-zero-times lw-eza-minus-one lw-eza-double-negative lw-eza-add-cancel lw-eza-double lw-eza-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

