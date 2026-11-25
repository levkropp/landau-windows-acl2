(in-package "ACL2")

(include-book "euler-continuation")
(include-book "dirichlet-series-product")

; Compare actual Euler prefixes with the native pole-removed zeta series.
; The upper boundary and all point errors remain explicit.

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
 lw-complex-common-dirichlet-prefix lw-complex-common-native-series
 lw-complex-zeta-series-value lw-dirichlet-sample lw-dirichlet-cubic-node-cost
 lw-dirichlet-native-refinement lw-dirichlet-series-count
 lw-euler-continuation-cutoff lw-euler-continuation-comparison-cost
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-ezp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ezp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ezp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ezp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ezp-times-negative (a b) (b a)))
                 :in-theory (disable lw-ezp-times-negative)))))

(local (defthm lw-ezp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ezp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ezp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ezp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ezp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ezp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ezp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ezp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ezp-left-commutes)))))

(local (defthm lw-ezp-size-data
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (and (rationalp (abs height)) (<= 0 (abs height))
       (rationalp (+ rate (abs height))) (<= 0 (+ rate (abs height)))))
 :rule-classes nil))

(defthm lw-complex-zeta-shifted-point-cap
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height))
  (lw-complex-diskp (cons (- rate 1) height) (+ rate (abs height) 1)))
 :hints (("Goal"
  :cases ((<= 1 rate))
  :use ((:instance lw-complex-l1-bound (point (cons (- rate 1) height)))
        (:instance lw-complex-disk-enlarge
         (point (cons (- rate 1) height)) (radius (+ (abs (- rate 1)) (abs height)))
         (cap (+ rate (abs height) 1))))
  :in-theory (union-theories
   '(lw-complexp lw-complex-l1 abs lw-ezp-left-commutes lw-ezp-left-distributes lw-ezp-fold-constants lw-ezp-times-negative lw-ezp-negative-times lw-ezp-zero-times lw-ezp-minus-one lw-ezp-double-negative lw-ezp-add-cancel lw-ezp-double lw-ezp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-euler-zeta-boundary-cost (rate height index)
 (+ (lw-dirichlet-cubic-node-cost rate height index)
    (* 6 (lw-exp-lipschitz-cap index))))

(local (in-theory (disable lw-euler-zeta-boundary-cost)))

(defthm lw-euler-zeta-boundary-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp index) (< 1 index))
  (and (rationalp (lw-euler-zeta-boundary-cost rate height index))
       (< 0 (lw-euler-zeta-boundary-cost rate height index))))
 :hints (("Goal"
  :use (lw-dirichlet-cubic-node-cost-valid (:instance lw-exp-lipschitz-cap-valid (cap index)))
  :in-theory (union-theories
   '(lw-euler-zeta-boundary-cost lw-ezp-left-commutes lw-ezp-left-distributes lw-ezp-fold-constants lw-ezp-times-negative lw-ezp-negative-times lw-ezp-zero-times lw-ezp-minus-one lw-ezp-double-negative lw-ezp-add-cancel lw-ezp-double lw-ezp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-zeta-pole-removed-series-value (rate height error)
 (lw-complex-mul (cons (- rate 1) height)
  (lw-complex-zeta-series-value nil rate height error)))

(local (in-theory (disable lw-complex-zeta-pole-removed-series-value)))

(defthm lw-complex-zeta-pole-removed-series-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-pole-removed-series-value rate height error)))
 :hints (("Goal"
  :use ((:instance lw-complex-zeta-series-value-rational (logp nil))
        (:instance lw-complex-operations-rational
         (left (cons (- rate 1) height)) (right (lw-complex-zeta-series-value nil rate height error)) (factor 1)))
  :in-theory (union-theories
   '(lw-complex-zeta-pole-removed-series-value lw-complexp lw-ezp-left-commutes lw-ezp-left-distributes lw-ezp-fold-constants lw-ezp-times-negative lw-ezp-negative-times lw-ezp-zero-times lw-ezp-minus-one lw-ezp-double-negative lw-ezp-add-cancel lw-ezp-double lw-ezp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ezp-mul-difference
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-mul point left) (lw-complex-mul point right))
         (lw-complex-mul point (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-mul)
                 :do-not-induct t)) :rule-classes nil))

(defthm lw-complex-zeta-pole-removed-series-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-zeta-pole-removed-series-value rate height left-error)
                   (lw-complex-zeta-pole-removed-series-value rate height right-error))
   (* (+ rate (abs height) 1) (+ left-error right-error))))
 :hints (("Goal"
  :use (lw-ezp-size-data lw-complex-zeta-shifted-point-cap
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error left-error))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error right-error))
        (:instance lw-complex-zeta-series-value-cauchy (logp nil))
        (:instance lw-ezp-mul-difference (point (cons (- rate 1) height))
         (left (lw-complex-zeta-series-value nil rate height left-error))
         (right (lw-complex-zeta-series-value nil rate height right-error)))
        (:instance lw-complex-mul-disk
         (left (cons (- rate 1) height))
         (right (lw-complex-sub (lw-complex-zeta-series-value nil rate height left-error)
                                (lw-complex-zeta-series-value nil rate height right-error)))
         (radius (+ rate (abs height) 1)) (other-radius (+ left-error right-error))))
  :in-theory (union-theories
   '(lw-complex-zeta-pole-removed-series-value lw-complexp lw-ezp-left-commutes lw-ezp-left-distributes lw-ezp-fold-constants lw-ezp-times-negative lw-ezp-negative-times lw-ezp-zero-times lw-ezp-minus-one lw-ezp-double-negative lw-ezp-add-cancel lw-ezp-double lw-ezp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-ezp-prefix-residual
 (implies (and (lw-complexp point) (lw-complexp left) (lw-complexp right) (lw-complexp boundary))
  (equal
   (lw-complex-sub (lw-complex-add (lw-complex-mul point left) boundary)
                   (lw-complex-mul point right))
   (lw-complex-add (lw-complex-mul point (lw-complex-sub left right)) boundary)))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul)
                 :do-not-induct t)) :rule-classes nil))

(defthm lw-complex-euler-prefix-zeta-series-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count)
               (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
               (rationalp target-error) (< 0 target-error)
               (rationalp request) (< 0 request) (<= request 1)
               (<= request (lw-dirichlet-native-refinement rate height count target-error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-dirichlet-prefix rate height count request)
                   (lw-complex-zeta-pole-removed-series-value rate height error))
   (+ (* (+ rate (abs height) 1) (+ (* 3/8 error) target-error))
      (* 2 (/ (+ 1 count)) (/ (+ 1 count)))
      (* (lw-euler-zeta-boundary-cost rate height (+ 1 count)) request))))
 :hints (("Goal"
  :use (lw-ezp-size-data lw-complex-zeta-shifted-point-cap
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (error request))
        (:instance lw-complex-zeta-series-value-rational (logp nil))
        (:instance lw-complex-log-ramp-independent-exp-rational
         (index (+ 1 count)) (log-error request) (delta request))
        (:instance lw-complex-scale-rational
         (point (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request))
         (factor (+ 1 count)))
        (:instance lw-complex-common-prefix-series-computed-comparison (mangoldtp nil) (logp nil))
        (:instance lw-complex-dirichlet-cubic-point-bound
         (index (+ 1 count)) (weight (+ 1 count)) (log-error request) (error request))
        (:instance lw-ezp-prefix-residual
         (point (cons (- rate 1) height))
         (left (lw-complex-common-dirichlet-prefix nil nil rate height count request))
         (right (lw-complex-zeta-series-value nil rate height error))
         (boundary (lw-complex-scale (+ 1 count)
          (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request))))
        (:instance lw-complex-mul-disk
         (left (cons (- rate 1) height))
         (right (lw-complex-sub (lw-complex-common-dirichlet-prefix nil nil rate height count request)
                                (lw-complex-zeta-series-value nil rate height error)))
         (radius (+ rate (abs height) 1)) (other-radius (+ (* 3/8 error) target-error)))
        (:instance lw-complex-add-disk
         (left (lw-complex-mul (cons (- rate 1) height)
          (lw-complex-sub (lw-complex-common-dirichlet-prefix nil nil rate height count request)
                          (lw-complex-zeta-series-value nil rate height error))))
         (right (lw-complex-scale (+ 1 count)
          (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request)))
         (radius (* (+ rate (abs height) 1) (+ (* 3/8 error) target-error)))
         (other-radius
          (+ (* 2 (/ (+ 1 count)) (/ (+ 1 count)))
             (* (lw-dirichlet-cubic-node-cost rate height (+ 1 count)) request)
             (* 6 (lw-exp-lipschitz-cap (+ 1 count)) request)))))
  :in-theory (union-theories
   '(lw-complex-euler-dirichlet-prefix lw-dirichlet-sample lw-complex-common-native-series lw-complex-zeta-pole-removed-series-value lw-euler-zeta-boundary-cost lw-complexp lw-ezp-left-commutes lw-ezp-left-distributes lw-ezp-fold-constants lw-ezp-times-negative lw-ezp-negative-times lw-ezp-zero-times lw-ezp-minus-one lw-ezp-double-negative lw-ezp-add-cancel lw-ezp-double lw-ezp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

