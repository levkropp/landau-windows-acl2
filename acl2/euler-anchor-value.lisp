(in-package "ACL2")

(include-book "euler-anchor-exponential")
(include-book "euler-fixed-truncation")
(include-book "complex-exp-negative")

; Calibrate the pole-removed Euler evaluator at the real anchor.
; The endpoint error is removed by an explicit rational gap argument.

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
(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))

(local (defthm lw-eav-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eav-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eav-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eav-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eav-times-negative (a b) (b a)))
                 :in-theory (disable lw-eav-times-negative)))))

(local (defthm lw-eav-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eav-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eav-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eav-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eav-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eav-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eav-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eav-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eav-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eav-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eav-left-commutes)))))

(defun lw-euler-anchor-node-cost (index)
 (+ (lw-complex-log-ramp-cap 1 0 index) 4
    (* 2 (lw-exp-lipschitz-cap index))))

(local (in-theory (disable lw-euler-anchor-node-cost)))

(defthm lw-euler-anchor-node-cost-valid
 (implies (and (rationalp index) (< 1 index))
  (and (rationalp (lw-euler-anchor-node-cost index))
       (< 0 (lw-euler-anchor-node-cost index))))
 :hints (("Goal"
  :use ((:instance lw-complex-exp-uniform-cap-data (argument-cap index))
        (:instance lw-exp-lipschitz-cap-valid (cap index)))
  :in-theory (union-theories
 '(lw-euler-anchor-node-cost lw-complex-log-ramp-cap abs lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-anchor-endpoint
 (implies (and (rationalp index) (< 1 index)
               (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-scale index (lw-dirichlet-sample 1 0 index request request))
    (cons 1 0))
   (* (lw-euler-anchor-node-cost index) request)))
 :hints (("Goal"
  :use ((:instance lw-euler-anchor-exponential-normalization
         (rate 1) (height 0) (log-error request) (delta request))
        (:instance lw-dirichlet-sample-rational
         (rate 1) (height 0) (log-error request) (node-error request))
        (:instance lw-complex-operations-rational
         (left (lw-dirichlet-sample 1 0 index request request))
         (right (cons 1 0)) (factor index))
        (:instance lw-complex-exp-value-zero (error request))
        (:instance lw-complex-difference-symmetric
         (left (cons 1 0))
         (right (lw-complex-scale index (lw-dirichlet-sample 1 0 index request request)))
         (radius (* (lw-euler-anchor-node-cost index) request))))
  :in-theory (union-theories
 '(lw-euler-anchor-node-cost lw-complex-log-ramp-independent-exp lw-dirichlet-sample lw-complex-scale lw-complex-laplace-point (:executable-counterpart lw-complexp) lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(local (defthm lw-eav-prefix-at-one
 (equal (lw-complex-euler-dirichlet-prefix 1 0 count request)
        (lw-complex-scale (+ 1 count) (lw-dirichlet-sample 1 0 (+ 1 count) request request)))
 :hints (("Goal"
  :in-theory (union-theories
 '(lw-complex-euler-dirichlet-prefix lw-complex-add lw-complex-mul lw-complex-scale lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-eav-power-data
 (implies (and (natp block) (<= 2 block))
  (and (rationalp (lw-rational-power 2 block))
       (< 1 (lw-rational-power 2 block))))
 :hints (("Goal"
  :use ((:instance lw-rational-power-bernoulli (base 2) (exponent block))
        (:instance lw-rational-power-rational (base 2) (exponent block)))
  :in-theory (union-theories
 '( lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defun lw-euler-anchor-request (block margin)
 (min
  (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost 1 0 block) margin)
  (lw-euler-rounding-precision (lw-euler-anchor-node-cost (lw-rational-power 2 block)) margin)))

(local (in-theory (disable lw-euler-anchor-request)))

(defthm lw-euler-anchor-request-valid
 (implies (and (natp block) (<= 2 block) (rationalp margin) (< 0 margin))
  (let ((request (lw-euler-anchor-request block margin)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= request (lw-euler-rounding-precision (lw-euler-dyadic-transport-cost 1 0 block) margin))
        (<= (* (lw-euler-anchor-node-cost (lw-rational-power 2 block)) request) (/ margin 2)))))
 :hints (("Goal"
  :use (lw-eav-power-data
        (:instance lw-euler-dyadic-transport-cost-valid (rate 1) (height 0) (count block))
        (:instance lw-euler-anchor-node-cost-valid (index (lw-rational-power 2 block)))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-dyadic-transport-cost 1 0 block)) (error margin))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-anchor-node-cost (lw-rational-power 2 block))) (error margin))
        (:instance lw-eav-multiply-order
         (a (lw-euler-anchor-request block margin))
         (b (lw-euler-rounding-precision (lw-euler-anchor-node-cost (lw-rational-power 2 block)) margin))
         (factor (lw-euler-anchor-node-cost (lw-rational-power 2 block)))))
  :in-theory (union-theories
 '(lw-euler-anchor-request min lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eav-dyadic-endpoint
 (implies (and (natp block) (<= 2 block) (rationalp margin) (< 0 margin))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-dyadic-prefix 1 0 block (lw-euler-anchor-request block margin)) (cons 1 0))
   (/ margin 2)))
 :hints (("Goal"
  :use (lw-eav-power-data lw-euler-anchor-request-valid
        (:instance lw-euler-anchor-endpoint
         (index (lw-rational-power 2 block)) (request (lw-euler-anchor-request block margin)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-dyadic-prefix 1 0 block (lw-euler-anchor-request block margin)) (cons 1 0)))
         (radius (* (lw-euler-anchor-node-cost (lw-rational-power 2 block)) (lw-euler-anchor-request block margin)))
         (cap (/ margin 2))))
  :in-theory (union-theories
 '(lw-complex-euler-dyadic-prefix lw-eav-prefix-at-one lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-eav-value-with-prefix
 (implies (and (rationalp error) (< 0 error) (rationalp margin) (< 0 margin)
               (natp block) (<= 2 block)
               (<= (lw-euler-continuation-block-cutoff 1 0 margin) block))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0))
   (+ (* 1/4 error) (* 3/2 margin))))
 :hints (("Goal"
  :use (lw-euler-anchor-request-valid lw-eav-dyadic-endpoint
        (:instance lw-complex-euler-continuation-value-rational (rate 1) (height 0))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (rate 1) (height 0) (count block) (error (lw-euler-anchor-request block margin)))
        (:instance lw-complex-euler-fixed-truncation-computed
         (rate 1) (height 0) (target-error margin) (request (lw-euler-anchor-request block margin)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-continuation-value 1 0 error))
         (middle (lw-complex-euler-dyadic-prefix 1 0 block (lw-euler-anchor-request block margin)))
         (right (cons 1 0)) (radius (+ (* 1/4 error) margin)) (other-radius (/ margin 2)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0)))
         (radius (+ (* 1/4 error) margin (/ margin 2)))
         (cap (+ (* 1/4 error) (* 3/2 margin)))))
  :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-eav-value-with-margin
 (implies (and (rationalp error) (< 0 error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0))
   (+ (* 1/4 error) (* 3/2 margin))))
 :hints (("Goal"
  :use ((:instance lw-euler-continuation-block-cutoff-natural (rate 1) (height 0) (error margin))
        (:instance lw-eav-value-with-prefix (block (lw-euler-continuation-block-cutoff 1 0 margin))))
  :in-theory (union-theories
 '( lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-anchor-value
 (implies (and (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0))
   (* 1/4 error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0))
   (* 1/4 error)))
  :use ((:instance lw-complex-euler-continuation-value-rational (rate 1) (height 0))
        (:instance lw-complex-operations-rational
         (left (lw-complex-euler-continuation-value 1 0 error)) (right (cons 1 0)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0)))
         (radius (* 1/4 error)) (cost 3/2))
        (:instance lw-eav-value-with-margin
         (margin (lw-disk-gap-refinement
          (lw-complex-sub (lw-complex-euler-continuation-value 1 0 error) (cons 1 0))
          (* 1/4 error) 3/2))))
  :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-eav-left-commutes lw-eav-left-distributes lw-eav-fold-constants lw-eav-times-negative lw-eav-negative-times lw-eav-zero-times lw-eav-minus-one lw-eav-double-negative lw-eav-add-cancel lw-eav-double lw-eav-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



