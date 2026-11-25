(in-package "ACL2")

(include-book "euler-zeta-prefix")

; One computed dyadic endpoint and point request control both the
; native zeta prefix and the Euler continuation comparison.

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
 lw-dirichlet-native-refinement lw-dirichlet-series-count lw-ceiling-rational
 lw-euler-continuation-cutoff lw-euler-continuation-comparison-cost
 lw-euler-zeta-boundary-cost lw-euler-rounding-precision
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-ezb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ezb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ezb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ezb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ezb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ezb-times-negative)))))

(local (defthm lw-ezb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ezb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ezb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ezb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ezb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ezb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ezb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ezb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ezb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ezb-left-commutes)))))

(defun lw-euler-zeta-comparison-cutoff (rate height euler-error series-error margin)
 (max 2
  (max (lw-euler-continuation-cutoff rate height euler-error)
   (max (lw-dirichlet-series-count series-error) (lw-ceiling-rational (* 2 (/ margin)))))))

(local (in-theory (disable lw-euler-zeta-comparison-cutoff)))

(defthm lw-euler-zeta-comparison-cutoff-brackets
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error) (rationalp margin) (< 0 margin))
  (let ((count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
   (and (natp count) (<= 2 count)
        (<= (lw-euler-continuation-cutoff rate height euler-error) count)
        (<= (lw-dirichlet-series-count series-error) count)
        (<= (* 2 (/ margin)) count))))
 :hints (("Goal"
  :use ((:instance lw-euler-continuation-constructor-data (error euler-error))
        (:instance lw-dirichlet-series-count-valid (error series-error))
        (:instance lw-ceiling-rational-natural (value (* 2 (/ margin))))
        (:instance lw-ceiling-rational-bracket (value (* 2 (/ margin)))))
  :in-theory (union-theories
   '(lw-euler-zeta-comparison-cutoff max lw-ezb-left-commutes lw-ezb-left-distributes lw-ezb-fold-constants lw-ezb-times-negative lw-ezb-negative-times lw-ezb-zero-times lw-ezb-minus-one lw-ezb-double-negative lw-ezb-add-cancel lw-ezb-double lw-ezb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-ezb-power-two-natural
 (natp (lw-rational-power 2 index))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ezb-reciprocal-square-small
 (implies (and (rationalp margin) (< 0 margin) (rationalp index) (<= 1 index)
               (<= (* 2 (/ margin)) index))
  (<= (* 2 (/ index) (/ index)) margin))
 :hints (("Goal"
  :use ((:instance lw-ezb-inverse-factor (divisor margin) (coefficient 2))
        (:instance lw-ezb-multiply-order (a (* 2 (/ margin))) (b index) (factor margin))
        (:instance lw-positive-division-bound (numerator 2) (divisor index) (bound margin))
        (:instance lw-reciprocal-antitone (left 1) (right index))
        (:instance lw-ezb-multiply-order (a (/ index)) (b 1) (factor (* 2 (/ index)))))
  :in-theory (union-theories
   '( lw-ezb-left-commutes lw-ezb-left-distributes lw-ezb-fold-constants lw-ezb-times-negative lw-ezb-negative-times lw-ezb-zero-times lw-ezb-minus-one lw-ezb-double-negative lw-ezb-add-cancel lw-ezb-double lw-ezb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-zeta-comparison-cutoff-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error) (rationalp margin) (< 0 margin))
  (let* ((count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))
         (endpoint (lw-rational-power 2 count)))
   (and (natp count) (<= 2 count)
        (<= (lw-euler-continuation-cutoff rate height euler-error) count)
        (natp endpoint) (<= 3 endpoint) (posp (- endpoint 1))
        (<= (lw-dirichlet-series-count series-error) (- endpoint 1))
        (<= (* 2 (/ endpoint) (/ endpoint)) margin))))
 :hints (("Goal"
  :use (lw-euler-zeta-comparison-cutoff-brackets
        (:instance lw-ezb-power-two-natural
         (index (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
        (:instance lw-rational-power-bernoulli (base 2)
         (exponent (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
        (:instance lw-ezb-reciprocal-square-small
         (index (lw-rational-power 2
          (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))))
  :in-theory (union-theories
   '( lw-ezb-left-commutes lw-ezb-left-distributes lw-ezb-fold-constants lw-ezb-times-negative lw-ezb-negative-times lw-ezb-zero-times lw-ezb-minus-one lw-ezb-double-negative lw-ezb-add-cancel lw-ezb-double lw-ezb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-euler-zeta-comparison-cost (rate height euler-error series-error margin)
 (let ((count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
  (+ (lw-euler-continuation-comparison-cost rate height count euler-error)
     (lw-euler-zeta-boundary-cost rate height (lw-rational-power 2 count)))))

(local (in-theory (disable lw-euler-zeta-comparison-cost)))

(defthm lw-euler-zeta-comparison-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error) (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-zeta-comparison-cost rate height euler-error series-error margin))
       (< 0 (lw-euler-zeta-comparison-cost rate height euler-error series-error margin))))
 :hints (("Goal"
  :use (lw-euler-zeta-comparison-cutoff-data
        (:instance lw-euler-continuation-comparison-cost-valid (error euler-error)
         (count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))
        (:instance lw-euler-zeta-boundary-cost-valid
         (index (lw-rational-power 2
          (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)))))
  :in-theory (union-theories
   '(lw-euler-zeta-comparison-cost lw-ezb-left-commutes lw-ezb-left-distributes lw-ezb-fold-constants lw-ezb-times-negative lw-ezb-negative-times lw-ezb-zero-times lw-ezb-minus-one lw-ezb-double-negative lw-ezb-add-cancel lw-ezb-double lw-ezb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-zeta-comparison-request (rate height euler-error series-error margin)
 (let* ((count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))
        (endpoint (lw-rational-power 2 count))
        (cost (lw-euler-zeta-comparison-cost rate height euler-error series-error margin)))
  (min (lw-dirichlet-native-refinement rate height (- endpoint 1) margin)
       (lw-euler-rounding-precision cost (* 2 margin)))))

(local (in-theory (disable lw-euler-zeta-comparison-request)))

(defthm lw-euler-zeta-comparison-request-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp euler-error) (< 0 euler-error)
               (rationalp series-error) (< 0 series-error) (rationalp margin) (< 0 margin))
  (let* ((count (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin))
         (request (lw-euler-zeta-comparison-request rate height euler-error series-error margin)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= request (lw-dirichlet-native-refinement rate height (- (lw-rational-power 2 count) 1) margin))
        (<= (* (lw-euler-zeta-comparison-cost rate height euler-error series-error margin) request)
            margin))))
 :hints (("Goal"
  :use (lw-euler-zeta-comparison-cutoff-data lw-euler-zeta-comparison-cost-valid
        (:instance lw-dirichlet-native-refinement-valid (error margin)
         (count (- (lw-rational-power 2
          (lw-euler-zeta-comparison-cutoff rate height euler-error series-error margin)) 1)))
        (:instance lw-euler-rounding-precision-valid (error (* 2 margin))
         (cost (lw-euler-zeta-comparison-cost rate height euler-error series-error margin)))
        (:instance lw-ezb-multiply-order
         (a (lw-euler-zeta-comparison-request rate height euler-error series-error margin))
         (b (lw-euler-rounding-precision
              (lw-euler-zeta-comparison-cost rate height euler-error series-error margin) (* 2 margin)))
         (factor (lw-euler-zeta-comparison-cost rate height euler-error series-error margin))))
  :in-theory (union-theories
   '(lw-euler-zeta-comparison-request min lw-ezb-left-commutes lw-ezb-left-distributes lw-ezb-fold-constants lw-ezb-times-negative lw-ezb-negative-times lw-ezb-zero-times lw-ezb-minus-one lw-ezb-double-negative lw-ezb-add-cancel lw-ezb-double lw-ezb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

