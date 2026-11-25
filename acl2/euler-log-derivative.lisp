(in-package "ACL2")

(include-book "euler-value-clearance")

; Construct V'/V from the actual coefficient and value Cauchy names.
; A checked coarse value supplies the denominator bounds at every request.

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

(local (in-theory (disable lw-complex-euler-continuation-value
 lw-complex-euler-local-coefficient-value lw-euler-uniform-coefficient-cap
 lw-euler-value-clearance-size lw-euler-value-clearance-lower
 lw-euler-value-clearance-check lw-complex-quotient)))

(local (defthm lw-eld-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eld-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eld-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eld-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eld-times-negative (a b) (b a)))
                 :in-theory (disable lw-eld-times-negative)))))

(local (defthm lw-eld-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eld-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eld-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eld-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eld-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eld-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eld-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eld-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eld-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eld-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eld-left-commutes)))))

(defun lw-euler-log-derivative-numerator-cap (rate height radius)
 (* (lw-euler-uniform-coefficient-cap rate height radius) (/ radius)))

(local (in-theory (disable lw-euler-log-derivative-numerator-cap)))

(defthm lw-euler-log-derivative-numerator-cap-data
 (implies (and (rationalp rate) (rationalp height)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-log-derivative-numerator-cap rate height radius)) (< 0 (lw-euler-log-derivative-numerator-cap rate height radius))
       (lw-complex-diskp (lw-complex-euler-local-coefficient-value rate height radius 1 error) (lw-euler-log-derivative-numerator-cap rate height radius))))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid
        (:instance lw-complex-euler-local-coefficient-cap (index 1))
        (:instance lw-reciprocal-positive (value radius))
        (:instance lw-eld-positive-product
         (a (lw-euler-uniform-coefficient-cap rate height radius)) (b (/ radius))))
  :expand ((lw-rational-power radius 1) (lw-rational-power radius 0))
  :in-theory (union-theories
 '(lw-euler-log-derivative-numerator-cap lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-log-derivative-cost (rate height radius anchor-error)
 (lw-complex-quotient-gain (lw-euler-value-clearance-lower rate height anchor-error) (lw-euler-value-clearance-lower rate height anchor-error) (lw-euler-log-derivative-numerator-cap rate height radius)))

(local (in-theory (disable lw-euler-log-derivative-cost)))

(defthm lw-euler-log-derivative-cost-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate))
  (and (rationalp (lw-euler-log-derivative-cost rate height radius anchor-error)) (< 0 (lw-euler-log-derivative-cost rate height radius anchor-error))))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data
        (:instance lw-euler-log-derivative-numerator-cap-data (error 1))
        (:instance lw-reciprocal-positive (value (lw-euler-value-clearance-lower rate height anchor-error)))
        (:instance lw-eld-positive-product (a (/ (lw-euler-value-clearance-lower rate height anchor-error))) (b (/ (lw-euler-value-clearance-lower rate height anchor-error))))
        (:instance lw-eld-positive-product (a (lw-euler-log-derivative-numerator-cap rate height radius)) (b (* (/ (lw-euler-value-clearance-lower rate height anchor-error)) (/ (lw-euler-value-clearance-lower rate height anchor-error))))))
  :in-theory (union-theories
 '(lw-euler-log-derivative-cost lw-complex-quotient-gain lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-log-derivative-request (rate height radius anchor-error error)
 (min (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error)) (lw-euler-rounding-precision (lw-euler-log-derivative-cost rate height radius anchor-error) (* 2 error))))

(local (in-theory (disable lw-euler-log-derivative-request)))

(defthm lw-euler-log-derivative-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-log-derivative-request rate height radius anchor-error error)) (< 0 (lw-euler-log-derivative-request rate height radius anchor-error error)) (<= (lw-euler-log-derivative-request rate height radius anchor-error error) 1)
       (<= (lw-euler-log-derivative-request rate height radius anchor-error error) (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error)))
       (<= (* (lw-euler-log-derivative-cost rate height radius anchor-error) (lw-euler-log-derivative-request rate height radius anchor-error error)) error)))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data lw-euler-log-derivative-cost-valid
        (:instance lw-euler-rounding-precision-valid (cost (lw-euler-log-derivative-cost rate height radius anchor-error)) (error (* 2 error)))
        (:instance lw-eld-multiply-order
         (a (lw-euler-log-derivative-request rate height radius anchor-error error)) (b (lw-euler-rounding-precision (lw-euler-log-derivative-cost rate height radius anchor-error) (* 2 error))) (factor (lw-euler-log-derivative-cost rate height radius anchor-error))))
  :in-theory (union-theories
 '(lw-euler-log-derivative-request min lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-euler-log-derivative-value (rate height radius anchor-error error)
 (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-log-derivative-request rate height radius anchor-error error)) (lw-complex-euler-continuation-value rate height (lw-euler-log-derivative-request rate height radius anchor-error error))))

(local (in-theory (disable lw-complex-euler-log-derivative-value)))

(defthm lw-complex-euler-log-derivative-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-log-derivative-value rate height radius anchor-error error)))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data lw-euler-log-derivative-request-data
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-euler-log-derivative-request rate height radius anchor-error error)))
        (:instance lw-complex-euler-continuation-value-rational (error (lw-euler-log-derivative-request rate height radius anchor-error error))))
  :in-theory (union-theories
 '(lw-complex-euler-log-derivative-value lw-complex-quotient-rational lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-log-derivative-cap (rate height radius anchor-error)
 (* (lw-euler-log-derivative-numerator-cap rate height radius) (/ (lw-euler-value-clearance-lower rate height anchor-error))))

(local (in-theory (disable lw-euler-log-derivative-cap)))

(defthm lw-complex-euler-log-derivative-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-log-derivative-cap rate height radius anchor-error))
       (< 0 (lw-euler-log-derivative-cap rate height radius anchor-error))
       (lw-complex-diskp (lw-complex-euler-log-derivative-value rate height radius anchor-error error) (lw-euler-log-derivative-cap rate height radius anchor-error))))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data lw-euler-log-derivative-request-data
        (:instance lw-complex-euler-value-clearance (request (lw-euler-log-derivative-request rate height radius anchor-error error)))
        (:instance lw-euler-log-derivative-numerator-cap-data (error (lw-euler-log-derivative-request rate height radius anchor-error error)))
        (:instance lw-reciprocal-positive (value (lw-euler-value-clearance-lower rate height anchor-error)))
        (:instance lw-eld-positive-product (a (lw-euler-log-derivative-numerator-cap rate height radius)) (b (/ (lw-euler-value-clearance-lower rate height anchor-error))))
        (:instance lw-complex-mul-disk
         (left (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-log-derivative-request rate height radius anchor-error error))) (right (lw-complex-reciprocal (lw-complex-euler-continuation-value rate height (lw-euler-log-derivative-request rate height radius anchor-error error)))) (radius (lw-euler-log-derivative-numerator-cap rate height radius)) (other-radius (/ (lw-euler-value-clearance-lower rate height anchor-error)))))
  :in-theory (union-theories
 '(lw-euler-log-derivative-cap lw-complex-euler-log-derivative-value lw-complex-quotient lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(defthm lw-complex-euler-log-derivative-node-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-request) (< 0 left-request) (<= left-request (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error)))
               (rationalp right-request) (< 0 right-request) (<= right-request (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))))
  (lw-complex-diskp (lw-complex-sub (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 left-request) (lw-complex-euler-continuation-value rate height left-request)) (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 right-request) (lw-complex-euler-continuation-value rate height right-request))) (* (lw-euler-log-derivative-cost rate height radius anchor-error) (+ left-request right-request))))
 :hints (("Goal"
  :use (lw-euler-value-clearance-data
        (:instance lw-euler-log-derivative-numerator-cap-data (error right-request))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error left-request))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error right-request))
        (:instance lw-complex-euler-continuation-value-rational (error left-request))
        (:instance lw-complex-euler-continuation-value-rational (error right-request))
        (:instance lw-complex-euler-value-clearance (request left-request))
        (:instance lw-complex-euler-value-clearance (request right-request))
        (:instance lw-complex-euler-local-coefficient-cauchy
         (index 1) (left-error left-request) (right-error right-request))
        (:instance lw-complex-euler-continuation-value-cauchy
         (left-error left-request) (right-error right-request))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-euler-local-coefficient-value rate height radius 1 left-request))
         (denominator (lw-complex-euler-continuation-value rate height left-request))
         (approximate-numerator (lw-complex-euler-local-coefficient-value rate height radius 1 right-request))
         (approximate-denominator (lw-complex-euler-continuation-value rate height right-request))
         (left-clearance (lw-euler-value-clearance-lower rate height anchor-error)) (right-clearance (lw-euler-value-clearance-lower rate height anchor-error)) (numerator-cap (lw-euler-log-derivative-numerator-cap rate height radius))
         (numerator-error (+ left-request right-request)) (denominator-error (+ left-request right-request))))
  :in-theory (union-theories
 '(lw-euler-log-derivative-cost lw-complex-quotient-gain lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-log-derivative-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error left-error) (lw-complex-euler-log-derivative-value rate height radius anchor-error right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :use (lw-euler-log-derivative-cost-valid
        (:instance lw-euler-log-derivative-request-data (error left-error))
        (:instance lw-euler-log-derivative-request-data (error right-error))
        (:instance lw-complex-euler-log-derivative-node-comparison
         (left-request (lw-euler-log-derivative-request rate height radius anchor-error left-error)) (right-request (lw-euler-log-derivative-request rate height radius anchor-error right-error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error left-error) (lw-complex-euler-log-derivative-value rate height radius anchor-error right-error))) (radius (* (lw-euler-log-derivative-cost rate height radius anchor-error) (+ (lw-euler-log-derivative-request rate height radius anchor-error left-error) (lw-euler-log-derivative-request rate height radius anchor-error right-error))))
         (cap (+ left-error right-error))))
  :in-theory (union-theories
 '(lw-complex-euler-log-derivative-value lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-log-derivative-common-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp error) (< 0 error)
               (rationalp request) (< 0 request) (<= request (* 1/4 (lw-euler-value-clearance-lower rate height anchor-error))))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error error) (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 request) (lw-complex-euler-continuation-value rate height request))) (+ error (* (lw-euler-log-derivative-cost rate height radius anchor-error) request))))
 :hints (("Goal"
  :use (lw-euler-log-derivative-cost-valid lw-euler-log-derivative-request-data
        (:instance lw-complex-euler-log-derivative-node-comparison
         (left-request (lw-euler-log-derivative-request rate height radius anchor-error error)) (right-request request))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius anchor-error error) (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 request) (lw-complex-euler-continuation-value rate height request))))
         (radius (* (lw-euler-log-derivative-cost rate height radius anchor-error) (+ (lw-euler-log-derivative-request rate height radius anchor-error error) request))) (cap (+ error (* (lw-euler-log-derivative-cost rate height radius anchor-error) request)))))
  :in-theory (union-theories
 '(lw-complex-euler-log-derivative-value lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


(defun lw-euler-log-derivative-overlap-request (rate height radius left-anchor right-anchor margin)
 (min (* 1/4 (lw-euler-value-clearance-lower rate height left-anchor))
  (min (* 1/4 (lw-euler-value-clearance-lower rate height right-anchor))
   (lw-euler-rounding-precision (+ (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-cost rate height radius right-anchor)) (* 2 margin)))))

(local (in-theory (disable lw-euler-log-derivative-overlap-request)))

(defthm lw-euler-log-derivative-overlap-request-data
 (implies (and (lw-euler-value-clearance-check rate height left-anchor)
               (lw-euler-value-clearance-check rate height right-anchor)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp margin) (< 0 margin))
  (and (rationalp (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)) (< 0 (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin))
       (<= (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin) (* 1/4 (lw-euler-value-clearance-lower rate height left-anchor))) (<= (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin) (* 1/4 (lw-euler-value-clearance-lower rate height right-anchor)))
       (<= (* (+ (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-cost rate height radius right-anchor)) (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)) margin)))
 :hints (("Goal"
  :use ((:instance lw-euler-value-clearance-data (anchor-error left-anchor))
        (:instance lw-euler-value-clearance-data (anchor-error right-anchor))
        (:instance lw-euler-log-derivative-cost-valid (anchor-error left-anchor))
        (:instance lw-euler-log-derivative-cost-valid (anchor-error right-anchor))
        (:instance lw-euler-rounding-precision-valid (cost (+ (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-cost rate height radius right-anchor))) (error (* 2 margin)))
        (:instance lw-eld-multiply-order (a (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin))
         (b (lw-euler-rounding-precision (+ (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-cost rate height radius right-anchor)) (* 2 margin))) (factor (+ (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-cost rate height radius right-anchor)))))
  :in-theory (union-theories
 '(lw-euler-log-derivative-overlap-request min lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eld-common-rational
 (implies (and (lw-euler-value-clearance-check rate height left-anchor)
               (lw-euler-value-clearance-check rate height right-anchor)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp margin) (< 0 margin))
  (lw-complexp (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)) (lw-complex-euler-continuation-value rate height (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))))
 :hints (("Goal"
  :use (lw-euler-log-derivative-overlap-request-data
        (:instance lw-euler-value-clearance-data (anchor-error left-anchor))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))
        (:instance lw-complex-euler-continuation-value-rational (error (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin))))
  :in-theory (union-theories
 '(lw-complex-quotient-rational lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-eld-certificate-overlap-with-margin
 (implies (and (lw-euler-value-clearance-check rate height left-anchor)
               (lw-euler-value-clearance-check rate height right-anchor)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
               (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error) (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)) (+ left-error right-error margin)))
 :hints (("Goal"
  :use (lw-euler-log-derivative-overlap-request-data lw-eld-common-rational
        (:instance lw-euler-log-derivative-cost-valid (anchor-error left-anchor))
        (:instance lw-euler-log-derivative-cost-valid (anchor-error right-anchor))
        (:instance lw-complex-euler-log-derivative-rational (anchor-error left-anchor) (error left-error))
        (:instance lw-complex-euler-log-derivative-rational (anchor-error right-anchor) (error right-error))
        (:instance lw-complex-euler-log-derivative-common-comparison
         (anchor-error left-anchor) (error left-error) (request (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))
        (:instance lw-complex-euler-log-derivative-common-comparison
         (anchor-error right-anchor) (error right-error) (request (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)) (right (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)) (lw-complex-euler-continuation-value rate height (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))) (radius (+ right-error (* (lw-euler-log-derivative-cost rate height radius right-anchor) (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error)) (middle (lw-complex-quotient (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)) (lw-complex-euler-continuation-value rate height (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))) (right (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error))
         (radius (+ left-error (* (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))) (other-radius (+ right-error (* (lw-euler-log-derivative-cost rate height radius right-anchor) (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error) (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)))
         (radius (+ left-error (* (lw-euler-log-derivative-cost rate height radius left-anchor) (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin)) right-error (* (lw-euler-log-derivative-cost rate height radius right-anchor) (lw-euler-log-derivative-overlap-request rate height radius left-anchor right-anchor margin))))
         (cap (+ left-error right-error margin))))
  :in-theory (union-theories
 '( lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-log-derivative-certificate-independence
 (implies (and (lw-euler-value-clearance-check rate height left-anchor)
               (lw-euler-value-clearance-check rate height right-anchor)
               (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error) (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error) (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)) (+ left-error right-error)))
  :use ((:instance lw-complex-euler-log-derivative-rational (anchor-error left-anchor) (error left-error))
        (:instance lw-complex-euler-log-derivative-rational (anchor-error right-anchor) (error right-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error)) (right (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error) (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error))) (radius (+ left-error right-error)) (cost 1))
        (:instance lw-eld-certificate-overlap-with-margin
         (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-log-derivative-value rate height radius left-anchor left-error) (lw-complex-euler-log-derivative-value rate height radius right-anchor right-error)) (+ left-error right-error) 1))))
  :in-theory (union-theories
 '( lw-eld-left-commutes lw-eld-left-distributes lw-eld-fold-constants lw-eld-times-negative lw-eld-negative-times lw-eld-zero-times lw-eld-minus-one lw-eld-double-negative lw-eld-add-cancel lw-eld-double lw-eld-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



