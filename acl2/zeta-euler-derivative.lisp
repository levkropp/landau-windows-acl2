(in-package "ACL2")

(include-book "complex-quotient-increments")
(include-book "euler-native-derivative")

; A normalized derivative name for V(s)/(s-1), with computed requests
; small enough for the actual finite difference quotient.

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

(local (in-theory
 (disable lw-euler-refined-polynomial lw-euler-refined-polynomial-request
          lw-euler-derivative-alignment-block lw-euler-derivative-alignment-request
          lw-euler-derivative-alignment-target lw-euler-block-prefix-count
          lw-euler-derivative-value-budget lw-euler-derivative-slope-budget
          lw-euler-derivative-native-budget lw-euler-native-derivative-gain
          lw-complex-euler-local-coefficient-value
          lw-complex-zeta-pole-removed-derivative-series-value)))

(local (in-theory (disable lw-euler-derivative-alignment-polynomial)))

(local (in-theory (disable lw-euler-native-derivative-request)))
(local (in-theory
 (disable lw-complex-l1 lw-complex-norm-square lw-complex-quotient
          lw-zeta-euler-inverse-cap lw-complex-zeta-euler-value lw-zeta-euler-point-error
          lw-euler-uniform-coefficient-cap lw-euler-local-coefficient-request)))

(local (defthm lw-zed-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zed-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zed-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zed-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zed-times-negative (a b) (b a)))
                 :in-theory (disable lw-zed-times-negative)))))

(local (defthm lw-zed-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zed-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zed-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zed-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zed-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zed-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zed-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zed-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zed-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zed-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zed-left-commutes)))))

(local (defthm lw-zed-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-zed-cons-equality
 (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d)))
 :hints (("Goal" :use ((:instance lw-zed-pair-equality (left (cons a b)) (right (cons c d))))
                 :in-theory (union-theories
 '( lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))))

(local (defthm lw-zed-point-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0))))
  (and (lw-complexp (cons (- rate 1) height)) (not (equal (cons (- rate 1) height) (cons 0 0)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-zed-cons-equality lw-complexp lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))
 :rule-classes nil))

(defun lw-zeta-derivative-anchor-size (rate height)
 (lw-complex-l1 (cons (- rate 1) height)))

(defun lw-zeta-derivative-left-gain (rate height)
 (/ (* 1/4 (lw-zeta-derivative-anchor-size rate height))))

(defun lw-zeta-derivative-right-gain (rate height)
 (/ (* 1/2 (lw-zeta-derivative-anchor-size rate height))))

(defun lw-zeta-derivative-request-cost (rate height)
 (+ (* 2 (lw-zeta-euler-inverse-cap rate height)) (* (lw-zeta-derivative-left-gain rate height) (+ 9 (* 4 (lw-zeta-euler-inverse-cap rate height))))))

(local (in-theory (disable lw-zeta-derivative-anchor-size lw-zeta-derivative-left-gain
 lw-zeta-derivative-right-gain lw-zeta-derivative-request-cost)))

(defthm lw-zeta-derivative-cost-data
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0))))
  (and (rationalp (lw-zeta-derivative-anchor-size rate height)) (< 0 (lw-zeta-derivative-anchor-size rate height))
       (rationalp (lw-zeta-derivative-left-gain rate height)) (< 0 (lw-zeta-derivative-left-gain rate height)) (rationalp (lw-zeta-derivative-right-gain rate height)) (< 0 (lw-zeta-derivative-right-gain rate height))
       (rationalp (lw-zeta-derivative-request-cost rate height)) (< 0 (lw-zeta-derivative-request-cost rate height))
       (<= (* 2 (lw-zeta-euler-inverse-cap rate height)) (lw-zeta-derivative-request-cost rate height)) (<= (* (lw-zeta-derivative-left-gain rate height) (+ 9 (* 4 (lw-zeta-euler-inverse-cap rate height)))) (lw-zeta-derivative-request-cost rate height))))
 :hints (("Goal"
  :use (lw-zed-point-data lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-l1-clearance (point (cons (- rate 1) height)))
        (:instance lw-reciprocal-positive (value (* 1/4 (lw-zeta-derivative-anchor-size rate height))))
        (:instance lw-reciprocal-positive (value (* 1/2 (lw-zeta-derivative-anchor-size rate height))))
        (:instance lw-zed-positive-product (a (lw-zeta-derivative-left-gain rate height)) (b (+ 9 (* 4 (lw-zeta-euler-inverse-cap rate height))))))
  :in-theory (union-theories
 '(lw-zeta-derivative-anchor-size lw-zeta-derivative-left-gain lw-zeta-derivative-right-gain lw-zeta-derivative-request-cost lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-derivative-request (rate height error)
 (lw-euler-rounding-precision (lw-zeta-derivative-request-cost rate height) (/ error 2)))

(local (in-theory (disable lw-zeta-derivative-request)))

(defthm lw-zeta-derivative-request-data
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-derivative-request rate height error)) (< 0 (lw-zeta-derivative-request rate height error)) (<= (lw-zeta-derivative-request rate height error) 1)
       (<= (* (lw-zeta-derivative-request-cost rate height) (lw-zeta-derivative-request rate height error)) (/ error 4))
       (<= (* 2 (lw-zeta-euler-inverse-cap rate height) (lw-zeta-derivative-request rate height error)) (/ error 4))
       (<= (* (lw-zeta-derivative-left-gain rate height) (+ 9 (* 4 (lw-zeta-euler-inverse-cap rate height))) (lw-zeta-derivative-request rate height error)) (/ error 4))))
 :hints (("Goal"
  :use (lw-zeta-derivative-cost-data lw-zeta-euler-inverse-cap-data
        (:instance lw-euler-rounding-precision-valid (cost (lw-zeta-derivative-request-cost rate height)) (error (/ error 2)))
        (:instance lw-zed-multiply-order (a (* 2 (lw-zeta-euler-inverse-cap rate height))) (b (lw-zeta-derivative-request-cost rate height)) (factor (lw-zeta-derivative-request rate height error)))
        (:instance lw-zed-multiply-order (a (* (lw-zeta-derivative-left-gain rate height) (+ 9 (* 4 (lw-zeta-euler-inverse-cap rate height))))) (b (lw-zeta-derivative-request-cost rate height)) (factor (lw-zeta-derivative-request rate height error))))
  :in-theory (union-theories
 '(lw-zeta-derivative-request lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-zeta-euler-derivative-value (rate height radius error)
 (lw-complex-mul (lw-complex-reciprocal (cons (- rate 1) height))
  (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error))
                  (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error)))))

(local (in-theory (disable lw-complex-zeta-euler-derivative-value)))

(defthm lw-complex-zeta-euler-derivative-rational
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-euler-derivative-value rate height radius error)))
 :hints (("Goal"
  :use (lw-zeta-derivative-request-data lw-zeta-euler-inverse-cap-data
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height error))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-derivative-value lw-complex-ring-rational lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-zed-derivative-residual
 (implies (and (lw-complexp factor) (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
  (equal
   (lw-complex-sub (lw-complex-mul factor (lw-complex-sub a b))
                   (lw-complex-mul factor (lw-complex-sub c d)))
   (lw-complex-mul factor (lw-complex-sub (lw-complex-sub a c) (lw-complex-sub b d)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-mul lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-zeta-euler-derivative-cauchy
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius left-error) (lw-complex-zeta-euler-derivative-value rate height radius right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :use (lw-zeta-euler-inverse-cap-data
        (:instance lw-zeta-derivative-request-data (error left-error))
        (:instance lw-zeta-derivative-request-data (error right-error))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height left-error)))
        (:instance lw-complex-euler-local-coefficient-rational (index 1) (error (lw-zeta-derivative-request rate height right-error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height left-error)))
        (:instance lw-complex-zeta-euler-value-rational (error (lw-zeta-derivative-request rate height right-error)))
        (:instance lw-complex-euler-local-coefficient-cauchy (index 1) (left-error (lw-zeta-derivative-request rate height left-error)) (right-error (lw-zeta-derivative-request rate height right-error)))
        (:instance lw-complex-zeta-euler-value-cauchy (left-error (lw-zeta-derivative-request rate height left-error)) (right-error (lw-zeta-derivative-request rate height right-error)))
        (:instance lw-complex-sub-disk
         (left (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height left-error)) (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height right-error)))) (right (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height left-error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height right-error))))
         (radius (+ (lw-zeta-derivative-request rate height left-error) (lw-zeta-derivative-request rate height right-error))) (other-radius (+ (lw-zeta-derivative-request rate height left-error) (lw-zeta-derivative-request rate height right-error))))
        (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (cons (- rate 1) height))) (right (lw-complex-sub (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height left-error)) (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height right-error))) (lw-complex-sub (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height left-error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height right-error)))))
         (radius (lw-zeta-euler-inverse-cap rate height)) (other-radius (* 2 (+ (lw-zeta-derivative-request rate height left-error) (lw-zeta-derivative-request rate height right-error)))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-derivative-value rate height radius left-error) (lw-complex-zeta-euler-derivative-value rate height radius right-error)))
         (radius (* 2 (lw-zeta-euler-inverse-cap rate height) (+ (lw-zeta-derivative-request rate height left-error) (lw-zeta-derivative-request rate height right-error)))) (cap (+ left-error right-error))))
  :in-theory (union-theories
 '(lw-complex-zeta-euler-derivative-value lw-zed-derivative-residual lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-zeta-euler-coarse-cap (rate height)
 (+ 2 (lw-complex-l1 (lw-complex-zeta-euler-value rate height 1))))

(local (in-theory (disable lw-zeta-euler-coarse-cap)))

(defthm lw-complex-zeta-euler-coarse-bound
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp request) (< 0 request) (<= request 1))
  (and (rationalp (lw-zeta-euler-coarse-cap rate height)) (<= 2 (lw-zeta-euler-coarse-cap rate height)) (lw-complex-diskp (lw-complex-zeta-euler-value rate height request) (lw-zeta-euler-coarse-cap rate height))))
 :hints (("Goal"
  :use ((:instance lw-complex-zeta-euler-value-rational (error request))
        (:instance lw-complex-zeta-euler-value-rational (error 1))
        (:instance lw-complex-zeta-euler-value-cauchy (left-error request) (right-error 1))
        (:instance lw-complex-l1-bound (point (lw-complex-zeta-euler-value rate height 1)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-euler-value rate height request) (lw-complex-zeta-euler-value rate height 1)))
         (radius (+ request 1)) (cap 2))
        (:instance lw-complex-difference-triangle (left (lw-complex-zeta-euler-value rate height request)) (middle (lw-complex-zeta-euler-value rate height 1)) (right (cons 0 0))
         (radius 2) (other-radius (lw-complex-l1 (lw-complex-zeta-euler-value rate height 1)))))
  :in-theory (union-theories
 '(lw-zeta-euler-coarse-cap lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-zed-power-first
 (implies (rationalp radius) (equal (lw-rational-power radius 1) radius))
 :hints (("Goal" :expand ((lw-rational-power radius 1) (lw-rational-power radius 0))
                 :in-theory (enable lw-rational-power)))))

(defun lw-zeta-derivative-numerator-cap (rate height radius)
 (+ (* (lw-euler-uniform-coefficient-cap rate height radius) (/ radius)) (lw-zeta-euler-coarse-cap rate height)))

(local (in-theory (disable lw-zeta-derivative-numerator-cap)))

(defthm lw-zeta-derivative-numerator-cap-data
 (implies (and (and (rationalp rate) (< 0 rate) (rationalp height) (not (and (equal rate 1) (equal height 0)))) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (and (rationalp (lw-zeta-derivative-numerator-cap rate height radius)) (< 0 (lw-zeta-derivative-numerator-cap rate height radius))
       (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error)) (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error))) (lw-zeta-derivative-numerator-cap rate height radius))))
 :hints (("Goal"
  :use (lw-zeta-derivative-request-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-reciprocal-positive (value radius))
        (:instance lw-zed-positive-product (a (lw-euler-uniform-coefficient-cap rate height radius)) (b (/ radius)))
        (:instance lw-complex-zeta-euler-coarse-bound (request (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-euler-local-coefficient-cap (index 1) (error (lw-zeta-derivative-request rate height error)))
        (:instance lw-complex-sub-disk (left (lw-complex-euler-local-coefficient-value rate height radius 1 (lw-zeta-derivative-request rate height error))) (right (lw-complex-zeta-euler-value rate height (lw-zeta-derivative-request rate height error)))
         (radius (* (lw-euler-uniform-coefficient-cap rate height radius) (/ radius))) (other-radius (lw-zeta-euler-coarse-cap rate height))))
  :in-theory (union-theories
 '(lw-zeta-derivative-numerator-cap lw-zed-power-first lw-zed-left-commutes lw-zed-left-distributes lw-zed-fold-constants lw-zed-times-negative lw-zed-negative-times lw-zed-zero-times lw-zed-minus-one lw-zed-double-negative lw-zed-add-cancel lw-zed-double lw-zed-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))


