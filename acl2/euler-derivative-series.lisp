(in-package "ACL2")

(include-book "euler-prefix-derivatives")
(include-book "zeta-series-clearance")

; The derivative of each finite Euler truncation approaches the actual
; ordinary-minus-logweighted native series, with its upper boundary explicit.

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

(local (in-theory (disable lw-exp-mixturep lw-exp-mixture-mass lw-exp-mixture-common-value
 lw-complex-common-dirichlet-prefix lw-common-dirichlet-coefficient
 lw-zeta-dirichlet-weight lw-dirichlet-sample lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (in-theory (disable lw-euler-dirichlet-nodes)))

(local (in-theory (disable lw-euler-boundary-nodes)))
(local (in-theory
 (disable lw-complex-euler-prefix-derivative lw-complex-zeta-series-value
          lw-complex-common-native-series lw-dirichlet-native-refinement
          lw-dirichlet-series-count lw-euler-zeta-boundary-cost)))

(local (defthm lw-eps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eps-times-negative (a b) (b a)))
                 :in-theory (disable lw-eps-times-negative)))))

(local (defthm lw-eps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eps-left-commutes)))))

(defun lw-euler-derivative-boundary-cost (rate height index)
 (* index index (lw-euler-zeta-boundary-cost rate height index)))

(local (in-theory (disable lw-euler-derivative-boundary-cost)))

(defthm lw-euler-derivative-boundary-cost-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp index) (< 1 index))
  (and (rationalp (lw-euler-derivative-boundary-cost rate height index))
       (< 0 (lw-euler-derivative-boundary-cost rate height index))))
 :hints (("Goal"
  :use (lw-euler-zeta-boundary-cost-valid)
  :in-theory (union-theories
 '(lw-euler-derivative-boundary-cost lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-eps-cube-cancel
 (implies (and (rationalp index) (not (equal index 0)))
  (equal (* index index (/ index) (/ index) (/ index)) (/ index)))
 :hints (("Goal" :use ((:instance lw-eps-inverse-factor (divisor index) (coefficient (* index (/ index) (/ index))))
                        (:instance lw-eps-inverse-factor (divisor index) (coefficient (/ index))))
  :in-theory (union-theories
 '( lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))))

(defthm lw-complex-euler-derivative-boundary-bound
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp index) (< 1 index)
               (rationalp request) (< 0 request) (<= request 1))
  (lw-complex-diskp
   (lw-complex-scale (* index (car (lw-log-bounds index request)))
    (lw-complex-log-ramp-independent-exp rate height index request request))
   (+ (* 2 (/ index)) (* (lw-euler-derivative-boundary-cost rate height index) request))))
 :hints (("Goal"
  :use (lw-euler-zeta-boundary-cost-valid
        lw-dirichlet-cubic-node-cost-valid
        (:instance lw-exp-lipschitz-cap-valid (cap index))
        (:instance lw-euler-weighted-boundary-nodes-data)
        (:instance lw-exp-mixture-mass-nonnegative
         (nodes (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes index request))))
        (:instance lw-complex-dirichlet-unweighted-cubic-bound (log-error request) (error request))
        (:instance lw-complex-disk-data
         (point (lw-complex-log-ramp-independent-exp rate height index request request))
         (radius (+ (* 2 (/ index) (/ index) (/ index)) (* (lw-euler-zeta-boundary-cost rate height index) request))))
        (:instance lw-complex-scale-disk
         (point (lw-complex-log-ramp-independent-exp rate height index request request))
         (factor (* index (car (lw-log-bounds index request))))
         (radius (+ (* 2 (/ index) (/ index) (/ index)) (* (lw-euler-zeta-boundary-cost rate height index) request))))
        (:instance lw-eps-multiply-order
         (a (* index (car (lw-log-bounds index request)))) (b (* index index))
         (factor (+ (* 2 (/ index) (/ index) (/ index)) (* (lw-euler-zeta-boundary-cost rate height index) request))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (* index (car (lw-log-bounds index request)))
          (lw-complex-log-ramp-independent-exp rate height index request request)))
         (radius (* (* index (car (lw-log-bounds index request)))
          (+ (* 2 (/ index) (/ index) (/ index)) (* (lw-euler-zeta-boundary-cost rate height index) request))))
         (cap (+ (* 2 (/ index)) (* (lw-euler-derivative-boundary-cost rate height index) request)))))
  :in-theory (union-theories
 '(lw-euler-derivative-boundary-cost lw-euler-zeta-boundary-cost lw-eps-cube-cancel abs lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-zeta-pole-removed-derivative-series-value (rate height error)
 (lw-complex-add (lw-complex-mul (cons (- rate 1) height) (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height error))) (lw-complex-zeta-series-value nil rate height error)))

(local (in-theory (disable lw-complex-zeta-pole-removed-derivative-series-value)))

(defthm lw-complex-zeta-pole-removed-derivative-series-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-pole-removed-derivative-series-value rate height error)))
 :hints (("Goal"
  :use ((:instance lw-complex-zeta-series-value-rational (logp nil))
        (:instance lw-complex-zeta-series-value-rational (logp t)))
  :in-theory (union-theories
 '(lw-complex-zeta-pole-removed-derivative-series-value lw-complex-ring-rational lw-complex-scale-rational lw-complexp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-eps-three-term-residual
 (implies (and (lw-complexp constant) (lw-complexp left1) (lw-complexp right1) (lw-complexp left2) (lw-complexp right2) (lw-complexp left3) (lw-complexp right3))
  (equal (lw-complex-sub (lw-complex-add (lw-complex-add (lw-complex-mul constant left1) left2) left3) (lw-complex-add (lw-complex-add (lw-complex-mul constant right1) right2) right3)) (lw-complex-add (lw-complex-add (lw-complex-mul constant (lw-complex-sub left1 right1)) (lw-complex-sub left2 right2)) (lw-complex-sub left3 right3))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(local (defthm lw-eps-three-term-error
 (implies (and (and (lw-complexp constant) (lw-complexp left1) (lw-complexp right1) (lw-complexp left2) (lw-complexp right2) (lw-complexp left3) (lw-complexp right3))
               (lw-complex-diskp constant cap)
               (lw-complex-diskp (lw-complex-sub left1 right1) error1)
               (lw-complex-diskp (lw-complex-sub left2 right2) error2)
               (lw-complex-diskp (lw-complex-sub left3 right3) error3))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add (lw-complex-add (lw-complex-mul constant left1) left2) left3) (lw-complex-add (lw-complex-add (lw-complex-mul constant right1) right2) right3))
   (+ (* cap error1) error2 error3)))
 :hints (("Goal"
  :use (lw-eps-three-term-residual
        (:instance lw-complex-mul-disk (left constant) (right (lw-complex-sub left1 right1)) (radius cap) (other-radius error1))
        (:instance lw-complex-add-disk (left (lw-complex-mul constant (lw-complex-sub left1 right1))) (right (lw-complex-sub left2 right2)) (radius (* cap error1)) (other-radius error2))
        (:instance lw-complex-add-disk (left (lw-complex-add (lw-complex-mul constant (lw-complex-sub left1 right1)) (lw-complex-sub left2 right2))) (right (lw-complex-sub left3 right3)) (radius (+ (* cap error1) error2)) (other-radius error3)))
  :in-theory (union-theories
 '( lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-eps-negated-difference
 (implies (and (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-scale -1 left) (lw-complex-scale -1 right))
         (lw-complex-scale -1 (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-scale lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-eps-negated-difference-bound
 (implies (and (lw-complexp left) (lw-complexp right)
               (lw-complex-diskp (lw-complex-sub left right) radius))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-scale -1 left) (lw-complex-scale -1 right)) radius))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (point (lw-complex-sub left right)))
        (:instance lw-complex-scale-disk (point (lw-complex-sub left right)) (factor -1)))
  :in-theory (union-theories
 '(lw-eps-negated-difference abs lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-eps-zero-error
 (lw-complex-diskp (lw-complex-sub (cons 0 0) (cons 0 0)) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-diskp lw-complex-sub)))))

(defthm lw-complex-zeta-pole-removed-derivative-series-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-zeta-pole-removed-derivative-series-value rate height left-error)
    (lw-complex-zeta-pole-removed-derivative-series-value rate height right-error))
   (* (+ 1 (+ rate (abs height) 1)) (+ left-error right-error))))
 :hints (("Goal"
  :use (lw-complex-zeta-shifted-point-cap lw-eps-zero-error
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error left-error))
        (:instance lw-complex-zeta-series-value-rational (logp nil) (error right-error))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error left-error))
        (:instance lw-complex-zeta-series-value-rational (logp t) (error right-error))
        (:instance lw-complex-zeta-series-value-cauchy (logp nil))
        (:instance lw-complex-zeta-series-value-cauchy (logp t))
        (:instance lw-eps-negated-difference-bound (left (lw-complex-zeta-series-value t rate height left-error)) (right (lw-complex-zeta-series-value t rate height right-error)) (radius (+ left-error right-error)))
        (:instance lw-eps-three-term-error
         (constant (cons (- rate 1) height)) (cap (+ rate (abs height) 1))
         (left1 (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height left-error))) (right1 (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height right-error)))
         (left2 (lw-complex-zeta-series-value nil rate height left-error)) (right2 (lw-complex-zeta-series-value nil rate height right-error))
         (left3 (cons 0 0)) (right3 (cons 0 0))
         (error1 (+ left-error right-error)) (error2 (+ left-error right-error)) (error3 0)))
  :in-theory (union-theories
 '(lw-complex-zeta-pole-removed-derivative-series-value lw-complexp lw-complex-add-zero lw-complex-scale-rational lw-complex-ring-rational lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-prefix-derivative-rational
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request))
  (lw-complexp (lw-complex-euler-prefix-derivative rate height count request)))
 :hints (("Goal"
  :use ((:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (error request))
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp t) (error request))
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request))
        (:instance lw-complex-log-ramp-independent-exp-rational (index (+ 1 count)) (log-error request) (delta request)))
  :in-theory (union-theories
 '(lw-complex-euler-prefix-derivative lw-complexp lw-complex-scale-rational lw-complex-ring-rational lw-intervalp lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-prefix-derivative-native-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count)
               (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
               (rationalp target-error) (< 0 target-error)
               (rationalp request) (< 0 request) (<= request 1)
               (<= request (lw-dirichlet-native-refinement rate height count target-error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-euler-prefix-derivative rate height count request)
    (lw-complex-zeta-pole-removed-derivative-series-value rate height error))
   (+ (* (+ 1 (+ rate (abs height) 1)) (+ (* 3/8 error) target-error))
      (* 2 (/ (+ 1 count)))
      (* (lw-euler-derivative-boundary-cost rate height (+ 1 count)) request))))
 :hints (("Goal"
  :use (lw-complex-zeta-shifted-point-cap
        (:instance lw-euler-derivative-boundary-cost-valid (index (+ 1 count)))
        (:instance lw-complex-euler-derivative-boundary-bound (index (+ 1 count)))
        (:instance lw-complex-common-prefix-series-computed-comparison (mangoldtp nil) (logp nil))
        (:instance lw-complex-common-prefix-series-computed-comparison (mangoldtp nil) (logp t))
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (error request))
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp t) (error request))
        (:instance lw-complex-zeta-series-value-rational (logp nil))
        (:instance lw-complex-zeta-series-value-rational (logp t))
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request))
        (:instance lw-complex-log-ramp-independent-exp-rational (index (+ 1 count)) (log-error request) (delta request))
        (:instance lw-eps-negated-difference-bound
         (left (lw-complex-common-dirichlet-prefix nil t rate height count request)) (right (lw-complex-zeta-series-value t rate height error)) (radius (+ (* 3/8 error) target-error)))
        (:instance lw-complex-scale-disk (point (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request))) (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request))) (factor -1)
         (radius (+ (* 2 (/ (+ 1 count))) (* (lw-euler-derivative-boundary-cost rate height (+ 1 count)) request))))
        (:instance lw-eps-three-term-error
         (constant (cons (- rate 1) height)) (cap (+ rate (abs height) 1))
         (left1 (lw-complex-scale -1 (lw-complex-common-dirichlet-prefix nil t rate height count request))) (right1 (lw-complex-scale -1 (lw-complex-zeta-series-value t rate height error)))
         (left2 (lw-complex-common-dirichlet-prefix nil nil rate height count request)) (right2 (lw-complex-zeta-series-value nil rate height error))
         (left3 (lw-complex-scale -1 (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request))) (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request)))) (right3 (cons 0 0))
         (error1 (+ (* 3/8 error) target-error)) (error2 (+ (* 3/8 error) target-error))
         (error3 (+ (* 2 (/ (+ 1 count))) (* (lw-euler-derivative-boundary-cost rate height (+ 1 count)) request)))))
  :in-theory (union-theories
 '(lw-complex-euler-prefix-derivative lw-complex-zeta-pole-removed-derivative-series-value lw-complex-common-native-series lw-complexp lw-complex-add-zero lw-complex-sub-zero lw-complex-scale-rational lw-complex-ring-rational lw-intervalp abs lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-prefix-polynomial-native-derivative-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (<= request 1)
               (lw-complex-diskp (lw-complex-laplace-point rate height) argument-cap) (natp target)
               (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp boundary-error) (< 0 boundary-error)
               (rationalp derivative-error) (< 0 derivative-error)
               (<= (lw-euler-derivative-target count request argument-cap derivative-error) target)
               (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
               (rationalp target-error) (< 0 target-error)
               (<= request (lw-dirichlet-native-refinement rate height count target-error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-coefficient-at (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error) 1 0)
                   (lw-complex-zeta-pole-removed-derivative-series-value rate height error))
   (+ (+ (* (+ rate (abs height) 1) (+ (* 3/2 derivative-error) (* count count request)))
      (* 3/2 ordinary-error) (* (- count 1) request)
      (* 3/2 derivative-error) (* (+ 1 count) (+ 1 count) request)) (+ (* (+ 1 (+ rate (abs height) 1)) (+ (* 3/8 error) target-error))
      (* 2 (/ (+ 1 count)))
      (* (lw-euler-derivative-boundary-cost rate height (+ 1 count)) request)))))
 :hints (("Goal"
  :use ((:instance lw-euler-prefix-polynomial-first-common-comparison (error derivative-error))
        lw-complex-euler-prefix-derivative-native-comparison
        lw-euler-prefix-polynomial-components-valid
        lw-complex-euler-prefix-derivative-rational
        lw-complex-zeta-pole-removed-derivative-series-rational
        (:instance lw-complex-disk-data (point (lw-complex-laplace-point rate height)) (radius argument-cap))
        (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error)) (target 1) (offset 0))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-coefficient-at (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error) 1 0))
         (middle (lw-complex-euler-prefix-derivative rate height count request))
         (right (lw-complex-zeta-pole-removed-derivative-series-value rate height error))
         (radius (+ (* (+ rate (abs height) 1) (+ (* 3/2 derivative-error) (* count count request)))
      (* 3/2 ordinary-error) (* (- count 1) request)
      (* 3/2 derivative-error) (* (+ 1 count) (+ 1 count) request))) (other-radius (+ (* (+ 1 (+ rate (abs height) 1)) (+ (* 3/8 error) target-error))
      (* 2 (/ (+ 1 count)))
      (* (lw-euler-derivative-boundary-cost rate height (+ 1 count)) request)))))
  :in-theory (union-theories
 '( lw-eps-left-commutes lw-eps-left-distributes lw-eps-fold-constants lw-eps-times-negative lw-eps-negative-times lw-eps-zero-times lw-eps-minus-one lw-eps-double-negative lw-eps-add-cancel lw-eps-double lw-eps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



