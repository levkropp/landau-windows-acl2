(in-package "ACL2")

(include-book "euler-prefix-polynomial")
(include-book "euler-weighted-mixtures")
(include-book "polynomial-sum-coefficients")

; Connect the first coefficient of the actual finite Euler polynomial
; to the ordinary and log-weighted common-precision Dirichlet prefixes.

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
 (disable lw-exp-mixture-derivative-nodes lw-exp-mixture-derivative-degree
          lw-euler-ordinary-polynomial lw-euler-boundary-polynomial lw-euler-prefix-polynomial
          lw-polynomial-add lw-polynomial-add-constant lw-polynomial-multiply-linear
          lw-complex-coefficient-at lw-complex-polynomial
          lw-exp-mixture-affine-polynomial lw-exp-mixture-degree lw-exp-mixture-coefficients)))

(local (defthm lw-epd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epd-times-negative (a b) (b a)))
                 :in-theory (disable lw-epd-times-negative)))))

(local (defthm lw-epd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epd-left-commutes)))))

(defun lw-euler-derivative-target (count request argument-cap error)
 (max
  (lw-exp-mixture-derivative-degree (lw-euler-dirichlet-nodes count request) argument-cap error)
  (lw-exp-mixture-derivative-degree (lw-euler-boundary-nodes (+ 1 count) request) argument-cap error)))

(local (in-theory (disable lw-euler-derivative-target)))

(defthm lw-euler-derivative-target-data
 (implies (and (posp count) (rationalp request) (< 0 request)
               (rationalp argument-cap) (<= 0 argument-cap) (rationalp error) (< 0 error))
  (and (posp (lw-euler-derivative-target count request argument-cap error))
       (<= (lw-exp-mixture-derivative-degree (lw-euler-dirichlet-nodes count request) argument-cap error)
           (lw-euler-derivative-target count request argument-cap error))
       (<= (lw-exp-mixture-derivative-degree (lw-euler-boundary-nodes (+ 1 count) request) argument-cap error)
           (lw-euler-derivative-target count request argument-cap error))))
 :hints (("Goal"
  :use ((:instance lw-euler-dirichlet-nodes-valid (log-error request))
        (:instance lw-euler-boundary-nodes-valid (index (+ 1 count)) (log-error request))
        (:instance lw-exp-mixture-derivative-degree-data (nodes (lw-euler-dirichlet-nodes count request)) (radius argument-cap))
        (:instance lw-exp-mixture-derivative-degree-data (nodes (lw-euler-boundary-nodes (+ 1 count) request)) (radius argument-cap)))
  :in-theory (union-theories
 '(lw-euler-derivative-target max lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-prefix-polynomial-linear-coefficient
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (rationalp argument-cap) (<= 0 argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp boundary-error) (< 0 boundary-error))
  (equal
   (lw-complex-coefficient-at (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error) 1 0)
   (lw-complex-add
    (lw-complex-add
     (lw-complex-mul (cons (- rate 1) height) (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 1 0))
     (lw-complex-add (cons 1 0) (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 0 0)))
    (lw-complex-coefficient-at (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error) 1 0))))
 :hints (("Goal"
  :use (lw-euler-prefix-polynomial-components-valid
        (:instance lw-polynomial-add-constant-valid (constant (cons 1 0)) (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-polynomial-multiply-linear-valid (constant (cons (- rate 1) height)) (slope (cons 1 0)) (coefficients (lw-polynomial-add-constant (cons 1 0) (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
        (:instance lw-polynomial-add-coefficient (left (lw-polynomial-multiply-linear (cons (- rate 1) height) (cons 1 0) (lw-polynomial-add-constant (cons 1 0) (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))) (right (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error)) (target 1) (offset 0))
        (:instance lw-polynomial-multiply-linear-first-coefficient (constant (cons (- rate 1) height)) (slope (cons 1 0)) (coefficients (lw-polynomial-add-constant (cons 1 0) (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
        (:instance lw-polynomial-add-constant-linear-coefficient (constant (cons 1 0)) (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-polynomial-add-constant-zero-coefficient (constant (cons 1 0)) (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)) (target 0) (offset 0))
        (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 0 0))))
  :in-theory (union-theories
 '(lw-euler-prefix-polynomial lw-complexp lw-complex-mul-one lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-epd-complex-negation
 (implies (lw-complexp point)
  (equal (lw-complex-mul (cons -1 0) point) (lw-complex-scale -1 point)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-mul lw-complex-scale lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-ordinary-polynomial-first-comparison
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (lw-complex-diskp (lw-complex-laplace-point rate height) argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp error) (< 0 error) (<= (lw-euler-derivative-target count request argument-cap error) target))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 1 0) (lw-complex-scale -1 (lw-complex-common-dirichlet-prefix nil t rate height count request)))
   (+ (* 3/2 error) (* count count request))))
 :hints (("Goal"
  :use (lw-euler-derivative-target-data lw-euler-weighted-dirichlet-nodes-prefix lw-euler-weighted-dirichlet-nodes-mass
        (:instance lw-complex-disk-data (point (lw-complex-laplace-point rate height)) (radius argument-cap))
        (:instance lw-euler-dirichlet-nodes-valid (log-error request))
        (:instance lw-exp-mixture-derivative-nodes-valid (nodes (lw-euler-dirichlet-nodes count request)))
        (:instance lw-exp-mixture-common-value-rational (nodes (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))) (point (lw-complex-laplace-point rate height)))
        (:instance lw-exp-mixture-affine-derivative-common-comparison
         (nodes (lw-euler-dirichlet-nodes count request)) (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (radius argument-cap) (slope-cap 1))
        (:instance lw-epd-multiply-order
         (a (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request)))) (b (* count count)) (factor request))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 1 0) (lw-complex-scale -1 (lw-complex-common-dirichlet-prefix nil t rate height count request))))
         (radius (+ (* 3/2 error) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-dirichlet-nodes count request))) request)))
         (cap (+ (* 3/2 error) (* count count request)))))
  :in-theory (union-theories
 '(lw-euler-ordinary-polynomial lw-epd-complex-negation lw-complexp lw-complex-diskp lw-diskp lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-boundary-polynomial-first-comparison
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (lw-complex-diskp (lw-complex-laplace-point rate height) argument-cap)
               (natp target) (rationalp boundary-error) (< 0 boundary-error)
               (rationalp error) (< 0 error) (<= (lw-euler-derivative-target count request argument-cap error) target))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-coefficient-at (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error) 1 0) (lw-complex-scale -1 (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request))) (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request))))
   (+ (* 3/2 error) (* (+ 1 count) (+ 1 count) request))))
 :hints (("Goal"
  :use (lw-euler-derivative-target-data
        (:instance lw-euler-weighted-boundary-nodes-data (index (+ 1 count)))
        (:instance lw-euler-weighted-boundary-nodes-value (index (+ 1 count)))
        (:instance lw-complex-disk-data (point (lw-complex-laplace-point rate height)) (radius argument-cap))
        (:instance lw-euler-boundary-nodes-valid (index (+ 1 count)) (log-error request))
        (:instance lw-exp-mixture-derivative-nodes-valid (nodes (lw-euler-boundary-nodes (+ 1 count) request)))
        (:instance lw-exp-mixture-common-value-rational (nodes (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes (+ 1 count) request))) (point (lw-complex-laplace-point rate height)))
        (:instance lw-exp-mixture-affine-derivative-common-comparison
         (nodes (lw-euler-boundary-nodes (+ 1 count) request)) (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (radius argument-cap) (slope-cap 1) (ordinary-error boundary-error))
        (:instance lw-epd-multiply-order
         (a (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes (+ 1 count) request)))) (b (* (+ 1 count) (+ 1 count))) (factor request))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-coefficient-at (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error) 1 0) (lw-complex-scale -1 (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request))) (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request)))))
         (radius (+ (* 3/2 error) (* (lw-exp-mixture-mass (lw-exp-mixture-derivative-nodes (lw-euler-boundary-nodes (+ 1 count) request))) request)))
         (cap (+ (* 3/2 error) (* (+ 1 count) (+ 1 count) request)))))
  :in-theory (union-theories
 '(lw-euler-boundary-polynomial lw-epd-complex-negation lw-complexp lw-complex-diskp lw-diskp lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-epd-translate-difference
 (implies (and (lw-complexp constant) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-add constant left) (lw-complex-add constant right))
         (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-ordinary-polynomial-zero-comparison
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (lw-complex-diskp (lw-complex-laplace-point rate height) argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add (cons 1 0) (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 0 0)) (lw-complex-common-dirichlet-prefix nil nil rate height count request))
   (+ (* 3/2 ordinary-error) (* (- count 1) request))))
 :hints (("Goal"
  :use (lw-euler-dirichlet-nodes-prefix (:instance lw-euler-dirichlet-nodes-mass (log-error request))
        (:instance lw-complex-disk-data (point (lw-complex-laplace-point rate height)) (radius argument-cap))
        (:instance lw-euler-dirichlet-nodes-valid (log-error request))
        (:instance lw-exp-mixture-common-value-rational (nodes (lw-euler-dirichlet-nodes count request)) (point (lw-complex-laplace-point rate height)))
        (:instance lw-exp-mixture-affine-polynomial-valid (nodes (lw-euler-dirichlet-nodes count request)) (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (error ordinary-error))
        (:instance lw-exp-mixture-affine-common-comparison
         (nodes (lw-euler-dirichlet-nodes count request)) (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (point (cons 0 0)) (error ordinary-error))
        (:instance lw-complex-polynomial-at-zero (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)) (target 0) (offset 0)))
  :in-theory (union-theories
 '(lw-euler-ordinary-polynomial lw-epd-translate-difference lw-complexp lw-complex-mul-zero lw-complex-add-zero lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-epd-three-term-residual
 (implies (and (lw-complexp constant) (lw-complexp left1) (lw-complexp right1) (lw-complexp left2) (lw-complexp right2) (lw-complexp left3) (lw-complexp right3))
  (equal (lw-complex-sub (lw-complex-add (lw-complex-add (lw-complex-mul constant left1) left2) left3) (lw-complex-add (lw-complex-add (lw-complex-mul constant right1) right2) right3)) (lw-complex-add (lw-complex-add (lw-complex-mul constant (lw-complex-sub left1 right1)) (lw-complex-sub left2 right2)) (lw-complex-sub left3 right3))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(local (defthm lw-epd-three-term-error
 (implies (and (and (lw-complexp constant) (lw-complexp left1) (lw-complexp right1) (lw-complexp left2) (lw-complexp right2) (lw-complexp left3) (lw-complexp right3))
               (lw-complex-diskp constant cap)
               (lw-complex-diskp (lw-complex-sub left1 right1) error1)
               (lw-complex-diskp (lw-complex-sub left2 right2) error2)
               (lw-complex-diskp (lw-complex-sub left3 right3) error3))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add (lw-complex-add (lw-complex-mul constant left1) left2) left3) (lw-complex-add (lw-complex-add (lw-complex-mul constant right1) right2) right3))
   (+ (* cap error1) error2 error3)))
 :hints (("Goal"
  :use (lw-epd-three-term-residual
        (:instance lw-complex-mul-disk (left constant) (right (lw-complex-sub left1 right1)) (radius cap) (other-radius error1))
        (:instance lw-complex-add-disk (left (lw-complex-mul constant (lw-complex-sub left1 right1))) (right (lw-complex-sub left2 right2)) (radius (* cap error1)) (other-radius error2))
        (:instance lw-complex-add-disk (left (lw-complex-add (lw-complex-mul constant (lw-complex-sub left1 right1)) (lw-complex-sub left2 right2))) (right (lw-complex-sub left3 right3)) (radius (+ (* cap error1) error2)) (other-radius error3)))
  :in-theory (union-theories
 '( lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defun lw-complex-euler-prefix-derivative (rate height count request)
 (lw-complex-add
  (lw-complex-add
   (lw-complex-mul (cons (- rate 1) height) (lw-complex-scale -1 (lw-complex-common-dirichlet-prefix nil t rate height count request)))
   (lw-complex-common-dirichlet-prefix nil nil rate height count request))
  (lw-complex-scale -1 (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request))) (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request)))))

(local (in-theory (disable lw-complex-euler-prefix-derivative)))

(defthm lw-euler-prefix-polynomial-first-common-comparison
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (lw-complex-diskp (lw-complex-laplace-point rate height) argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp boundary-error) (< 0 boundary-error)
               (rationalp error) (< 0 error) (<= (lw-euler-derivative-target count request argument-cap error) target))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-coefficient-at (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error) 1 0)
                   (lw-complex-euler-prefix-derivative rate height count request))
   (+ (* (+ rate (abs height) 1) (+ (* 3/2 error) (* count count request)))
      (* 3/2 ordinary-error) (* (- count 1) request)
      (* 3/2 error) (* (+ 1 count) (+ 1 count) request))))
 :hints (("Goal"
  :use (lw-euler-prefix-polynomial-linear-coefficient
        lw-euler-ordinary-polynomial-first-comparison
        lw-euler-boundary-polynomial-first-comparison
        lw-euler-ordinary-polynomial-zero-comparison
        lw-complex-zeta-shifted-point-cap
        lw-euler-prefix-polynomial-components-valid
        (:instance lw-complex-disk-data (point (lw-complex-laplace-point rate height)) (radius argument-cap))
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp nil) (error request))
        (:instance lw-complex-common-dirichlet-prefix-rational (mangoldtp nil) (logp t) (error request))
        (:instance lw-log-bounds-interval (value (+ 1 count)) (epsilon request))
        (:instance lw-complex-log-ramp-independent-exp-rational (index (+ 1 count)) (log-error request) (delta request))
        (:instance lw-epd-three-term-error
         (constant (cons (- rate 1) height)) (cap (+ rate (abs height) 1))
         (left1 (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 1 0)) (right1 (lw-complex-scale -1 (lw-complex-common-dirichlet-prefix nil t rate height count request)))
         (left2 (lw-complex-add (cons 1 0) (lw-complex-coefficient-at (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) 0 0))) (right2 (lw-complex-common-dirichlet-prefix nil nil rate height count request))
         (left3 (lw-complex-coefficient-at (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error) 1 0)) (right3 (lw-complex-scale -1 (lw-complex-scale (* (+ 1 count) (car (lw-log-bounds (+ 1 count) request))) (lw-complex-log-ramp-independent-exp rate height (+ 1 count) request request))))
         (error1 (+ (* 3/2 error) (* count count request)))
         (error2 (+ (* 3/2 ordinary-error) (* (- count 1) request)))
         (error3 (+ (* 3/2 error) (* (+ 1 count) (+ 1 count) request)))))
  :in-theory (union-theories
 '(lw-complex-euler-prefix-derivative lw-complex-coefficient-at-rational lw-complex-ring-rational lw-complex-scale-rational lw-complexp lw-intervalp lw-epd-left-commutes lw-epd-left-distributes lw-epd-fold-constants lw-epd-times-negative lw-epd-negative-times lw-epd-zero-times lw-epd-minus-one lw-epd-double-negative lw-epd-add-cancel lw-epd-double lw-epd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



