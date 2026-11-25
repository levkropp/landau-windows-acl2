(in-package "ACL2")

(include-book "euler-exponential-mixtures")
(include-book "polynomial-addition")

; Actual finite Euler polynomials in a centered complex parameter.
; Exponential degrees come from the existing uniform mixture constructor.

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

(local (defthm lw-epp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epp-times-negative (a b) (b a)))
                 :in-theory (disable lw-epp-times-negative)))))

(local (defthm lw-epp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epp-left-commutes)))))

(local (defthm lw-epp-point-rational
 (implies (and (rationalp rate) (rationalp height))
  (lw-complexp (lw-complex-laplace-point rate height)))
 :hints (("Goal" :in-theory (enable lw-complex-laplace-point lw-complexp)))
 :rule-classes nil))

(local (defthm lw-epp-shifted-identity
 (implies (and (rationalp rate) (rationalp height) (lw-complexp point))
  (equal (lw-complex-add (cons (- rate 1) height) (lw-complex-mul (cons 1 0) point))
         (cons (+ rate (car point) -1) (+ height (cdr point)))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-add lw-complex-mul lw-complex-scale lw-epp-left-commutes lw-epp-left-distributes lw-epp-fold-constants lw-epp-times-negative lw-epp-negative-times lw-epp-zero-times lw-epp-minus-one lw-epp-double-negative lw-epp-add-cancel lw-epp-double lw-epp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(local (defthm lw-epp-argument-identity
 (implies (and (rationalp rate) (rationalp height) (lw-complexp point))
  (equal (lw-complex-add (lw-complex-laplace-point rate height) (lw-complex-mul (cons -1 0) point))
         (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point)))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-laplace-point lw-complex-add lw-complex-mul lw-complex-scale lw-epp-left-commutes lw-epp-left-distributes lw-epp-fold-constants lw-epp-times-negative lw-epp-negative-times lw-epp-zero-times lw-epp-minus-one lw-epp-double-negative lw-epp-add-cancel lw-epp-double lw-epp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defun lw-euler-ordinary-polynomial (rate height count request argument-cap target ordinary-error)
 (lw-exp-mixture-affine-polynomial (lw-euler-dirichlet-nodes count request)
  (lw-complex-laplace-point rate height) (cons -1 0) argument-cap target ordinary-error))

(defun lw-euler-boundary-polynomial (rate height count request argument-cap target boundary-error)
 (lw-exp-mixture-affine-polynomial (lw-euler-boundary-nodes (+ 1 count) request)
  (lw-complex-laplace-point rate height) (cons -1 0) argument-cap target boundary-error))

(defun lw-euler-prefix-polynomial (rate height count request argument-cap target ordinary-error boundary-error)
 (lw-polynomial-add
  (lw-polynomial-multiply-linear (cons (- rate 1) height) (cons 1 0)
   (lw-polynomial-add-constant (cons 1 0)
    (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
  (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error)))

(local (in-theory (disable lw-euler-ordinary-polynomial lw-euler-boundary-polynomial lw-euler-prefix-polynomial)))

(defthm lw-euler-prefix-polynomial-components-valid
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (rationalp argument-cap) (<= 0 argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp boundary-error) (< 0 boundary-error))
  (and (lw-complex-coefficientsp (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))
       (lw-complex-coefficientsp (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error))
       (lw-complex-coefficientsp
        (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error))))
 :hints (("Goal"
  :use (lw-epp-point-rational
        (:instance lw-euler-dirichlet-nodes-valid (log-error request))
        (:instance lw-euler-boundary-nodes-valid (index (+ 1 count)) (log-error request))
        (:instance lw-exp-mixture-affine-polynomial-valid
         (nodes (lw-euler-dirichlet-nodes count request))
         (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (error ordinary-error))
        (:instance lw-exp-mixture-affine-polynomial-valid
         (nodes (lw-euler-boundary-nodes (+ 1 count) request))
         (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (error boundary-error))
        (:instance lw-polynomial-add-constant-valid (constant (cons 1 0))
         (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-polynomial-multiply-linear-valid (constant (cons (- rate 1) height)) (slope (cons 1 0))
         (coefficients (lw-polynomial-add-constant (cons 1 0)
          (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
        (:instance lw-polynomial-add-valid
         (left (lw-polynomial-multiply-linear (cons (- rate 1) height) (cons 1 0)
          (lw-polynomial-add-constant (cons 1 0)
           (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
         (right (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error))))
  :in-theory (union-theories
   '(lw-euler-ordinary-polynomial lw-euler-boundary-polynomial lw-euler-prefix-polynomial lw-complexp lw-epp-left-commutes lw-epp-left-distributes lw-epp-fold-constants lw-epp-times-negative lw-epp-negative-times lw-epp-zero-times lw-epp-minus-one lw-epp-double-negative lw-epp-add-cancel lw-epp-double lw-epp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-prefix-polynomial-evaluation
 (implies (and (rationalp rate) (rationalp height) (posp count)
               (rationalp request) (< 0 request) (rationalp argument-cap) (<= 0 argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp boundary-error) (< 0 boundary-error) (lw-complexp point))
  (equal
   (lw-complex-polynomial
    (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error) point 0)
   (lw-complex-add
    (lw-complex-mul (cons (+ rate (car point) -1) (+ height (cdr point)))
     (lw-complex-add (cons 1 0)
      (lw-complex-polynomial
       (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) point 0)))
    (lw-complex-polynomial
     (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error) point 0))))
 :hints (("Goal"
  :use (lw-euler-prefix-polynomial-components-valid
        (:instance lw-polynomial-add-constant-valid (constant (cons 1 0))
         (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-polynomial-multiply-linear-valid (constant (cons (- rate 1) height)) (slope (cons 1 0))
         (coefficients (lw-polynomial-add-constant (cons 1 0)
          (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
        (:instance lw-polynomial-add-evaluation (offset 0)
         (left (lw-polynomial-multiply-linear (cons (- rate 1) height) (cons 1 0)
          (lw-polynomial-add-constant (cons 1 0)
           (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
         (right (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error)))
        (:instance lw-polynomial-multiply-linear-evaluation (constant (cons (- rate 1) height)) (slope (cons 1 0))
         (coefficients (lw-polynomial-add-constant (cons 1 0)
          (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
        (:instance lw-polynomial-add-constant-evaluation (constant (cons 1 0))
         (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error))))
  :in-theory (union-theories
   '(lw-euler-prefix-polynomial lw-epp-shifted-identity lw-complexp lw-epp-left-commutes lw-epp-left-distributes lw-epp-fold-constants lw-epp-times-negative lw-epp-negative-times lw-epp-zero-times lw-epp-minus-one lw-epp-double-negative lw-epp-add-cancel lw-epp-double lw-epp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))
(local (defthm lw-epp-residual
 (implies (and (lw-complexp factor) (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
  (equal
   (lw-complex-sub
    (lw-complex-add (lw-complex-mul factor (lw-complex-add (cons 1 0) a)) b)
    (lw-complex-add (lw-complex-mul factor (lw-complex-add (cons 1 0) c)) d))
   (lw-complex-add (lw-complex-mul factor (lw-complex-sub a c)) (lw-complex-sub b d))))
 :hints (("Goal" :in-theory (union-theories
   '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-epp-left-commutes lw-epp-left-distributes lw-epp-fold-constants lw-epp-times-negative lw-epp-negative-times lw-epp-zero-times lw-epp-minus-one lw-epp-double-negative lw-epp-add-cancel lw-epp-double lw-epp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
                 :do-not-induct t))))

(defthm lw-euler-prefix-polynomial-error
 (implies (and (rationalp rate) (rationalp height) (posp count) (lw-complexp point)
               (rationalp request) (< 0 request) (rationalp argument-cap) (<= 0 argument-cap)
               (natp target) (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp boundary-error) (< 0 boundary-error)
               (lw-complex-diskp
                (lw-complex-add (lw-complex-laplace-point rate height) (lw-complex-mul (cons -1 0) point))
                argument-cap)
               (lw-complex-diskp (cons (+ rate (car point) -1) (+ height (cdr point))) factor-cap))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial
     (lw-euler-prefix-polynomial rate height count request argument-cap target ordinary-error boundary-error) point 0)
    (lw-complex-euler-dirichlet-prefix (+ rate (car point)) (+ height (cdr point)) count request))
   (+ (* factor-cap (+ (* 3/2 ordinary-error) (* (- count 1) request)))
      (* 3/2 boundary-error) (* (+ count 1) request))))
 :hints (("Goal"
  :use (lw-euler-prefix-polynomial-components-valid
        lw-epp-point-rational
        (:instance lw-epp-point-rational (rate (+ rate (car point))) (height (+ height (cdr point))))
        (:instance lw-complex-disk-data
         (point (cons (+ rate (car point) -1) (+ height (cdr point)))) (radius factor-cap))
        (:instance lw-euler-dirichlet-nodes-valid (log-error request))
        (:instance lw-euler-boundary-nodes-valid (index (+ 1 count)) (log-error request))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error)))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error)))
        (:instance lw-exp-mixture-common-value-rational
         (nodes (lw-euler-dirichlet-nodes count request))
         (point (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point)))))
        (:instance lw-exp-mixture-common-value-rational
         (nodes (lw-euler-boundary-nodes (+ 1 count) request))
         (point (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point)))))
        (:instance lw-exp-mixture-affine-common-comparison
         (nodes (lw-euler-dirichlet-nodes count request))
         (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (error ordinary-error))
        (:instance lw-exp-mixture-affine-common-comparison
         (nodes (lw-euler-boundary-nodes (+ 1 count) request))
         (center (lw-complex-laplace-point rate height)) (slope (cons -1 0)) (error boundary-error))
        (:instance lw-complex-mul-disk
         (left (cons (+ rate (car point) -1) (+ height (cdr point))))
         (right (lw-complex-sub
          (lw-complex-polynomial
           (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) point 0)
          (lw-exp-mixture-common-value (lw-euler-dirichlet-nodes count request)
           (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point))) request)))
         (radius factor-cap) (other-radius (+ (* 3/2 ordinary-error) (* (- count 1) request))))
        (:instance lw-complex-add-disk
         (left (lw-complex-mul (cons (+ rate (car point) -1) (+ height (cdr point)))
          (lw-complex-sub
           (lw-complex-polynomial
            (lw-euler-ordinary-polynomial rate height count request argument-cap target ordinary-error) point 0)
           (lw-exp-mixture-common-value (lw-euler-dirichlet-nodes count request)
            (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point))) request))))
         (right (lw-complex-sub
          (lw-complex-polynomial
           (lw-euler-boundary-polynomial rate height count request argument-cap target boundary-error) point 0)
          (lw-exp-mixture-common-value (lw-euler-boundary-nodes (+ 1 count) request)
           (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point))) request)))
         (radius (* factor-cap (+ (* 3/2 ordinary-error) (* (- count 1) request))))
         (other-radius (+ (* 3/2 boundary-error) (* (+ count 1) request)))))
  :in-theory (union-theories
   '(lw-euler-ordinary-polynomial lw-euler-boundary-polynomial lw-epp-argument-identity lw-epp-residual lw-euler-prefix-polynomial-evaluation lw-complex-euler-prefix-mixture-identity lw-euler-dirichlet-nodes-mass lw-euler-boundary-nodes-valid lw-complexp lw-epp-left-commutes lw-epp-left-distributes lw-epp-fold-constants lw-epp-times-negative lw-epp-negative-times lw-epp-zero-times lw-epp-minus-one lw-epp-double-negative lw-epp-add-cancel lw-epp-double lw-epp-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


