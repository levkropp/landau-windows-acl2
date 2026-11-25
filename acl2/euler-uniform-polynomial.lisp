(in-package "ACL2")

(include-book "euler-prefix-polynomial")

; Uniform finite polynomial approximants for the actual Euler Cauchy name.
; All coefficients and budgets depend on the disk, never on its evaluation point.

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

(local (defthm lw-eup-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eup-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eup-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eup-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eup-times-negative (a b) (b a)))
                 :in-theory (disable lw-eup-times-negative)))))

(local (defthm lw-eup-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eup-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eup-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eup-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eup-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eup-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eup-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eup-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eup-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eup-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eup-left-commutes)))))

(defun lw-euler-polynomial-argument-cap (rate height radius)
 (+ rate (abs height) (* 2 radius)))

(defun lw-euler-polynomial-factor-cap (rate height radius)
 (+ 1 (lw-euler-polynomial-argument-cap rate height radius)))

(defthm lw-euler-polynomial-caps-positive
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate))
  (and (rationalp (lw-euler-polynomial-argument-cap rate height radius))
       (< 0 (lw-euler-polynomial-argument-cap rate height radius))
       (rationalp (lw-euler-polynomial-factor-cap rate height radius))
       (< 0 (lw-euler-polynomial-factor-cap rate height radius))))
 :hints (("Goal" :use (lw-euler-disk-envelope-data)
  :in-theory (union-theories
   '(lw-euler-polynomial-argument-cap lw-euler-polynomial-factor-cap lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-polynomial-point-caps
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius))
  (and (lw-complexp point)
       (lw-complex-diskp
        (lw-complex-add (lw-complex-laplace-point rate height) (lw-complex-mul (cons -1 0) point))
        (lw-euler-polynomial-argument-cap rate height radius))
       (lw-complex-diskp (cons (+ rate (car point) -1) (+ height (cdr point)))
        (lw-euler-polynomial-factor-cap rate height radius))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data)
        (:instance lw-euler-disk-point-data (offset point))
        lw-euler-disk-envelope-data
        (:instance lw-complex-l1-bound
         (point (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point)))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-laplace-point (+ rate (car point)) (+ height (cdr point))))
         (radius (+ (+ rate (car point)) (abs (+ height (cdr point))))) 
         (cap (lw-euler-polynomial-argument-cap rate height radius)))
        (:instance lw-complex-zeta-shifted-point-cap
         (rate (+ rate (car point))) (height (+ height (cdr point))))
        (:instance lw-complex-disk-enlarge
         (point (cons (+ rate (car point) -1) (+ height (cdr point))))
         (radius (+ (+ rate (car point)) (abs (+ height (cdr point))) 1))
         (cap (lw-euler-polynomial-factor-cap rate height radius))))
  :in-theory (union-theories
   '(lw-euler-polynomial-argument-cap lw-euler-polynomial-factor-cap lw-complexp lw-complex-laplace-point lw-complex-add lw-complex-mul lw-complex-scale lw-complex-l1 abs lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-euler-polynomial-ordinary-error (rate height radius error)
 (* 1/4 error (/ (lw-euler-polynomial-factor-cap rate height radius))))

(defun lw-euler-polynomial-rounding-cost (rate height radius count)
 (+ (* (lw-euler-polynomial-factor-cap rate height radius) (- count 1)) (+ count 1)))

(defun lw-euler-polynomial-precision (rate height radius count error)
 (lw-euler-rounding-precision (lw-euler-polynomial-rounding-cost rate height radius count) (/ error 2)))

(local (in-theory (disable lw-euler-polynomial-argument-cap lw-euler-polynomial-factor-cap
 lw-euler-polynomial-ordinary-error lw-euler-polynomial-rounding-cost lw-euler-polynomial-precision)))

(defthm lw-euler-polynomial-budget-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (posp count) (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-polynomial-ordinary-error rate height radius error))
       (< 0 (lw-euler-polynomial-ordinary-error rate height radius error))
       (rationalp (lw-euler-polynomial-rounding-cost rate height radius count))
       (< 0 (lw-euler-polynomial-rounding-cost rate height radius count))
       (rationalp (lw-euler-polynomial-precision rate height radius count error))
       (< 0 (lw-euler-polynomial-precision rate height radius count error))
       (<= (lw-euler-polynomial-precision rate height radius count error) 1)
       (<= (* (lw-euler-polynomial-rounding-cost rate height radius count)
              (lw-euler-polynomial-precision rate height radius count error)) (/ error 4))))
 :hints (("Goal"
  :use (lw-euler-polynomial-caps-positive
        (:instance lw-eup-positive-product (a (* 1/4 error))
         (b (/ (lw-euler-polynomial-factor-cap rate height radius))))
        (:instance lw-eup-multiply-order (a 0) (b (- count 1))
         (factor (lw-euler-polynomial-factor-cap rate height radius)))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-polynomial-rounding-cost rate height radius count)) (error (/ error 2))))
  :in-theory (union-theories
   '(lw-euler-polynomial-ordinary-error lw-euler-polynomial-rounding-cost lw-euler-polynomial-precision lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-polynomial-budget-adequate
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (posp count) (rationalp error) (< 0 error) (rationalp request) (< 0 request)
               (<= request (lw-euler-polynomial-precision rate height radius count error)))
  (<= (+ (* (lw-euler-polynomial-factor-cap rate height radius)
            (+ (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius error)) (* (- count 1) request)))
         (* 3/8 error) (* (+ count 1) request))
      error))
 :hints (("Goal"
  :use (lw-euler-polynomial-caps-positive lw-euler-polynomial-budget-valid
        (:instance lw-eup-multiply-order (a request)
         (b (lw-euler-polynomial-precision rate height radius count error))
         (factor (lw-euler-polynomial-rounding-cost rate height radius count)))
        (:instance lw-eup-inverse-factor (divisor (lw-euler-polynomial-factor-cap rate height radius))
         (coefficient error)))
  :in-theory (union-theories
   '(lw-euler-polynomial-ordinary-error lw-euler-polynomial-rounding-cost lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-prefix-polynomial-computed
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (posp count) (natp target)
               (rationalp error) (< 0 error) (rationalp request) (< 0 request)
               (<= request (lw-euler-polynomial-precision rate height radius count error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial
     (lw-euler-prefix-polynomial rate height count request
      (lw-euler-polynomial-argument-cap rate height radius) target
      (lw-euler-polynomial-ordinary-error rate height radius error) (/ error 4)) point 0)
    (lw-complex-euler-dirichlet-prefix (+ rate (car point)) (+ height (cdr point)) count request))
   error))
 :hints (("Goal"
  :use (lw-euler-polynomial-caps-positive lw-euler-polynomial-point-caps
        lw-euler-polynomial-budget-valid lw-euler-polynomial-budget-adequate
        (:instance lw-euler-prefix-polynomial-error
         (argument-cap (lw-euler-polynomial-argument-cap rate height radius))
         (factor-cap (lw-euler-polynomial-factor-cap rate height radius))
         (ordinary-error (lw-euler-polynomial-ordinary-error rate height radius error))
         (boundary-error (/ error 4)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-polynomial
           (lw-euler-prefix-polynomial rate height count request
            (lw-euler-polynomial-argument-cap rate height radius) target
            (lw-euler-polynomial-ordinary-error rate height radius error) (/ error 4)) point 0)
          (lw-complex-euler-dirichlet-prefix (+ rate (car point)) (+ height (cdr point)) count request)))
         (radius (+ (* (lw-euler-polynomial-factor-cap rate height radius)
            (+ (* 3/2 (lw-euler-polynomial-ordinary-error rate height radius error)) (* (- count 1) request)))
                    (* 3/8 error) (* (+ count 1) request))) (cap error)))
  :in-theory (union-theories
   '( lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-eup-power-two-natural
 (natp (lw-rational-power 2 index))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-uniform-polynomial-block (rate height radius error)
 (lw-euler-disk-block-cutoff rate height radius (/ error 2)))

(defun lw-euler-uniform-polynomial-count (rate height radius error)
 (- (lw-rational-power 2 (lw-euler-uniform-polynomial-block rate height radius error)) 1))

(defun lw-euler-uniform-polynomial-request (rate height radius error)
 (min (lw-euler-rounding-precision
       (lw-euler-disk-transport-cost rate height radius
        (lw-euler-uniform-polynomial-block rate height radius error)) (/ error 2))
      (lw-euler-polynomial-precision rate height radius
       (lw-euler-uniform-polynomial-count rate height radius error) (/ error 2))))

(defun lw-euler-uniform-polynomial (rate height radius target error)
 (lw-euler-prefix-polynomial rate height
  (lw-euler-uniform-polynomial-count rate height radius error)
  (lw-euler-uniform-polynomial-request rate height radius error)
  (lw-euler-polynomial-argument-cap rate height radius) target
  (lw-euler-polynomial-ordinary-error rate height radius (/ error 2)) (/ error 8)))

(local (in-theory (disable lw-euler-uniform-polynomial-block lw-euler-uniform-polynomial-count
 lw-euler-uniform-polynomial-request lw-euler-uniform-polynomial)))

(defthm lw-euler-uniform-polynomial-indices
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (and (natp (lw-euler-uniform-polynomial-block rate height radius error))
       (<= 2 (lw-euler-uniform-polynomial-block rate height radius error))
       (equal (lw-euler-uniform-polynomial-block rate height radius error)
              (lw-euler-disk-block-cutoff rate height radius (/ error 2)))
       (posp (lw-euler-uniform-polynomial-count rate height radius error))))
 :hints (("Goal"
  :use ((:instance lw-euler-disk-constructors-valid (block 2) (error (/ error 2)))
        (:instance lw-eup-power-two-natural
         (index (lw-euler-uniform-polynomial-block rate height radius error)))
        (:instance lw-rational-power-bernoulli (base 2)
         (exponent (lw-euler-uniform-polynomial-block rate height radius error))))
  :in-theory (union-theories
   '(lw-euler-uniform-polynomial-count lw-euler-uniform-polynomial-block lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-uniform-polynomial-request-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (rationalp error) (< 0 error))
  (let ((request (lw-euler-uniform-polynomial-request rate height radius error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (<= request (lw-euler-rounding-precision
          (lw-euler-disk-transport-cost rate height radius
           (lw-euler-uniform-polynomial-block rate height radius error)) (/ error 2)))
        (<= request (lw-euler-polynomial-precision rate height radius
          (lw-euler-uniform-polynomial-count rate height radius error) (/ error 2))))))
 :hints (("Goal"
  :use (lw-euler-uniform-polynomial-indices
        (:instance lw-euler-disk-constructors-valid
         (block (lw-euler-uniform-polynomial-block rate height radius error)) (error (/ error 2)))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-disk-transport-cost rate height radius
          (lw-euler-uniform-polynomial-block rate height radius error))) (error (/ error 2)))
        (:instance lw-euler-polynomial-budget-valid (error (/ error 2))
         (count (lw-euler-uniform-polynomial-count rate height radius error))))
  :in-theory (union-theories
   '(lw-euler-uniform-polynomial-request min lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-uniform-polynomial-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (natp target) (rationalp error) (< 0 error))
  (lw-complex-coefficientsp (lw-euler-uniform-polynomial rate height radius target error)))
 :hints (("Goal"
  :use (lw-euler-uniform-polynomial-indices lw-euler-uniform-polynomial-request-data
        lw-euler-polynomial-caps-positive
        (:instance lw-euler-polynomial-budget-valid (error (/ error 2))
         (count (lw-euler-uniform-polynomial-count rate height radius error)))
        (:instance lw-euler-prefix-polynomial-components-valid
         (count (lw-euler-uniform-polynomial-count rate height radius error))
         (request (lw-euler-uniform-polynomial-request rate height radius error))
         (argument-cap (lw-euler-polynomial-argument-cap rate height radius))
         (ordinary-error (lw-euler-polynomial-ordinary-error rate height radius (/ error 2)))
         (boundary-error (/ error 8))))
  :in-theory (union-theories
   '(lw-euler-uniform-polynomial lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-uniform-polynomial-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (natp target)
               (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) point 0)
    (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
   (+ error (* 1/4 value-error))))
 :hints (("Goal"
  :use (lw-euler-uniform-polynomial-indices lw-euler-uniform-polynomial-request-data
        lw-euler-uniform-polynomial-valid
        (:instance lw-euler-disk-point-data (offset point))
        (:instance lw-complex-disk-data)
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius target error)))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car point))) (height (+ height (cdr point))) (error value-error))
        (:instance lw-complex-euler-dyadic-prefix-rational
         (rate (+ rate (car point))) (height (+ height (cdr point)))
         (count (lw-euler-uniform-polynomial-block rate height radius error))
         (error (lw-euler-uniform-polynomial-request rate height radius error)))
        (:instance lw-complex-euler-prefix-polynomial-computed (error (/ error 2))
         (count (lw-euler-uniform-polynomial-count rate height radius error))
         (request (lw-euler-uniform-polynomial-request rate height radius error)))
        (:instance lw-complex-euler-disk-fixed-truncation (offset point) (target-error (/ error 2))
         (error value-error) (block (lw-euler-uniform-polynomial-block rate height radius error))
         (request (lw-euler-uniform-polynomial-request rate height radius error)))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
         (right (lw-complex-euler-dyadic-prefix (+ rate (car point)) (+ height (cdr point))
          (lw-euler-uniform-polynomial-block rate height radius error)
          (lw-euler-uniform-polynomial-request rate height radius error)))
         (radius (+ (/ error 2) (* 1/4 value-error))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius target error) point 0))
         (middle (lw-complex-euler-dyadic-prefix (+ rate (car point)) (+ height (cdr point))
          (lw-euler-uniform-polynomial-block rate height radius error)
          (lw-euler-uniform-polynomial-request rate height radius error)))
         (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) value-error))
         (radius (/ error 2)) (other-radius (+ (/ error 2) (* 1/4 value-error)))))
  :in-theory (union-theories
   '(lw-euler-uniform-polynomial lw-euler-uniform-polynomial-count lw-complex-euler-dyadic-prefix lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-polynomial-cauchy-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error margin)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data)
        (:instance lw-euler-disk-point-data (offset point))
        (:instance lw-euler-uniform-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius left-target left-error)))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius right-target right-error)))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car point))) (height (+ height (cdr point))) (error (* 2 margin)))
        (:instance lw-complex-euler-uniform-polynomial-comparison (target left-target) (error left-error)
         (value-error (* 2 margin)))
        (:instance lw-complex-euler-uniform-polynomial-comparison (target right-target) (error right-error)
         (value-error (* 2 margin)))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (* 2 margin))) (radius (+ right-error (* 1/2 margin))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0)) (middle (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) (* 2 margin))) (right (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0))
         (radius (+ left-error (* 1/2 margin))) (other-radius (+ right-error (* 1/2 margin)))))
  :in-theory (union-theories
   '( lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-uniform-polynomial-cauchy
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp point radius) (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error)))
  :use ((:instance lw-complex-disk-data)
        (:instance lw-euler-uniform-polynomial-valid (target left-target) (error left-error))
        (:instance lw-euler-uniform-polynomial-valid (target right-target) (error right-error))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius left-target left-error)))
        (:instance lw-complex-polynomial-rational (offset 0)
         (coefficients (lw-euler-uniform-polynomial rate height radius right-target right-error)))
        (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0)) (right (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0))) (radius (+ left-error right-error)) (cost 1))
        (:instance lw-complex-euler-uniform-polynomial-cauchy-with-margin
         (margin (lw-disk-gap-refinement
          (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius left-target left-error) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height radius right-target right-error) point 0)) (+ left-error right-error) 1))))
  :in-theory (union-theories
   '( lw-eup-left-commutes lw-eup-left-distributes lw-eup-fold-constants lw-eup-times-negative lw-eup-negative-times lw-eup-zero-times lw-eup-minus-one lw-eup-double-negative lw-eup-add-cancel lw-eup-double lw-eup-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))



