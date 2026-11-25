; A computed variation bound for a polynomial about the origin.
(in-package "ACL2")
(include-book "euler-uniform-derivative-bounds")
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

(local (in-theory (disable lw-euler-uniform-polynomial
 lw-complex-euler-continuation-value lw-polynomial-affine
 lw-polynomial-multiply-linear lw-polynomial-add-constant)))
(local (in-theory (disable lw-complex-polynomial lw-polynomial-divided-difference lw-polynomial-disk-cap)))
(local (defthm lw-pdi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pdi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pdi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pdi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pdi-times-negative (a b) (b a)))
                 :in-theory (disable lw-pdi-times-negative)))))

(local (defthm lw-pdi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pdi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pdi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pdi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pdi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pdi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pdi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pdi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pdi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pdi-left-commutes)))))

(defun lw-polynomial-disk-increment-cap (coefficients outer-radius)
 (lw-polynomial-disk-cap (lw-polynomial-divided-difference coefficients (cons 0 0)) outer-radius))

(local (in-theory (disable lw-polynomial-disk-increment-cap)))

(defthm lw-polynomial-disk-increment-cap-valid
 (implies (and (lw-complex-coefficientsp coefficients)
  (rationalp outer-radius) (<= 0 outer-radius))
 (and (rationalp (lw-polynomial-disk-increment-cap coefficients outer-radius)) (<= 0 (lw-polynomial-disk-increment-cap coefficients outer-radius))))
 :hints (("Goal"
 :use ((:instance lw-polynomial-divided-difference-valid (anchor (cons 0 0)))
       (:instance lw-polynomial-disk-cap-valid (coefficients (lw-polynomial-divided-difference coefficients (cons 0 0))) (radius outer-radius)))
 :in-theory (union-theories
 '(lw-polynomial-disk-increment-cap (:executable-counterpart lw-complexp) lw-pdi-left-commutes lw-pdi-left-distributes lw-pdi-fold-constants lw-pdi-times-negative lw-pdi-negative-times lw-pdi-zero-times lw-pdi-minus-one lw-pdi-double-negative lw-pdi-add-cancel lw-pdi-double lw-pdi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-polynomial-disk-increment-bound
 (implies (and (lw-complex-coefficientsp coefficients)
  (rationalp outer-radius) (<= 0 outer-radius)
  (lw-complex-diskp point radius) (<= radius outer-radius))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                 (lw-complex-polynomial coefficients (cons 0 0) 0))
  (* radius (lw-polynomial-disk-increment-cap coefficients outer-radius))))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-data)
       (:instance lw-complex-disk-enlarge (cap outer-radius))
       (:instance lw-polynomial-divided-difference-valid (anchor (cons 0 0)))
       (:instance lw-complex-polynomial-disk-cap-bound (coefficients (lw-polynomial-divided-difference coefficients (cons 0 0))) (radius outer-radius))
       (:instance lw-polynomial-divided-difference-identity (anchor (cons 0 0)))
       (:instance lw-complex-mul-disk
        (left point) (right (lw-complex-polynomial (lw-polynomial-divided-difference coefficients (cons 0 0)) point 0))
        (other-radius (lw-polynomial-disk-increment-cap coefficients outer-radius))))
 :in-theory (union-theories
 '(lw-polynomial-disk-increment-cap lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-pdi-left-commutes lw-pdi-left-distributes lw-pdi-fold-constants lw-pdi-times-negative lw-pdi-negative-times lw-pdi-zero-times lw-pdi-minus-one lw-pdi-double-negative lw-pdi-add-cancel lw-pdi-double lw-pdi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

