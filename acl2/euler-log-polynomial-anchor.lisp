; Polynomial quotient models respect every accepted value check and the gamma anchor.
(in-package "ACL2")
(include-book "euler-log-polynomial-cauchy")
(include-book "euler-log-derivative-anchor")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-neighborhood-radius
 lw-euler-uniform-log-polynomial lw-complex-polynomial lw-complex-euler-log-derivative-value lw-euler-bounds)))
(local (defthm lw-lpa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lpa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lpa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lpa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lpa-times-negative (a b) (b a)))
                 :in-theory (disable lw-lpa-times-negative)))))

(local (defthm lw-lpa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lpa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lpa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lpa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lpa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lpa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lpa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lpa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lpa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lpa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lpa-left-commutes)))))

(local (defthm lw-lpa-checked-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point)))
 (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (+ error value-error (* 2 margin))))
 :hints (("Goal"
 :use (lw-euler-neighborhood-shifted-check
       (:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       lw-euler-uniform-log-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error (* 1/2 anchor-error)) (error margin))
       (:instance lw-complex-euler-log-derivative-certificate-independence
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (left-anchor local-anchor)
        (right-anchor (* 1/2 anchor-error)) (left-error value-error) (right-error margin))
       (:instance lw-complex-euler-uniform-log-comparison (value-error margin))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (middle (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius (* 1/2 anchor-error) margin)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0))
        (radius (+ value-error margin)) (other-radius (+ error margin)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)))
        (radius (+ value-error margin error margin)) (cap (+ error value-error (* 2 margin)))))
 :in-theory (union-theories
 '( lw-lpa-left-commutes lw-lpa-left-distributes lw-lpa-fold-constants lw-lpa-times-negative lw-lpa-negative-times lw-lpa-zero-times lw-lpa-minus-one lw-lpa-double-negative lw-lpa-add-cancel lw-lpa-double lw-lpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-log-polynomial-checked-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
 (lw-complex-diskp point (lw-euler-neighborhood-radius rate height outer-radius anchor-error)) (rationalp coefficient-radius) (< 0 coefficient-radius) (< coefficient-radius (+ rate (car point)))
 (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) local-anchor)
 (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (+ error value-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (+ error value-error)))
 :use ((:instance lw-complex-disk-data (radius (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
       lw-euler-uniform-log-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational
        (rate (+ rate (car point))) (height (+ height (cdr point))) (radius coefficient-radius) (anchor-error local-anchor) (error value-error))
       (:instance lw-complex-operations-rational (left (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0))) (radius (+ error value-error)) (cost 2))
       (:instance lw-lpa-checked-with-margin
        (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-log-derivative-value (+ rate (car point)) (+ height (cdr point)) coefficient-radius local-anchor value-error) (lw-complex-polynomial (lw-euler-uniform-log-polynomial rate height outer-radius anchor-error target error) point 0)) (+ error value-error) 2))))
 :in-theory (union-theories
 '( lw-lpa-left-commutes lw-lpa-left-distributes lw-lpa-fold-constants lw-lpa-times-negative lw-lpa-negative-times lw-lpa-zero-times lw-lpa-minus-one lw-lpa-double-negative lw-lpa-add-cancel lw-lpa-double lw-lpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-lpa-gamma-rational
 (implies (and (rationalp gamma-error) (< 0 gamma-error)) (lw-complexp (cons (car (lw-euler-bounds gamma-error)) 0)))
 :hints (("Goal" :use ((:instance lw-euler-bounds-interval (epsilon gamma-error)))
 :in-theory (union-theories
 '(lw-intervalp lw-complexp lw-lpa-left-commutes lw-lpa-left-distributes lw-lpa-fold-constants lw-lpa-times-negative lw-lpa-negative-times lw-lpa-zero-times lw-lpa-minus-one lw-lpa-double-negative lw-lpa-add-cancel lw-lpa-double lw-lpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(local (defthm lw-lpa-anchor-with-margin
 (implies (and (natp target) (rationalp error) (< 0 error)
  (rationalp gamma-error) (< 0 gamma-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ error gamma-error (* 2 margin))))
 :hints (("Goal"
 :use (lw-euler-log-derivative-anchor-check lw-lpa-gamma-rational
       (:instance lw-euler-neighborhood-data (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64))
       (:instance lw-euler-value-anchor-clearance (anchor-error 1/128))
       (:instance lw-complex-zero-disk (radius (lw-euler-neighborhood-radius 1 0 1/2 1/64)))
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error)) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-euler-log-derivative-rational
        (rate 1) (height 0) (radius 1/4) (anchor-error 1/128) (error margin))
       (:instance lw-complex-euler-uniform-log-comparison (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64)
        (point (cons 0 0)) (coefficient-radius 1/4) (value-error margin))
       (:instance lw-complex-euler-log-derivative-anchor (radius 1/4) (anchor-error 1/128) (error margin))
       (:instance lw-complex-difference-symmetric (left (lw-complex-euler-log-derivative-value 1 0 1/4 1/128 margin)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0)) (radius (+ error margin)))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0)) (middle (lw-complex-euler-log-derivative-value 1 0 1/4 1/128 margin)) (right (cons (car (lw-euler-bounds gamma-error)) 0))
        (radius (+ error margin)) (other-radius (+ margin gamma-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0) (cons (car (lw-euler-bounds gamma-error)) 0)))
        (radius (+ error margin margin gamma-error)) (cap (+ error gamma-error (* 2 margin)))))
 :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-lpa-left-commutes lw-lpa-left-distributes lw-lpa-fold-constants lw-lpa-times-negative lw-lpa-negative-times lw-lpa-zero-times lw-lpa-minus-one lw-lpa-double-negative lw-lpa-add-cancel lw-lpa-double lw-lpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-log-polynomial-anchor
 (implies (and (natp target) (rationalp error) (< 0 error)
  (rationalp gamma-error) (< 0 gamma-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ error gamma-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ error gamma-error)))
 :use (lw-euler-log-derivative-anchor-check lw-lpa-gamma-rational
       (:instance lw-euler-uniform-log-polynomial-valid (rate 1) (height 0) (outer-radius 1/2) (anchor-error 1/64))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error)) (point (cons 0 0)) (offset 0))
       (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0)) (right (cons (car (lw-euler-bounds gamma-error)) 0)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0) (cons (car (lw-euler-bounds gamma-error)) 0))) (radius (+ error gamma-error)) (cost 2))
       (:instance lw-lpa-anchor-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-uniform-log-polynomial 1 0 1/2 1/64 target error) (cons 0 0) 0) (cons (car (lw-euler-bounds gamma-error)) 0)) (+ error gamma-error) 2))))
 :in-theory (union-theories
 '((:executable-counterpart lw-complexp) lw-lpa-left-commutes lw-lpa-left-distributes lw-lpa-fold-constants lw-lpa-times-negative lw-lpa-negative-times lw-lpa-zero-times lw-lpa-minus-one lw-lpa-double-negative lw-lpa-add-cancel lw-lpa-double lw-lpa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

