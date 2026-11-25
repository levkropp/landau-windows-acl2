; Compare actual normalized Euler polynomials with improper Mellin polynomials.
(in-package "ACL2")
(include-book "euler-mellin-local-polynomial")
(include-book "mellin-improper-polynomial")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-mellin-radius
 lw-euler-mellin-polynomial lw-euler-local-normalized-polynomial lw-euler-zeta-clearance-request
 lw-complex-polynomial lw-mellin-integral lw-mellin-euler-log-extended-value
 lw-mellin-improper-polynomial)))
(local (defthm lw-empc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-empc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-empc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-empc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-empc-times-negative (a b) (b a)))
                 :in-theory (disable lw-empc-times-negative)))))

(local (defthm lw-empc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-empc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-empc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-empc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-empc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-empc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-empc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-empc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-empc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-empc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-empc-left-commutes)))))
(local (defthm lw-empc-value-with-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (lw-complex-diskp point (lw-euler-mellin-radius rate height outer-radius anchor-error)) (natp target) (rationalp error) (< 0 error) (rationalp integral-error) (< 0 integral-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error)) (+ (+ (* 1/2 error) (* 5 integral-error)) margin)))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data lw-euler-mellin-shift-data lw-euler-mellin-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-mellin-integral-rational (sigma (- rate (car point))) (height (- height (cdr point))) (index 0) (error integral-error))
       (:instance lw-mellin-euler-log-extended-value-rational (rate (- rate (car point))) (height (- height (cdr point))) (radius (* 1/2 (- rate (car point)))) (anchor-error (lw-euler-zeta-clearance-request (- rate (car point)) (- height (cdr point)))) (error margin))
       (:instance lw-complex-euler-local-normalized-comparison (point (lw-complex-scale -1 point)) (local-anchor (lw-euler-zeta-clearance-request (- rate (car point)) (- height (cdr point)))) (coefficient-radius (* 1/2 (- rate (car point)))) (value-error margin))
       (:instance lw-mellin-euler-log-extended-right-comparison (rate (- rate (car point))) (height (- height (cdr point))) (radius (* 1/2 (- rate (car point)))) (euler-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error)) (right (lw-mellin-euler-log-extended-value (- rate (car point)) (- height (cdr point)) (* 1/2 (- rate (car point))) (lw-euler-zeta-clearance-request (- rate (car point)) (- height (cdr point))) margin)) (radius (+ (* 5 integral-error) (* 1/2 margin))))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0)) (middle (lw-mellin-euler-log-extended-value (- rate (car point)) (- height (cdr point)) (* 1/2 (- rate (car point))) (lw-euler-zeta-clearance-request (- rate (car point)) (- height (cdr point))) margin)) (right (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error))
        (radius (* 1/2 (+ error margin))) (other-radius (+ (* 5 integral-error) (* 1/2 margin)))))
 :in-theory (union-theories
 '(lw-euler-mellin-polynomial-evaluation lw-complex-scale lw-complexp lw-empc-left-commutes lw-empc-left-distributes lw-empc-fold-constants lw-empc-times-negative lw-empc-negative-times lw-empc-zero-times lw-empc-minus-one lw-empc-double-negative lw-empc-add-cancel lw-empc-double lw-empc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-complex-euler-mellin-polynomial-value-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (lw-complex-diskp point (lw-euler-mellin-radius rate height outer-radius anchor-error)) (natp target) (rationalp error) (< 0 error) (rationalp integral-error) (< 0 integral-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error)) (+ (* 1/2 error) (* 5 integral-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error)) (+ (* 1/2 error) (* 5 integral-error))))
 :use (lw-euler-mellin-radius-data lw-euler-mellin-shift-data lw-euler-mellin-polynomial-valid
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error)) (offset 0))
       (:instance lw-mellin-integral-rational (sigma (- rate (car point))) (height (- height (cdr point))) (index 0) (error integral-error))
       (:instance lw-complex-operations-rational (left (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0)) (right (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error))) (radius (+ (* 1/2 error) (* 5 integral-error))) (cost 1))
       (:instance lw-empc-value-with-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 integral-error)) (+ (* 1/2 error) (* 5 integral-error)) 1))))
 :in-theory (union-theories
 '( lw-empc-left-commutes lw-empc-left-distributes lw-empc-fold-constants lw-empc-times-negative lw-empc-negative-times lw-empc-zero-times lw-empc-minus-one lw-empc-double-negative lw-empc-add-cancel lw-empc-double lw-empc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defun lw-euler-mellin-comparison-error (left-error right-error)
 (+ (* 1/2 left-error) (* 69/64 right-error)))
(local (in-theory (disable lw-euler-mellin-comparison-error)))
(defthm lw-euler-mellin-comparison-error-data
 (implies (and (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (and (rationalp (lw-euler-mellin-comparison-error left-error right-error))
      (< 0 (lw-euler-mellin-comparison-error left-error right-error))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-euler-mellin-comparison-error lw-empc-left-commutes lw-empc-left-distributes lw-empc-fold-constants lw-empc-times-negative lw-empc-negative-times lw-empc-zero-times lw-empc-minus-one lw-empc-double-negative lw-empc-add-cancel lw-empc-double lw-empc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-complex-euler-mellin-polynomial-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (lw-complex-diskp point (lw-euler-mellin-radius rate height outer-radius anchor-error)) (natp left-target) (natp right-target)
 (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) point 0)) (lw-euler-mellin-comparison-error left-error right-error)))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data lw-euler-mellin-shift-data
       (:instance lw-euler-mellin-polynomial-valid (target left-target) (error left-error))
       (:instance lw-mellin-improper-polynomial-valid (sigma rate) (target right-target) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (error right-error))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error)) (offset 0))
       (:instance lw-mellin-integral-rational (sigma (- rate (car point))) (height (- height (cdr point))) (index 0) (error (* 1/64 right-error)))
       (:instance lw-complex-euler-mellin-polynomial-value-comparison (target left-target) (error left-error) (integral-error (* 1/64 right-error)))
       (:instance lw-mellin-computed-uniform-improper-polynomial (sigma rate) (target right-target) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (shift point) (error right-error))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) point 0)) (right (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 (* 1/64 right-error))) (radius right-error))
       (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) point 0)) (middle (lw-mellin-integral (- rate (car point)) (- height (cdr point)) 0 (* 1/64 right-error))) (right (lw-complex-polynomial (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) point 0))
        (radius (+ (* 1/2 left-error) (* 5/64 right-error))) (other-radius right-error))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error left-target left-error) point 0) (lw-complex-polynomial (lw-mellin-improper-polynomial rate height right-target (lw-euler-mellin-radius rate height outer-radius anchor-error) right-error) point 0)))
        (radius (+ (* 1/2 left-error) (* 5/64 right-error) right-error))
        (cap (lw-euler-mellin-comparison-error left-error right-error))))
 :in-theory (union-theories
 '(lw-euler-mellin-comparison-error lw-empc-left-commutes lw-empc-left-distributes lw-empc-fold-constants lw-empc-times-negative lw-empc-negative-times lw-empc-zero-times lw-empc-minus-one lw-empc-double-negative lw-empc-add-cancel lw-empc-double lw-empc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
