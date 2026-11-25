; Reflect actual normalized models on a computed right-plane disk.
(in-package "ACL2")
(include-book "euler-normalized-physical-comparison")
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
(local (in-theory (disable lw-euler-value-clearance-check lw-euler-local-normalized-radius
 lw-euler-local-normalized-cap lw-euler-local-normalized-polynomial
 lw-euler-zeta-clearance-request lw-polynomial-rescale lw-complex-polynomial)))
(local (defthm lw-eml-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eml-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eml-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eml-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eml-times-negative (a b) (b a)))
                 :in-theory (disable lw-eml-times-negative)))))

(local (defthm lw-eml-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eml-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eml-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eml-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eml-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eml-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eml-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eml-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eml-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eml-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eml-left-commutes)))))
(defun lw-euler-mellin-radius (rate height outer-radius anchor-error)
 (min (lw-euler-local-normalized-radius rate height outer-radius anchor-error) (* 1/2 (- rate 3))))
(local (in-theory (disable lw-euler-mellin-radius)))
(defthm lw-euler-mellin-radius-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate))
 (and (rationalp rate) (rationalp height)
      (rationalp (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
      (rationalp (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (< 0 (lw-euler-local-normalized-cap rate height outer-radius anchor-error))
      (rationalp (lw-euler-mellin-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-mellin-radius rate height outer-radius anchor-error)) (<= (lw-euler-mellin-radius rate height outer-radius anchor-error) (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
      (< (lw-euler-mellin-radius rate height outer-radius anchor-error) (- rate 3)) (< 3 (- rate (lw-euler-mellin-radius rate height outer-radius anchor-error)))))
 :hints (("Goal" :use (lw-euler-local-normalized-data)
 :in-theory (union-theories
 '(lw-euler-mellin-radius min lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-mellin-shift-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (lw-complex-diskp point (lw-euler-mellin-radius rate height outer-radius anchor-error)))
 (and (lw-complexp point) (lw-complex-diskp (lw-complex-scale -1 point) (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
      (rationalp (- rate (car point))) (< 3 (- rate (car point))) (rationalp (- height (cdr point)))
      (lw-euler-value-clearance-check (- rate (car point)) (- height (cdr point)) (lw-euler-zeta-clearance-request (- rate (car point)) (- height (cdr point))))))
 :hints (("Goal"
 :use (lw-euler-mellin-radius-data
       (:instance lw-complex-disk-data (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-scale-disk (factor -1) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-scale -1 point)) (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (cap (lw-euler-local-normalized-radius rate height outer-radius anchor-error)))
       (:instance lw-euler-disk-point-data (radius (lw-euler-mellin-radius rate height outer-radius anchor-error)) (offset (lw-complex-scale -1 point)))
       (:instance lw-euler-zeta-clearance-check (rate (- rate (car point))) (height (- height (cdr point)))))
 :in-theory (union-theories
 '(abs lw-complex-scale lw-complexp lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-mellin-sign-data
 (implies (natp index)
 (and (rationalp (lw-rational-power -1 index))
      (equal (abs (lw-rational-power -1 index)) 1)
      (equal (* (lw-rational-power -1 index) (lw-rational-power -1 index)) 1)))
 :hints (("Goal" :induct (lw-rational-power -1 index)
 :expand ((lw-rational-power -1 index))
 :in-theory (union-theories
 '(lw-rational-power lw-rational-power-rational abs lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t)))
(defun lw-euler-mellin-polynomial (rate height outer-radius anchor-error target error)
 (lw-polynomial-rescale (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) -1 0))
(local (in-theory (disable lw-euler-mellin-polynomial)))
(defthm lw-euler-mellin-polynomial-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error))
 (and (lw-complex-coefficientsp (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error)) (equal (len (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error)) (len (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-polynomial-valid
       (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)) (factor -1) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-mellin-polynomial lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-mellin-polynomial-evaluation
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (rationalp error) (< 0 error) (lw-complexp point))
 (equal (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-complex-polynomial (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) (lw-complex-scale -1 point) 0)))
 :hints (("Goal"
 :use (lw-euler-local-normalized-polynomial-valid
       (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)) (factor -1) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-mellin-polynomial lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-euler-mellin-polynomial-coefficient
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (natp index) (rationalp error) (< 0 error))
 (equal (lw-complex-coefficient-at (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) index 0)
  (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) index 0))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-polynomial-valid
       (:instance lw-polynomial-rescale-coefficient (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error)) (factor -1) (target index) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-mellin-polynomial lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-euler-mellin-polynomial-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp target) (rationalp error) (< 0 error) (lw-complex-diskp point (lw-euler-mellin-radius rate height outer-radius anchor-error)))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-mellin-polynomial rate height outer-radius anchor-error target error) point 0) (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal"
 :use (lw-euler-mellin-shift-data lw-euler-mellin-polynomial-evaluation
       (:instance lw-complex-euler-local-normalized-polynomial-cap (point (lw-complex-scale -1 point))))
 :in-theory (union-theories
 '( lw-eml-left-commutes lw-eml-left-distributes lw-eml-fold-constants lw-eml-times-negative lw-eml-negative-times lw-eml-zero-times lw-eml-minus-one lw-eml-double-negative lw-eml-add-cancel lw-eml-double lw-eml-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
