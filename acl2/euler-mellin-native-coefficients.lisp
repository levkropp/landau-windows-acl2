; Canonical right-plane coefficients use generated coarse checks only.
(in-package "ACL2")
(include-book "euler-mellin-moments")
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
(local (in-theory (disable lw-euler-zeta-clearance-request lw-euler-value-clearance-check
 lw-euler-local-normalized-radius lw-euler-local-normalized-cap
 lw-complex-euler-mellin-coefficient-value lw-complex-euler-normalized-physical-coefficient-value
 lw-rational-power lw-mellin-integral)))
(local (defthm lw-emn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-emn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-emn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-emn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-emn-times-negative (a b) (b a)))
                 :in-theory (disable lw-emn-times-negative)))))

(local (defthm lw-emn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-emn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-emn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-emn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-emn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-emn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-emn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-emn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-emn-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-emn-left-commutes)))))
(defun lw-complex-mellin-euler-coefficient-value (rate height index error)
 (lw-complex-euler-mellin-coefficient-value rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height) index error))
(defun lw-mellin-euler-coefficient-cap (rate height index)
 (* (lw-euler-local-normalized-cap rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height)) (/ (lw-rational-power (lw-euler-local-normalized-radius rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height)) index))))
(local (in-theory (disable lw-complex-mellin-euler-coefficient-value lw-mellin-euler-coefficient-cap)))
(defthm lw-mellin-euler-native-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
 (and (lw-euler-value-clearance-check rate height (lw-euler-zeta-clearance-request rate height))
      (rationalp (lw-euler-local-normalized-radius rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height))) (< 0 (lw-euler-local-normalized-radius rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height))) (rationalp (lw-euler-local-normalized-cap rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height))) (< 0 (lw-euler-local-normalized-cap rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height)))))
 :hints (("Goal"
 :use (lw-euler-zeta-clearance-check
       (:instance lw-euler-local-normalized-data (outer-radius (* 1/2 rate)) (anchor-error (lw-euler-zeta-clearance-request rate height))))
 :in-theory (union-theories
 '( lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-mellin-euler-coefficient-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (rationalp error) (< 0 error))
 (lw-complexp (lw-complex-mellin-euler-coefficient-value rate height index error)))
 :hints (("Goal" :use (lw-mellin-euler-native-data
       (:instance lw-complex-euler-mellin-coefficient-rational (outer-radius (* 1/2 rate)) (anchor-error (lw-euler-zeta-clearance-request rate height))))
 :in-theory (union-theories
 '(lw-complex-mellin-euler-coefficient-value lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-mellin-euler-coefficient-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-mellin-euler-coefficient-value rate height index left-error) (lw-complex-mellin-euler-coefficient-value rate height index right-error))
  (* 1/2 (+ left-error right-error))))
 :hints (("Goal" :use (lw-mellin-euler-native-data
       (:instance lw-complex-euler-mellin-coefficient-cauchy (outer-radius (* 1/2 rate)) (anchor-error (lw-euler-zeta-clearance-request rate height))))
 :in-theory (union-theories
 '(lw-complex-mellin-euler-coefficient-value lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-mellin-euler-coefficient-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value rate height index error) (lw-mellin-euler-coefficient-cap rate height index)))
 :hints (("Goal"
 :use (lw-mellin-euler-native-data lw-euler-mellin-sign-data
       (:instance lw-complex-euler-normalized-physical-coefficient-rational (outer-radius (* 1/2 rate)) (anchor-error (lw-euler-zeta-clearance-request rate height)))
       (:instance lw-complex-euler-normalized-physical-coefficient-cap (outer-radius (* 1/2 rate)) (anchor-error (lw-euler-zeta-clearance-request rate height)))
       (:instance lw-complex-scale-disk (factor (lw-rational-power -1 index))
        (point (lw-complex-euler-normalized-physical-coefficient-value rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height) index error))
        (radius (* (lw-euler-local-normalized-cap rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height)) (/ (lw-rational-power (lw-euler-local-normalized-radius rate height (* 1/2 rate) (lw-euler-zeta-clearance-request rate height)) index))))))
 :in-theory (union-theories
 '(lw-complex-mellin-euler-coefficient-value lw-complex-euler-mellin-coefficient-value lw-mellin-euler-coefficient-cap lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-mellin-euler-native-moment-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp integral-error) (< 0 integral-error))
 (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height index integral-error) (lw-complex-mellin-euler-coefficient-value rate height index coefficient-error)) (+ (* 5 integral-error) (* 1/2 coefficient-error))))
 :hints (("Goal" :use (lw-mellin-euler-native-data
       (:instance lw-mellin-euler-moment-comparison (outer-radius (* 1/2 rate)) (anchor-error (lw-euler-zeta-clearance-request rate height))))
 :in-theory (union-theories
 '(lw-complex-mellin-euler-coefficient-value lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-mellin-euler-native-computed-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp index) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-sub (lw-mellin-integral rate height index (* 1/10 error)) (lw-complex-mellin-euler-coefficient-value rate height index error)) error))
 :hints (("Goal"
 :use ((:instance lw-mellin-euler-native-moment-comparison (coefficient-error error) (integral-error (* 1/10 error))))
 :in-theory (union-theories
 '( lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


(local (defthm lw-emn-coefficient-agreement-margin
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-mellin-euler-coefficient-value rate height index right-error)) (+ (* 1/2 (+ left-error right-error)) (* 10 margin))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-data
       (:instance lw-complex-euler-mellin-coefficient-rational (error left-error))
       (:instance lw-complex-mellin-euler-coefficient-rational (error right-error))
       (:instance lw-mellin-integral-rational (sigma rate) (error margin))
       (:instance lw-mellin-euler-moment-comparison (coefficient-error left-error) (integral-error margin))
       (:instance lw-mellin-euler-native-moment-comparison (coefficient-error right-error) (integral-error margin))
       (:instance lw-complex-difference-symmetric (left (lw-mellin-integral rate height index margin)) (right (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error)) (radius (+ (* 5 margin) (* 1/2 left-error))))
       (:instance lw-complex-difference-triangle (left (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error)) (middle (lw-mellin-integral rate height index margin)) (right (lw-complex-mellin-euler-coefficient-value rate height index right-error))
        (radius (+ (* 5 margin) (* 1/2 left-error))) (other-radius (+ (* 5 margin) (* 1/2 right-error)))))
 :in-theory (union-theories
 '( lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(defthm lw-mellin-euler-native-coefficient-agreement
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (< 3 rate) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-mellin-euler-coefficient-value rate height index right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-mellin-euler-coefficient-value rate height index right-error)) (* 1/2 (+ left-error right-error))))
 :use (lw-euler-local-normalized-data
       (:instance lw-complex-euler-mellin-coefficient-rational (error left-error))
       (:instance lw-complex-mellin-euler-coefficient-rational (error right-error))
       (:instance lw-complex-operations-rational (left (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error)) (right (lw-complex-mellin-euler-coefficient-value rate height index right-error)) (factor 1))
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-mellin-euler-coefficient-value rate height index right-error))) (radius (* 1/2 (+ left-error right-error))) (cost 10))
       (:instance lw-emn-coefficient-agreement-margin (margin (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-mellin-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-mellin-euler-coefficient-value rate height index right-error)) (* 1/2 (+ left-error right-error)) 10))))
 :in-theory (union-theories
 '( lw-emn-left-commutes lw-emn-left-distributes lw-emn-fold-constants lw-emn-times-negative lw-emn-negative-times lw-emn-zero-times lw-emn-minus-one lw-emn-double-negative lw-emn-add-cancel lw-emn-double lw-emn-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

