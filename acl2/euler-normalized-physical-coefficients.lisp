(in-package "ACL2")

(include-book "euler-normalized-coefficient-values")
(include-book "euler-local-coefficients")

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

(local (in-theory (disable lw-euler-local-normalized-polynomial lw-euler-local-normalized-coefficient-polynomial
 lw-complex-euler-local-normalized-polynomial-coefficient lw-complex-euler-local-normalized-coefficient-value lw-euler-local-normalized-cap
 lw-complex-coefficient-at lw-polynomial-rescale lw-complex-power)))

(local (defthm lw-npc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-npc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-npc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-npc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-npc-times-negative (a b) (b a)))
                 :in-theory (disable lw-npc-times-negative)))))

(local (defthm lw-npc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-npc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-npc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-npc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-npc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-npc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-npc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-npc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-npc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-npc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-npc-left-commutes)))))

(local (defthm lw-npc-request-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
 (and (rationalp (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (< 0 (lw-euler-local-normalized-radius rate height outer-radius anchor-error))
      (rationalp (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (< 0 (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))
      (rationalp (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)) (< 0 (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)) (<= (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error) 1)
      (<= (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error) (* error (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))
      (<= (* (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)) error)))
 :hints (("Goal" :use (lw-euler-local-normalized-data
       (:instance lw-euler-local-coefficient-request-valid (radius (lw-euler-local-normalized-radius rate height outer-radius anchor-error))))
 :in-theory (union-theories
 '( lw-npc-left-commutes lw-npc-left-distributes lw-npc-fold-constants lw-npc-times-negative lw-npc-negative-times lw-npc-zero-times lw-npc-minus-one lw-npc-double-negative lw-npc-add-cancel lw-npc-double lw-npc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-local-normalized-polynomial-coefficient-scaling
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (natp target) (rationalp error) (< 0 error))
  (equal (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error target index error)
         (lw-complex-scale (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)
          (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error) index 0))))
 :hints (("Goal"
  :use (lw-euler-local-normalized-data lw-euler-local-normalized-polynomial-valid
        (:instance lw-polynomial-rescale-coefficient
         (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error target error))
         (factor (lw-euler-local-normalized-radius rate height outer-radius anchor-error)) (target index) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-euler-local-normalized-polynomial-coefficient lw-euler-local-normalized-coefficient-polynomial lw-npc-left-commutes lw-npc-left-distributes lw-npc-fold-constants lw-npc-times-negative lw-npc-negative-times lw-npc-zero-times lw-npc-minus-one lw-npc-double-negative lw-npc-add-cancel lw-npc-double lw-npc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-euler-normalized-physical-coefficient-value (rate height outer-radius anchor-error index error)
 (lw-complex-scale (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error))))

(local (in-theory (disable lw-euler-local-coefficient-request lw-complex-euler-normalized-physical-coefficient-value)))

(defthm lw-complex-euler-normalized-physical-coefficient-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index error)))
 :hints (("Goal"
  :use (lw-npc-request-data
        (:instance lw-complex-euler-local-normalized-coefficient-value-rational (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)))
        (:instance lw-complex-scale-rational (factor (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))) (point (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)))))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-physical-coefficient-value lw-npc-left-commutes lw-npc-left-distributes lw-npc-fold-constants lw-npc-times-negative lw-npc-negative-times lw-npc-zero-times lw-npc-minus-one lw-npc-double-negative lw-npc-add-cancel lw-npc-double lw-npc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-normalized-physical-coefficient-identity
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
  (equal (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index error)
         (lw-complex-coefficient-at (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)) index 0)))
 :hints (("Goal"
  :use (lw-npc-request-data
        (:instance lw-euler-local-normalized-polynomial-valid (target index) (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)))
        (:instance lw-complex-coefficient-at-rational (offset 0) (target index)
         (coefficients (lw-euler-local-normalized-polynomial rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error))))
        (:instance lw-complex-euler-local-normalized-polynomial-coefficient-scaling (target index) (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)))
        (:instance lw-npc-inverse-factor (divisor (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (coefficient 1)))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-physical-coefficient-value lw-complex-euler-local-normalized-coefficient-value lw-complex-scale-compose lw-complex-scale-one lw-npc-left-commutes lw-npc-left-distributes lw-npc-fold-constants lw-npc-times-negative lw-npc-negative-times lw-npc-zero-times lw-npc-minus-one lw-npc-double-negative lw-npc-add-cancel lw-npc-double lw-npc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-normalized-physical-coefficient-cauchy
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
  :use ((:instance lw-npc-request-data (error left-error))
        (:instance lw-npc-request-data (error right-error))
        (:instance lw-complex-euler-local-normalized-coefficient-value-rational (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index left-error)))
        (:instance lw-complex-euler-local-normalized-coefficient-value-rational (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index right-error)))
        (:instance lw-complex-euler-local-normalized-coefficient-value-cauchy
         (left-error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index left-error)) (right-error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index right-error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index left-error)) (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index right-error))))
         (factor (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))) (radius (* 1/2 (+ (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index left-error) (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index right-error)))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index left-error) (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index right-error)))
         (radius (* (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)) (* 1/2 (+ (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index left-error) (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index right-error))))) (cap (* 1/2 (+ left-error right-error)))))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-physical-coefficient-value lw-complex-sub-scales abs lw-npc-left-commutes lw-npc-left-distributes lw-npc-fold-constants lw-npc-times-negative lw-npc-negative-times lw-npc-zero-times lw-npc-minus-one lw-npc-double-negative lw-npc-add-cancel lw-npc-double lw-npc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-normalized-physical-coefficient-cap
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp index) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-euler-normalized-physical-coefficient-value rate height outer-radius anchor-error index error)
   (* (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index)))))
 :hints (("Goal"
  :use (lw-npc-request-data
        (:instance lw-complex-euler-local-normalized-coefficient-value-cap (error (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error index (lw-euler-local-coefficient-request (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index error))) (factor (/ (lw-rational-power (lw-euler-local-normalized-radius rate height outer-radius anchor-error) index))) (radius (lw-euler-local-normalized-cap rate height outer-radius anchor-error))))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-physical-coefficient-value abs lw-npc-left-commutes lw-npc-left-distributes lw-npc-fold-constants lw-npc-times-negative lw-npc-negative-times lw-npc-zero-times lw-npc-minus-one lw-npc-double-negative lw-npc-add-cancel lw-npc-double lw-npc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))
