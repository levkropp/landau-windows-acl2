(in-package "ACL2")

(include-book "euler-normalized-coefficient-values")
(include-book "polynomial-prefix-bounds")

; Finite lists of canonical Euler coefficients recover polynomial prefixes.
; Different coefficient and polynomial requests remain independent.

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

(local (in-theory (disable lw-euler-local-normalized-coefficient-polynomial lw-euler-local-normalized-cap
 lw-complex-euler-local-normalized-polynomial-coefficient lw-complex-euler-local-normalized-coefficient-value
 lw-complex-polynomial lw-complex-coefficient-at lw-polynomial-difference lw-polynomial-pad
 lw-polynomial-coefficient-caps lw-polynomial-cap-index lw-complex-linear-remainder)))

(local (defthm lw-nsc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nsc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nsc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nsc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nsc-times-negative (a b) (b a)))
                 :in-theory (disable lw-nsc-times-negative)))))

(local (defthm lw-nsc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nsc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nsc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nsc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nsc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nsc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nsc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nsc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nsc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nsc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nsc-left-commutes)))))

(local (defthm lw-nsc-polynomial-data
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp target) (natp index) (rationalp error) (< 0 error))
 (and (lw-complex-coefficientsp (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target error)) (lw-complexp (lw-complex-euler-local-normalized-polynomial-coefficient rate height outer-radius anchor-error target index error))))
 :hints (("Goal"
 :use (lw-euler-local-normalized-coefficient-polynomial-valid
       lw-complex-euler-local-normalized-polynomial-coefficient-rational)
 :in-theory (union-theories
 '( lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defun lw-euler-normalized-series-coefficients (rate height outer-radius anchor-error start count error)
 (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp count) nil
  (cons (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error start error)
        (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error (+ 1 start) (- count 1) error))))

(defthm lw-euler-normalized-series-coefficients-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp start) (natp count) (rationalp error) (< 0 error))
  (and (lw-complex-coefficientsp (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error))
       (equal (len (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error)) count)))
 :hints (("Goal" :induct (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error)
  :in-theory (union-theories
   '(lw-euler-normalized-series-coefficients lw-complex-coefficientsp lw-complex-euler-local-normalized-coefficient-value-rational len lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defun lw-nsc-nth-induct (start count index)
 (declare (xargs :measure (nfix count) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (or (zp count) (zp index)) start
  (lw-nsc-nth-induct (+ 1 start) (- count 1) (- index 1)))))

(defthm lw-euler-normalized-series-coefficients-nth
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp start) (natp count) (natp index) (< index count)
               (rationalp error) (< 0 error))
  (equal (nth index (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error))
         (lw-complex-euler-local-normalized-coefficient-value rate height outer-radius anchor-error (+ start index) error)))
 :hints (("Goal" :induct (lw-nsc-nth-induct start count index)
  :expand ((lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error))
  :in-theory (union-theories
   '((:induction lw-nsc-nth-induct) lw-euler-normalized-series-coefficients nth nfix lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-euler-normalized-series-coefficients-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp start) (natp count) (rationalp error) (< 0 error))
  (lw-polynomial-coefficient-caps
   (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error)
   (lw-euler-local-normalized-cap rate height outer-radius anchor-error)))
 :hints (("Goal" :induct (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error start count error)
  :in-theory (union-theories
   '(lw-euler-normalized-series-coefficients lw-polynomial-coefficient-caps lw-complex-euler-local-normalized-coefficient-value-cap endp lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defun lw-euler-normalized-series-prefix-difference (rate height outer-radius anchor-error count coefficient-error target polynomial-error)
 (lw-polynomial-difference (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error) (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count)))

(local (in-theory (disable lw-euler-normalized-series-coefficients lw-euler-normalized-series-prefix-difference)))

(defthm lw-euler-normalized-series-prefix-difference-valid
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp count) (natp target) (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (and (lw-complex-coefficientsp (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error)) (equal (len (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error)) count)))
 :hints (("Goal"
  :use ((:instance lw-euler-normalized-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-nsc-polynomial-data (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)))
        (:instance lw-polynomial-difference-valid (left (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count))))
  :in-theory (union-theories
   '(lw-euler-normalized-series-prefix-difference lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-normalized-series-prefix-difference-caps
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp count) (natp target) (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (lw-polynomial-coefficient-caps (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error))))
 :hints (("Goal"
  :cases ((lw-polynomial-coefficient-caps (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error))))
  :use (lw-euler-normalized-series-prefix-difference-valid
        (:instance lw-euler-normalized-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-nsc-polynomial-data (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)))
        (:instance lw-polynomial-cap-index-data (coefficients (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error)) (cap (* 1/2 (+ coefficient-error polynomial-error))))
        (:instance lw-polynomial-difference-nth (left (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count)) (index (lw-polynomial-cap-index (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error)))))
        (:instance lw-euler-normalized-series-coefficients-nth (start 0) (error coefficient-error) (index (lw-polynomial-cap-index (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error)))))
        (:instance lw-polynomial-pad-nth (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)) (index (lw-polynomial-cap-index (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error)))))
        (:instance lw-complex-euler-local-normalized-polynomial-coefficient-cauchy
         (left-target (lw-polynomial-cap-index (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error)))) (right-target target) (index (lw-polynomial-cap-index (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error) (* 1/2 (+ coefficient-error polynomial-error))))
         (left-error coefficient-error) (right-error polynomial-error)))
  :in-theory (union-theories
   '(lw-euler-normalized-series-prefix-difference lw-complex-euler-local-normalized-coefficient-value lw-complex-euler-local-normalized-polynomial-coefficient lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-euler-normalized-series-prefix (rate height outer-radius anchor-error count point error)
 (lw-complex-polynomial (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count error) point 0))

(local (in-theory (disable lw-complex-euler-normalized-series-prefix)))

(defthm lw-complex-euler-normalized-series-prefix-rational
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate) (natp count) (lw-complexp point) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point error)))
 :hints (("Goal"
  :use ((:instance lw-euler-normalized-series-coefficients-valid (start 0))
        (:instance lw-complex-polynomial-rational
         (coefficients (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count error)) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-euler-normalized-series-prefix lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-nsc-zero-power
 (equal (lw-rational-power base 0) 1)
 :hints (("Goal" :expand ((lw-rational-power base 0)) :in-theory (union-theories
   '( lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-complex-euler-normalized-series-prefix-polynomial-comparison
 (implies (and (lw-euler-value-clearance-check rate height anchor-error)
 (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
               (natp count) (natp target) (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error) (lw-complex-diskp point 1/2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-normalized-series-prefix rate height outer-radius anchor-error count point coefficient-error)
                   (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) point 0))
   (+ (* 2 (* 1/2 (+ coefficient-error polynomial-error))) (* 2 (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-rational-power 1/2 count)))))
 :hints (("Goal"
  :use (lw-euler-normalized-series-prefix-difference-valid lw-euler-normalized-series-prefix-difference-caps
        lw-euler-local-normalized-data
        (:instance lw-complex-disk-data (radius 1/2))
        (:instance lw-euler-normalized-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-nsc-polynomial-data (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count)) (offset 0))
        (:instance lw-polynomial-difference-evaluation (left (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count)) (offset 0))
        (:instance lw-complex-polynomial-coefficient-tail-bound
         (coefficients (lw-euler-normalized-series-prefix-difference rate height outer-radius anchor-error count coefficient-error target polynomial-error)) (cap (* 1/2 (+ coefficient-error polynomial-error))) (radius 1/2) (offset 0))
        (:instance lw-euler-local-normalized-polynomial-coefficient-caps (error polynomial-error))
        (:instance lw-complex-polynomial-prefix-tail-bound
         (coefficients (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error)) (cap (lw-euler-local-normalized-cap rate height outer-radius anchor-error)) (radius 1/2))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) point 0)) (right (lw-complex-polynomial (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count) point 0)) (radius (* 2 (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-rational-power 1/2 count))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-normalized-series-coefficients rate height outer-radius anchor-error 0 count coefficient-error) point 0))
         (middle (lw-complex-polynomial (lw-polynomial-pad (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) count) point 0))
         (right (lw-complex-polynomial (lw-euler-local-normalized-coefficient-polynomial rate height outer-radius anchor-error target polynomial-error) point 0))
         (radius (* 2 (* 1/2 (+ coefficient-error polynomial-error)))) (other-radius (* 2 (lw-euler-local-normalized-cap rate height outer-radius anchor-error) (lw-rational-power 1/2 count)))))
  :in-theory (union-theories
   '(lw-euler-normalized-series-prefix-difference lw-complex-euler-normalized-series-prefix lw-nsc-zero-power lw-nsc-left-commutes lw-nsc-left-distributes lw-nsc-fold-constants lw-nsc-times-negative lw-nsc-negative-times lw-nsc-zero-times lw-nsc-minus-one lw-nsc-double-negative lw-nsc-add-cancel lw-nsc-double lw-nsc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))
