(in-package "ACL2")

(include-book "euler-quadratic-increment")
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

(local (in-theory (disable lw-euler-coefficient-polynomial lw-euler-uniform-coefficient-cap
 lw-complex-euler-polynomial-coefficient lw-complex-euler-coefficient-value
 lw-complex-polynomial lw-complex-coefficient-at lw-polynomial-difference lw-polynomial-pad
 lw-polynomial-coefficient-caps lw-polynomial-cap-index lw-complex-linear-remainder)))

(local (defthm lw-esc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esc-times-negative (a b) (b a)))
                 :in-theory (disable lw-esc-times-negative)))))

(local (defthm lw-esc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esc-left-commutes)))))

(defun lw-euler-series-coefficients (rate height radius start count error)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil
  (cons (lw-complex-euler-coefficient-value rate height radius start error)
        (lw-euler-series-coefficients rate height radius (+ 1 start) (- count 1) error))))

(defthm lw-euler-series-coefficients-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp start) (natp count) (rationalp error) (< 0 error))
  (and (lw-complex-coefficientsp (lw-euler-series-coefficients rate height radius start count error))
       (equal (len (lw-euler-series-coefficients rate height radius start count error)) count)))
 :hints (("Goal" :induct (lw-euler-series-coefficients rate height radius start count error)
  :in-theory (union-theories
   '(lw-euler-series-coefficients lw-complex-coefficientsp lw-complex-euler-coefficient-value-rational len lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(local (defun lw-esc-nth-induct (start count index)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (zp index)) start
  (lw-esc-nth-induct (+ 1 start) (- count 1) (- index 1)))))

(defthm lw-euler-series-coefficients-nth
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp start) (natp count) (natp index) (< index count)
               (rationalp error) (< 0 error))
  (equal (nth index (lw-euler-series-coefficients rate height radius start count error))
         (lw-complex-euler-coefficient-value rate height radius (+ start index) error)))
 :hints (("Goal" :induct (lw-esc-nth-induct start count index)
  :expand ((lw-euler-series-coefficients rate height radius start count error))
  :in-theory (union-theories
   '((:induction lw-esc-nth-induct) lw-euler-series-coefficients nth nfix lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defthm lw-euler-series-coefficients-caps
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp start) (natp count) (rationalp error) (< 0 error) (<= error 1))
  (lw-polynomial-coefficient-caps
   (lw-euler-series-coefficients rate height radius start count error)
   (lw-euler-uniform-coefficient-cap rate height radius)))
 :hints (("Goal" :induct (lw-euler-series-coefficients rate height radius start count error)
  :in-theory (union-theories
   '(lw-euler-series-coefficients lw-polynomial-coefficient-caps lw-complex-euler-coefficient-value-cap endp lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)))))

(defun lw-euler-series-prefix-difference (rate height radius count coefficient-error target polynomial-error)
 (lw-polynomial-difference (lw-euler-series-coefficients rate height radius 0 count coefficient-error) (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count)))

(local (in-theory (disable lw-euler-series-coefficients lw-euler-series-prefix-difference)))

(defthm lw-euler-series-prefix-difference-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp count) (natp target) (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (and (lw-complex-coefficientsp (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error)) (equal (len (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error)) count)))
 :hints (("Goal"
  :use ((:instance lw-euler-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-euler-polynomial-coefficient-rational (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)))
        (:instance lw-polynomial-difference-valid (left (lw-euler-series-coefficients rate height radius 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count))))
  :in-theory (union-theories
   '(lw-euler-series-prefix-difference lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-series-prefix-difference-caps
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp count) (natp target) (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error))
  (lw-polynomial-coefficient-caps (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error)))
 :hints (("Goal"
  :cases ((lw-polynomial-coefficient-caps (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error)))
  :use (lw-euler-series-prefix-difference-valid
        (:instance lw-euler-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-euler-polynomial-coefficient-rational (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)))
        (:instance lw-polynomial-cap-index-data (coefficients (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error)) (cap (+ coefficient-error polynomial-error)))
        (:instance lw-polynomial-difference-nth (left (lw-euler-series-coefficients rate height radius 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count)) (index (lw-polynomial-cap-index (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error))))
        (:instance lw-euler-series-coefficients-nth (start 0) (error coefficient-error) (index (lw-polynomial-cap-index (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error))))
        (:instance lw-polynomial-pad-nth (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)) (index (lw-polynomial-cap-index (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error))))
        (:instance lw-complex-euler-polynomial-coefficient-cauchy
         (left-target (lw-polynomial-cap-index (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error))) (right-target target) (index (lw-polynomial-cap-index (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error) (+ coefficient-error polynomial-error)))
         (left-error coefficient-error) (right-error polynomial-error)))
  :in-theory (union-theories
   '(lw-euler-series-prefix-difference lw-complex-euler-coefficient-value lw-complex-euler-polynomial-coefficient lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-euler-series-prefix (rate height radius count point error)
 (lw-complex-polynomial (lw-euler-series-coefficients rate height radius 0 count error) point 0))

(local (in-theory (disable lw-complex-euler-series-prefix)))

(defthm lw-complex-euler-series-prefix-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp count) (lw-complexp point) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-series-prefix rate height radius count point error)))
 :hints (("Goal"
  :use ((:instance lw-euler-series-coefficients-valid (start 0))
        (:instance lw-complex-polynomial-rational
         (coefficients (lw-euler-series-coefficients rate height radius 0 count error)) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-euler-series-prefix lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-esc-zero-power
 (equal (lw-rational-power base 0) 1)
 :hints (("Goal" :expand ((lw-rational-power base 0)) :in-theory (union-theories
   '( lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))))

(defthm lw-complex-euler-series-prefix-polynomial-comparison
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp count) (natp target) (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp polynomial-error) (< 0 polynomial-error) (lw-complex-diskp point 1/2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error)
                   (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target polynomial-error) point 0))
   (+ (* 2 (+ coefficient-error polynomial-error)) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-rational-power 1/2 count)))))
 :hints (("Goal"
  :use (lw-euler-series-prefix-difference-valid lw-euler-series-prefix-difference-caps
        lw-euler-uniform-coefficient-cap-valid
        (:instance lw-complex-disk-data (radius 1/2))
        (:instance lw-euler-series-coefficients-valid (start 0) (error coefficient-error))
        (:instance lw-euler-polynomial-coefficient-rational (index 0) (error polynomial-error))
        (:instance lw-polynomial-pad-valid (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-series-coefficients rate height radius 0 count coefficient-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count)) (offset 0))
        (:instance lw-polynomial-difference-evaluation (left (lw-euler-series-coefficients rate height radius 0 count coefficient-error)) (right (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count)) (offset 0))
        (:instance lw-complex-polynomial-coefficient-tail-bound
         (coefficients (lw-euler-series-prefix-difference rate height radius count coefficient-error target polynomial-error)) (cap (+ coefficient-error polynomial-error)) (radius 1/2) (offset 0))
        (:instance lw-euler-polynomial-coefficient-caps (error polynomial-error))
        (:instance lw-complex-polynomial-prefix-tail-bound
         (coefficients (lw-euler-coefficient-polynomial rate height radius target polynomial-error)) (cap (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error)) (radius 1/2))
        (:instance lw-complex-difference-symmetric
         (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target polynomial-error) point 0)) (right (lw-complex-polynomial (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count) point 0)) (radius (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-rational-power 1/2 count))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-series-coefficients rate height radius 0 count coefficient-error) point 0))
         (middle (lw-complex-polynomial (lw-polynomial-pad (lw-euler-coefficient-polynomial rate height radius target polynomial-error) count) point 0))
         (right (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target polynomial-error) point 0))
         (radius (* 2 (+ coefficient-error polynomial-error))) (other-radius (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-rational-power 1/2 count)))))
  :in-theory (union-theories
   '(lw-euler-series-prefix-difference lw-complex-euler-series-prefix lw-esc-zero-power lw-esc-left-commutes lw-esc-left-distributes lw-esc-fold-constants lw-esc-times-negative lw-esc-negative-times lw-esc-zero-times lw-esc-minus-one lw-esc-double-negative lw-esc-add-cancel lw-esc-double lw-esc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


