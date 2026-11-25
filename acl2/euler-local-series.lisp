(in-package "ACL2")

(include-book "euler-series-coefficients")

; Recover the actual Euler Cauchy name from its canonical coefficients.
; A computed half-disk tail cutoff makes this a finite rational evaluator.

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
 lw-complex-euler-continuation-value lw-complex-euler-series-prefix
 lw-complex-polynomial lw-complex-coefficient-at lw-rational-power
 lw-resolvent-truncation-count)))

(local (defthm lw-esr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esr-times-negative (a b) (b a)))
                 :in-theory (disable lw-esr-times-negative)))))

(local (defthm lw-esr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esr-left-commutes)))))

(local (defthm lw-esr-point-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (lw-complex-diskp point 1/2))
  (and (lw-complexp point) (lw-complex-diskp point 1) (lw-complex-diskp (lw-complex-scale radius point) radius)
       (rationalp (+ rate (car (lw-complex-scale radius point)))) (< 0 (+ rate (car (lw-complex-scale radius point))))
       (rationalp (+ height (cdr (lw-complex-scale radius point))))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-data (radius 1/2))
        (:instance lw-complex-disk-enlarge (radius 1/2) (cap 1))
        (:instance lw-complex-scale-disk (factor radius) (radius 1))
        (:instance lw-euler-disk-point-data (offset (lw-complex-scale radius point))))
  :in-theory (union-theories
   '(abs lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-esr-three-times
 (implies (rationalp x) (equal (* 3 x) (+ x (* 2 x))))
 :hints (("Goal" :use ((:instance distributivity (x x) (y 1) (z 2)))))))

(defthm lw-complex-euler-series-prefix-with-margin
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp count) (lw-complex-diskp point 1/2)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp value-error) (< 0 value-error) (rationalp polynomial-error) (< 0 polynomial-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (+ (* 2 coefficient-error) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 count)) (* 1/4 value-error)) (* (+ 3 (* 2 (lw-rational-power 1/2 count))) polynomial-error))))
 :hints (("Goal"
  :use (lw-esr-point-data
        (:instance lw-complex-euler-series-prefix-rational (error coefficient-error))
        (:instance lw-euler-polynomial-coefficient-rational (target 0) (index 0) (error polynomial-error))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius 0 polynomial-error)) (offset 0))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error value-error))
        (:instance lw-complex-euler-series-prefix-polynomial-comparison (target 0))
        (:instance lw-complex-euler-normalized-polynomial-comparison (target 0) (error polynomial-error))
        (:instance lw-complex-difference-triangle (left (lw-complex-euler-series-prefix rate height radius count point coefficient-error)) (middle (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius 0 polynomial-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))
         (radius (+ (* 2 (+ coefficient-error polynomial-error)) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) polynomial-error) (lw-rational-power 1/2 count))))
         (other-radius (+ polynomial-error (* 1/4 value-error)))))
  :in-theory (union-theories
   '(lw-esr-three-times lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-series-prefix-agreement
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
               (natp count) (lw-complex-diskp point 1/2)
               (rationalp coefficient-error) (< 0 coefficient-error)
               (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (* 2 coefficient-error) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 count)) (* 1/4 value-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (* 2 coefficient-error) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 count)) (* 1/4 value-error))))
  :use (lw-esr-point-data lw-euler-uniform-coefficient-cap-valid
        (:instance lw-rational-power-rational (base 1/2) (exponent count))
        (:instance lw-rational-power-positive (base 1/2) (exponent count))
        (:instance lw-complex-euler-series-prefix-rational (error coefficient-error))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error value-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-series-prefix rate height radius count point coefficient-error)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error))) (radius (+ (* 2 coefficient-error) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 count)) (* 1/4 value-error))) (cost (+ 3 (* 2 (lw-rational-power 1/2 count)))))
        (:instance lw-complex-euler-series-prefix-with-margin
         (polynomial-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-series-prefix rate height radius count point coefficient-error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (* 2 coefficient-error) (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 count)) (* 1/4 value-error)) (+ 3 (* 2 (lw-rational-power 1/2 count)))))))
  :in-theory (union-theories
   '( lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defun lw-euler-local-series-count (rate height radius error)
 (lw-resolvent-truncation-count 1/2 (* 1/8 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))))

(defun lw-euler-local-series-coefficient-error (error)
 (min 1 (/ error 8)))

(defun lw-complex-euler-local-series-value (rate height radius point error)
 (lw-complex-euler-series-prefix rate height radius (lw-euler-local-series-count rate height radius error) point (lw-euler-local-series-coefficient-error error)))

(local (in-theory (disable lw-euler-local-series-count lw-euler-local-series-coefficient-error
 lw-complex-euler-local-series-value)))

(local (defthm lw-esr-reciprocal-positive
 (implies (and (rationalp x) (< 0 x))
  (and (rationalp (/ x)) (< 0 (/ x))))
 :hints (("Goal" :use ((:instance inverse-of-* (x x))) :nonlinearp t))
 :rule-classes nil))

(defthm lw-euler-local-series-constructor-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (rationalp error) (< 0 error))
  (and (natp (lw-euler-local-series-count rate height radius error)) (< 0 (lw-euler-local-series-count rate height radius error))
       (rationalp (lw-euler-local-series-coefficient-error error)) (< 0 (lw-euler-local-series-coefficient-error error)) (<= (lw-euler-local-series-coefficient-error error) 1)
       (<= (* 2 (lw-euler-local-series-coefficient-error error)) (/ error 4))
       (<= (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 (lw-euler-local-series-count rate height radius error))) (/ error 4))))
 :hints (("Goal"
  :use (lw-euler-uniform-coefficient-cap-valid
        (:instance lw-esr-reciprocal-positive (x (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))
        (:instance lw-esr-positive-product (a (* 1/8 error)) (b (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)))))
        (:instance lw-resolvent-truncation-count-natural (radius 1/2) (error (* 1/8 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))))
        (:instance lw-rational-power-rational (base 1/2) (exponent (lw-euler-local-series-count rate height radius error)))
        (:instance lw-rational-power-nonnegative (base 1/2) (exponent (lw-euler-local-series-count rate height radius error)))
        (:instance lw-resolvent-truncation-count-adequate (radius 1/2) (error (* 1/8 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))))) (count (lw-euler-local-series-count rate height radius error)))
        (:instance lw-esr-multiply-order (a (lw-rational-power 1/2 (lw-euler-local-series-count rate height radius error))) (b (* 1/8 error (/ (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)))))
         (factor (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)))))
        (:instance lw-esr-inverse-factor (divisor (+ -1 (lw-euler-uniform-coefficient-cap rate height radius))) (coefficient error)))
  :in-theory (union-theories
   '(lw-euler-local-series-count lw-euler-local-series-coefficient-error min lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-local-series-value-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (lw-complexp point) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-local-series-value rate height radius point error)))
 :hints (("Goal"
  :use (lw-euler-local-series-constructor-data
        (:instance lw-complex-euler-series-prefix-rational (count (lw-euler-local-series-count rate height radius error)) (error (lw-euler-local-series-coefficient-error error))))
  :in-theory (union-theories
   '(lw-complex-euler-local-series-value lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-local-series-value-agreement
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (lw-complex-diskp point 1/2)
               (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)) (+ (/ error 2) (* 1/4 value-error))))
 :hints (("Goal"
  :use (lw-euler-local-series-constructor-data
        (:instance lw-complex-euler-series-prefix-agreement
         (count (lw-euler-local-series-count rate height radius error)) (coefficient-error (lw-euler-local-series-coefficient-error error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point error) (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) value-error)))
         (radius (+ (* 2 (lw-euler-local-series-coefficient-error error))
                    (* 2 (+ -1 (lw-euler-uniform-coefficient-cap rate height radius)) (lw-rational-power 1/2 (lw-euler-local-series-count rate height radius error))) (* 1/4 value-error)))
         (cap (+ (/ error 2) (* 1/4 value-error)))))
  :in-theory (union-theories
   '(lw-complex-euler-local-series-value lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-local-series-value-cauchy
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (lw-complex-diskp point 1/2)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error))))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error))))
  :use (lw-esr-point-data
        (:instance lw-complex-euler-local-series-value-rational (error left-error))
        (:instance lw-complex-euler-local-series-value-rational (error right-error))
        (:instance lw-complex-operations-rational (left (lw-complex-euler-local-series-value rate height radius point left-error)) (right (lw-complex-euler-local-series-value rate height radius point right-error)) (factor 1))
        (:instance lw-complex-disk-gap-refinement-excludes
         (point (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error))) (radius (* 1/2 (+ left-error right-error))) (cost 1))
        (:instance lw-complex-euler-local-series-value-agreement (error left-error) (value-error (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1))))
        (:instance lw-complex-euler-local-series-value-agreement (error right-error) (value-error (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1))))
        (:instance lw-complex-euler-continuation-value-rational
         (rate (+ rate (car (lw-complex-scale radius point)))) (height (+ height (cdr (lw-complex-scale radius point)))) (error (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1))))
        (:instance lw-complex-difference-symmetric (left (lw-complex-euler-local-series-value rate height radius point right-error)) (right (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1))))
         (radius (+ (* 1/2 right-error) (* 1/2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1)))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-euler-local-series-value rate height radius point left-error)) (middle (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale radius point))) (+ height (cdr (lw-complex-scale radius point))) (* 2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1)))) (right (lw-complex-euler-local-series-value rate height radius point right-error))
         (radius (+ (* 1/2 left-error) (* 1/2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1)))) (other-radius (+ (* 1/2 right-error) (* 1/2 (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-series-value rate height radius point left-error) (lw-complex-euler-local-series-value rate height radius point right-error)) (* 1/2 (+ left-error right-error)) 1))))))
  :in-theory (union-theories
   '( lw-esr-left-commutes lw-esr-left-distributes lw-esr-fold-constants lw-esr-times-negative lw-esr-negative-times lw-esr-zero-times lw-esr-minus-one lw-esr-double-negative lw-esr-add-cancel lw-esr-double lw-esr-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


