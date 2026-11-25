; Coefficients at a fixed center are coherent across all admissible radii.
; A single global polynomial compares both extractions; its budget is eliminated.
(in-package "ACL2")
(include-book "euler-shifted-coefficients")
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
(local (in-theory (disable lw-euler-shifted-polynomial lw-complex-euler-local-coefficient-value
 lw-complex-coefficient-at)))
(local (defthm lw-ecr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecr-times-negative)))))

(local (defthm lw-ecr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecr-left-commutes)))))

(local (defthm lw-ecr-power-data
 (implies (and (rationalp left-radius) (< 0 left-radius)
  (rationalp right-radius) (< 0 right-radius) (natp index))
 (and (rationalp (lw-rational-power left-radius index)) (< 0 (lw-rational-power left-radius index)) (rationalp (/ (lw-rational-power left-radius index))) (< 0 (/ (lw-rational-power left-radius index)))
      (rationalp (lw-rational-power right-radius index)) (< 0 (lw-rational-power right-radius index)) (rationalp (/ (lw-rational-power right-radius index))) (< 0 (/ (lw-rational-power right-radius index)))
      (rationalp (+ (/ (lw-rational-power left-radius index)) (/ (lw-rational-power right-radius index)))) (< 0 (+ (/ (lw-rational-power left-radius index)) (/ (lw-rational-power right-radius index))))))
 :hints (("Goal"
 :use ((:instance lw-rational-power-rational (base left-radius) (exponent index))
       (:instance lw-rational-power-positive (base left-radius) (exponent index))
       (:instance lw-rational-power-rational (base right-radius) (exponent index))
       (:instance lw-rational-power-positive (base right-radius) (exponent index))
       (:instance lw-reciprocal-positive (value (lw-rational-power left-radius index)))
       (:instance lw-reciprocal-positive (value (lw-rational-power right-radius index))))
 :in-theory (union-theories
 '( lw-ecr-left-commutes lw-ecr-left-distributes lw-ecr-fold-constants lw-ecr-times-negative lw-ecr-negative-times lw-ecr-zero-times lw-ecr-minus-one lw-ecr-double-negative lw-ecr-add-cancel lw-ecr-double lw-ecr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ecr-radius-comparison-with-model
 (implies (and (rationalp rate) (rationalp height)
 (rationalp left-radius) (< 0 left-radius) (< left-radius rate)
 (rationalp right-radius) (< 0 right-radius) (< right-radius rate)
 (natp index) (rationalp left-error) (< 0 left-error)
 (rationalp right-error) (< 0 right-error) (rationalp model-error) (< 0 model-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height left-radius index left-error) (lw-complex-euler-local-coefficient-value rate height right-radius index right-error))
  (+ left-error right-error (* model-error (+ (/ (lw-rational-power left-radius index)) (/ (lw-rational-power right-radius index)))))))
 :hints (("Goal"
 :use (lw-ecr-power-data
  (:instance lw-complex-zero-disk (radius (- (max left-radius right-radius) left-radius)))
  (:instance lw-complex-zero-disk (radius (- (max left-radius right-radius) right-radius)))
  (:instance lw-euler-uniform-polynomial-valid (radius (max left-radius right-radius)) (target index) (error model-error))
  (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-uniform-polynomial rate height (max left-radius right-radius) index model-error)) (target index) (offset 0))
  (:instance lw-complex-euler-local-coefficient-rational (radius left-radius) (error left-error))
  (:instance lw-complex-euler-local-coefficient-rational (radius right-radius) (error right-error))
  (:instance lw-euler-shifted-polynomial-at-zero (outer-radius (max left-radius right-radius)) (target index) (error model-error))
  (:instance lw-complex-euler-shifted-local-coefficient-comparison
   (outer-radius (max left-radius right-radius)) (center (cons 0 0)) (radius left-radius) (target index) (error model-error) (coefficient-error left-error))
  (:instance lw-complex-euler-shifted-local-coefficient-comparison
   (outer-radius (max left-radius right-radius)) (center (cons 0 0)) (radius right-radius) (target index) (error model-error) (coefficient-error right-error))
  (:instance lw-complex-difference-symmetric (left (lw-complex-coefficient-at (lw-euler-uniform-polynomial rate height (max left-radius right-radius) index model-error) index 0)) (right (lw-complex-euler-local-coefficient-value rate height left-radius index left-error)) (radius (+ (* model-error (/ (lw-rational-power left-radius index))) left-error)))
  (:instance lw-complex-difference-triangle (left (lw-complex-euler-local-coefficient-value rate height left-radius index left-error)) (middle (lw-complex-coefficient-at (lw-euler-uniform-polynomial rate height (max left-radius right-radius) index model-error) index 0)) (right (lw-complex-euler-local-coefficient-value rate height right-radius index right-error))
   (radius (+ (* model-error (/ (lw-rational-power left-radius index))) left-error)) (other-radius (+ (* model-error (/ (lw-rational-power right-radius index))) right-error)))
  (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height left-radius index left-error) (lw-complex-euler-local-coefficient-value rate height right-radius index right-error)))
   (radius (+ (* model-error (/ (lw-rational-power left-radius index))) left-error (* model-error (/ (lw-rational-power right-radius index))) right-error))
   (cap (+ left-error right-error (* model-error (+ (/ (lw-rational-power left-radius index)) (/ (lw-rational-power right-radius index))))))))
 :in-theory (union-theories
 '(max (:executable-counterpart lw-complexp) lw-ecr-left-commutes lw-ecr-left-distributes lw-ecr-fold-constants lw-ecr-times-negative lw-ecr-negative-times lw-ecr-zero-times lw-ecr-minus-one lw-ecr-double-negative lw-ecr-add-cancel lw-ecr-double lw-ecr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-local-coefficient-radius-comparison
 (implies (and (rationalp rate) (rationalp height)
 (rationalp left-radius) (< 0 left-radius) (< left-radius rate)
 (rationalp right-radius) (< 0 right-radius) (< right-radius rate)
 (natp index) (rationalp left-error) (< 0 left-error)
 (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height left-radius index left-error) (lw-complex-euler-local-coefficient-value rate height right-radius index right-error)) (+ left-error right-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height left-radius index left-error) (lw-complex-euler-local-coefficient-value rate height right-radius index right-error)) (+ left-error right-error)))
 :use (lw-ecr-power-data
  (:instance lw-complex-euler-local-coefficient-rational (radius left-radius) (error left-error))
  (:instance lw-complex-euler-local-coefficient-rational (radius right-radius) (error right-error))
  (:instance lw-complex-operations-rational (left (lw-complex-euler-local-coefficient-value rate height left-radius index left-error)) (right (lw-complex-euler-local-coefficient-value rate height right-radius index right-error)) (factor 1))
  (:instance lw-complex-disk-gap-refinement-excludes
   (point (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height left-radius index left-error) (lw-complex-euler-local-coefficient-value rate height right-radius index right-error))) (radius (+ left-error right-error)) (cost (+ (/ (lw-rational-power left-radius index)) (/ (lw-rational-power right-radius index)))))
  (:instance lw-ecr-radius-comparison-with-model
   (model-error (lw-disk-gap-refinement (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height left-radius index left-error) (lw-complex-euler-local-coefficient-value rate height right-radius index right-error)) (+ left-error right-error) (+ (/ (lw-rational-power left-radius index)) (/ (lw-rational-power right-radius index)))))))
 :in-theory (union-theories
 '( lw-ecr-left-commutes lw-ecr-left-distributes lw-ecr-fold-constants lw-ecr-times-negative lw-ecr-negative-times lw-ecr-zero-times lw-ecr-minus-one lw-ecr-double-negative lw-ecr-add-cancel lw-ecr-double lw-ecr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

