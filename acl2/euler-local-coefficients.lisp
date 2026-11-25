(in-package "ACL2")

(include-book "euler-coefficient-bounds")

; Physical coefficients, with precision compensating for the disk radius.
; These are actual polynomial coefficients, not assumed derivative data.

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

(local (in-theory (disable lw-euler-uniform-polynomial lw-euler-coefficient-polynomial
 lw-complex-euler-polynomial-coefficient lw-complex-euler-coefficient-value lw-euler-uniform-coefficient-cap
 lw-complex-coefficient-at lw-polynomial-rescale lw-complex-power)))

(local (defthm lw-elc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-elc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-elc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-elc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-elc-times-negative (a b) (b a)))
                 :in-theory (disable lw-elc-times-negative)))))

(local (defthm lw-elc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-elc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-elc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-elc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-elc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-elc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-elc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-elc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-elc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-elc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-elc-left-commutes)))))

(defthm lw-complex-euler-polynomial-coefficient-scaling
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp index) (natp target) (rationalp error) (< 0 error))
  (equal (lw-complex-euler-polynomial-coefficient rate height radius target index error)
         (lw-complex-scale (lw-rational-power radius index)
          (lw-complex-coefficient-at (lw-euler-uniform-polynomial rate height radius target error) index 0))))
 :hints (("Goal"
  :use (lw-euler-uniform-polynomial-valid
        (:instance lw-polynomial-rescale-coefficient
         (coefficients (lw-euler-uniform-polynomial rate height radius target error))
         (factor radius) (target index) (offset 0)))
  :in-theory (union-theories
   '(lw-complex-euler-polynomial-coefficient lw-euler-coefficient-polynomial lw-elc-left-commutes lw-elc-left-distributes lw-elc-fold-constants lw-elc-times-negative lw-elc-negative-times lw-elc-zero-times lw-elc-minus-one lw-elc-double-negative lw-elc-add-cancel lw-elc-double lw-elc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-euler-local-coefficient-request (radius index error)
 (min 1 (* error (lw-rational-power radius index))))

(defun lw-complex-euler-local-coefficient-value (rate height radius index error)
 (lw-complex-scale (/ (lw-rational-power radius index)) (lw-complex-euler-coefficient-value rate height radius index (lw-euler-local-coefficient-request radius index error))))

(local (in-theory (disable lw-euler-local-coefficient-request lw-complex-euler-local-coefficient-value)))

(defthm lw-euler-local-coefficient-request-valid
 (implies (and (rationalp radius) (< 0 radius) (natp index) (rationalp error) (< 0 error))
  (and (rationalp (lw-rational-power radius index)) (< 0 (lw-rational-power radius index))
       (rationalp (lw-euler-local-coefficient-request radius index error)) (< 0 (lw-euler-local-coefficient-request radius index error)) (<= (lw-euler-local-coefficient-request radius index error) 1)
       (<= (lw-euler-local-coefficient-request radius index error) (* error (lw-rational-power radius index)))
       (<= (* (/ (lw-rational-power radius index)) (lw-euler-local-coefficient-request radius index error)) error)))
 :hints (("Goal"
  :use ((:instance lw-rational-power-rational (base radius) (exponent index))
        (:instance lw-rational-power-positive (base radius) (exponent index))
        (:instance lw-elc-positive-product (a error) (b (lw-rational-power radius index)))
        (:instance lw-elc-multiply-order (a (lw-euler-local-coefficient-request radius index error)) (b (* error (lw-rational-power radius index))) (factor (/ (lw-rational-power radius index))))
        (:instance lw-elc-inverse-factor (divisor (lw-rational-power radius index)) (coefficient error)))
  :in-theory (union-theories
   '(lw-euler-local-coefficient-request min lw-elc-left-commutes lw-elc-left-distributes lw-elc-fold-constants lw-elc-times-negative lw-elc-negative-times lw-elc-zero-times lw-elc-minus-one lw-elc-double-negative lw-elc-add-cancel lw-elc-double lw-elc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-local-coefficient-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp index) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-local-coefficient-value rate height radius index error)))
 :hints (("Goal"
  :use (lw-euler-local-coefficient-request-valid
        (:instance lw-complex-euler-coefficient-value-rational (error (lw-euler-local-coefficient-request radius index error)))
        (:instance lw-complex-scale-rational (factor (/ (lw-rational-power radius index))) (point (lw-complex-euler-coefficient-value rate height radius index (lw-euler-local-coefficient-request radius index error)))))
  :in-theory (union-theories
   '(lw-complex-euler-local-coefficient-value lw-elc-left-commutes lw-elc-left-distributes lw-elc-fold-constants lw-elc-times-negative lw-elc-negative-times lw-elc-zero-times lw-elc-minus-one lw-elc-double-negative lw-elc-add-cancel lw-elc-double lw-elc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-local-coefficient-identity
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp index) (rationalp error) (< 0 error))
  (equal (lw-complex-euler-local-coefficient-value rate height radius index error)
         (lw-complex-coefficient-at (lw-euler-uniform-polynomial rate height radius index (lw-euler-local-coefficient-request radius index error)) index 0)))
 :hints (("Goal"
  :use (lw-euler-local-coefficient-request-valid
        (:instance lw-euler-uniform-polynomial-valid (target index) (error (lw-euler-local-coefficient-request radius index error)))
        (:instance lw-complex-coefficient-at-rational (offset 0) (target index)
         (coefficients (lw-euler-uniform-polynomial rate height radius index (lw-euler-local-coefficient-request radius index error))))
        (:instance lw-complex-euler-polynomial-coefficient-scaling (target index) (error (lw-euler-local-coefficient-request radius index error)))
        (:instance lw-elc-inverse-factor (divisor (lw-rational-power radius index)) (coefficient 1)))
  :in-theory (union-theories
   '(lw-complex-euler-local-coefficient-value lw-complex-euler-coefficient-value lw-complex-scale-compose lw-complex-scale-one lw-elc-left-commutes lw-elc-left-distributes lw-elc-fold-constants lw-elc-times-negative lw-elc-negative-times lw-elc-zero-times lw-elc-minus-one lw-elc-double-negative lw-elc-add-cancel lw-elc-double lw-elc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-local-coefficient-cauchy
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp index) (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius index left-error) (lw-complex-euler-local-coefficient-value rate height radius index right-error)) (+ left-error right-error)))
 :hints (("Goal"
  :use ((:instance lw-euler-local-coefficient-request-valid (error left-error))
        (:instance lw-euler-local-coefficient-request-valid (error right-error))
        (:instance lw-complex-euler-coefficient-value-rational (error (lw-euler-local-coefficient-request radius index left-error)))
        (:instance lw-complex-euler-coefficient-value-rational (error (lw-euler-local-coefficient-request radius index right-error)))
        (:instance lw-complex-euler-coefficient-value-cauchy
         (left-error (lw-euler-local-coefficient-request radius index left-error)) (right-error (lw-euler-local-coefficient-request radius index right-error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-euler-coefficient-value rate height radius index (lw-euler-local-coefficient-request radius index left-error)) (lw-complex-euler-coefficient-value rate height radius index (lw-euler-local-coefficient-request radius index right-error))))
         (factor (/ (lw-rational-power radius index))) (radius (+ (lw-euler-local-coefficient-request radius index left-error) (lw-euler-local-coefficient-request radius index right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-euler-local-coefficient-value rate height radius index left-error) (lw-complex-euler-local-coefficient-value rate height radius index right-error)))
         (radius (* (/ (lw-rational-power radius index)) (+ (lw-euler-local-coefficient-request radius index left-error) (lw-euler-local-coefficient-request radius index right-error)))) (cap (+ left-error right-error))))
  :in-theory (union-theories
   '(lw-complex-euler-local-coefficient-value lw-complex-sub-scales abs lw-elc-left-commutes lw-elc-left-distributes lw-elc-fold-constants lw-elc-times-negative lw-elc-negative-times lw-elc-zero-times lw-elc-minus-one lw-elc-double-negative lw-elc-add-cancel lw-elc-double lw-elc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-local-coefficient-cap
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate) (natp index) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-euler-local-coefficient-value rate height radius index error)
   (* (lw-euler-uniform-coefficient-cap rate height radius) (/ (lw-rational-power radius index)))))
 :hints (("Goal"
  :use (lw-euler-local-coefficient-request-valid
        (:instance lw-complex-euler-coefficient-value-cap (error (lw-euler-local-coefficient-request radius index error)))
        (:instance lw-complex-scale-disk
         (point (lw-complex-euler-coefficient-value rate height radius index (lw-euler-local-coefficient-request radius index error))) (factor (/ (lw-rational-power radius index))) (radius (lw-euler-uniform-coefficient-cap rate height radius))))
  :in-theory (union-theories
   '(lw-complex-euler-local-coefficient-value abs lw-elc-left-commutes lw-elc-left-distributes lw-elc-fold-constants lw-elc-times-negative lw-elc-negative-times lw-elc-zero-times lw-elc-minus-one lw-elc-double-negative lw-elc-add-cancel lw-elc-double lw-elc-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

