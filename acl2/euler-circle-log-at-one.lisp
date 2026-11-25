(in-package "ACL2")

(include-book "euler-circle-factor-quotient")
(include-book "euler-anchor-derivative")

(defun lw-euler-circle-at-one-value-error (rate radius error value-error)
  (+ (* (lw-euler-circle-outer-gap (cons rate 0) radius) error) (* 1/2 value-error)))

(defun lw-euler-circle-at-one-derivative-error (error value-error)
  (+ error value-error (* 2 value-error)))

(defun lw-euler-circle-at-one-log-error (rate radius error epsilon value-error)
  (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius (cons rate 0) radius) radius) 1/8 (lw-euler-circle-global-derivative-cap (cons rate 0) radius)) epsilon) (+ (* 4 (lw-euler-circle-at-one-derivative-error error value-error)) (* 8 (lw-euler-circle-at-one-value-error rate radius error value-error)))))

(local (defthm lw-ecao-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecao-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecao-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecao-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecao-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecao-times-negative)))))

(local (defthm lw-ecao-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecao-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecao-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecao-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecao-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecao-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecao-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecao-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecao-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecao-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecao-left-commutes)))))

(local
 (defthm lw-ecao-real-pair
   (implies (rationalp value) (lw-complexp (cons value 0)))
   :hints (("Goal" :in-theory
             (union-theories '(lw-complexp car-cons cdr-cons)
                             (theory 'minimal-theory))))))

(local
 (defthm lw-ecao-shift-disk
   (implies (and (rationalp rate) (< 1 rate) (rationalp radius) (<= (- rate 1) radius))
            (lw-complex-diskp (cons (- 1 rate) 0) radius))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons (- 1 rate) 0)))
                  (:instance lw-ecao-multiply-order (a (- rate 1)) (b radius) (factor radius))
                  (:instance lw-ecao-multiply-order (a (- rate 1)) (b radius) (factor (- rate 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              lw-ecao-left-commutes lw-ecao-left-distributes lw-ecao-fold-constants
              lw-ecao-times-negative lw-ecao-negative-times lw-ecao-zero-times
              lw-ecao-minus-one lw-ecao-double-negative lw-ecao-add-cancel lw-ecao-double lw-ecao-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecao-gamma-data
   (implies (and (rationalp value-error) (< 0 value-error) (<= value-error 1))
            (lw-complex-diskp (cons (car (lw-euler-bounds value-error)) 0) 2))
   :hints (("Goal"
            :use ((:instance lw-euler-bounds-interval (epsilon value-error))
                  (:instance lw-euler-bounds-coarse (epsilon value-error))
                  (:instance lw-complex-disk-norm-square (point (cons (car (lw-euler-bounds value-error)) 0)) (radius 2))
                  (:instance lw-ecao-multiply-order
                    (a (- 2)) (b (car (lw-euler-bounds value-error)))
                    (factor (- (car (lw-euler-bounds value-error)))))
                  (:instance lw-ecao-multiply-order
                    (a (car (lw-euler-bounds value-error))) (b 2)
                    (factor (car (lw-euler-bounds value-error)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp lw-complexp lw-complex-norm-square
              lw-ecao-left-commutes lw-ecao-left-distributes lw-ecao-fold-constants
              lw-ecao-times-negative lw-ecao-negative-times lw-ecao-zero-times
              lw-ecao-minus-one lw-ecao-double-negative lw-ecao-add-cancel lw-ecao-double lw-ecao-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :cases ((< (car (lw-euler-bounds value-error)) 0))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-polynomial-at-one
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (rationalp rate) (< 1 rate) (<= (- rate 1) radius)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (rationalp value-error) (< 0 value-error) (<= value-error 1/4))
           (and (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0) (cons 1 0)) (lw-euler-circle-at-one-value-error rate radius error value-error))
                (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0)) (cons (car (lw-euler-bounds value-error)) 0)) (lw-euler-circle-at-one-derivative-error error value-error))
                (lw-complex-diskp (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0)) (lw-euler-circle-global-derivative-cap (cons rate 0) radius))))
  :hints (("Goal"
           :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                 lw-ecao-shift-disk
                 (:instance lw-complex-disk-enlarge (point (cons (- 1 rate) 0)) (radius radius) (cap (lw-euler-circle-outer-radius (cons rate 0) radius)))
                 (:instance lw-euler-circle-global-polynomials-valid (center (cons rate 0)))
                 (:instance lw-euler-circle-global-derivative-identity (center (cons rate 0)))
                 (:instance lw-polynomial-derivative-coefficients-evaluation
                   (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius target error)) (point (cons (- 1 rate) 0)))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius target error)) (point (cons (- 1 rate) 0)) (offset 0))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-global-derivative (cons rate 0) radius target error)) (point (cons (- 1 rate) 0)) (offset 0))
                 (:instance lw-complex-euler-continuation-value-rational (rate 1) (height 0) (error value-error))
                 (:instance lw-complex-euler-local-coefficient-rational (rate 1) (height 0) (radius 1/2) (index 1) (error value-error))
                 (:instance lw-complex-euler-uniform-polynomial-comparison
                   (height 0) (radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (point (cons (- 1 rate) 0)) (error (* (lw-euler-circle-outer-gap (cons rate 0) radius) error)))
                 (:instance lw-complex-euler-anchor-value (error value-error))
                 (:instance lw-complex-euler-uniform-derivative-comparison
                   (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (inner-radius radius) (center (cons (- 1 rate) 0))
                   (coefficient-radius 1/2) (coefficient-error value-error))
                 (:instance lw-complex-euler-anchor-derivative
                   (radius 1/2) (coefficient-error value-error) (gamma-error value-error))
                 (:instance lw-complex-euler-uniform-derivative-polynomial-cap
                   (height 0) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (inner-radius radius) (center (cons (- 1 rate) 0)))
                 lw-ecao-gamma-data
                 (:instance lw-complex-disk-data (point (cons (car (lw-euler-bounds value-error)) 0)) (radius 2))
                 (:instance lw-ecao-positive-product (a (lw-euler-circle-outer-gap (cons rate 0) radius)) (b error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0)) (middle (lw-complex-euler-continuation-value 1 0 value-error)) (right (cons 1 0))
                   (radius (+ (* (lw-euler-circle-outer-gap (cons rate 0) radius) error) (* 1/4 value-error))) (other-radius (* 1/4 value-error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-circle-global-derivative (cons rate 0) radius target error) (cons (- 1 rate) 0) 0)) (middle (lw-complex-euler-local-coefficient-value 1 0 1/2 1 value-error)) (right (cons (car (lw-euler-bounds value-error)) 0))
                   (radius (+ error value-error)) (other-radius (* 2 value-error))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-global-polynomial lw-euler-circle-global-derivative
              lw-euler-circle-global-derivative-cap lw-euler-circle-at-one-value-error
              lw-euler-circle-at-one-derivative-error lw-ecao-real-pair
              lw-ecao-left-commutes lw-ecao-left-distributes lw-ecao-fold-constants
              lw-ecao-times-negative lw-ecao-negative-times lw-ecao-zero-times
              lw-ecao-minus-one lw-ecao-double-negative lw-ecao-add-cancel lw-ecao-double lw-ecao-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecao-one-clearance
   (implies (and (lw-complexp value)
                 (lw-complex-diskp (lw-complex-sub value (cons 1 0)) 1/4))
            (and (not (lw-complex-diskp value 1/4))
                 (<= 1/16 (lw-complex-norm-square value))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-anchor-clearance (anchor (cons 1 0)) (point value))
                  (:instance lw-complex-disk-coordinates (point (lw-complex-sub value (cons 1 0))) (radius 1/4))
                  (:instance lw-complex-disk-coordinates (point value) (radius 1/4))
                  (:instance lw-complex-disk-data (point (lw-complex-sub value (cons 1 0))) (radius 1/4)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-l1 lw-complexp lw-complex-sub abs
              lw-ecao-left-commutes lw-ecao-left-distributes lw-ecao-fold-constants
              lw-ecao-times-negative lw-ecao-negative-times lw-ecao-zero-times
              lw-ecao-minus-one lw-ecao-double-negative lw-ecao-add-cancel lw-ecao-double lw-ecao-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-factor-log-at-one
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (rationalp rate) (< 1 rate) (<= (- rate 1) radius)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (rationalp value-error) (< 0 value-error) (<= value-error 1/4)
                (<= (* (lw-euler-circle-outer-gap (cons rate 0) radius) error) 1/8)
                (rationalp epsilon) (< 0 epsilon) (<= epsilon 1/8))
           (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots (cons rate 0) radius target error epsilon) (cons (- 1 rate) 0)) (cons (car (lw-euler-bounds value-error)) 0))
                             (lw-euler-circle-at-one-log-error rate radius error epsilon value-error)))
  :hints (("Goal"
           :use (lw-euler-circle-polynomial-at-one lw-ecao-gamma-data lw-ecao-shift-disk
                 (:instance lw-euler-circle-outer-data (center (cons rate 0)))
                 (:instance lw-euler-circle-global-polynomials-valid (center (cons rate 0)))
                 (:instance lw-euler-circle-global-derivative-cap-data (center (cons rate 0)))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius target error)) (point (cons (- 1 rate) 0)) (offset 0))
                 (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius target error)) (point (cons (- 1 rate) 0)))
                 (:instance lw-complex-disk-data (point (cons (car (lw-euler-bounds value-error)) 0)) (radius 2))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0) (cons 1 0))) (radius (lw-euler-circle-at-one-value-error rate radius error value-error)) (cap 1/4))
                 (:instance lw-ecao-one-clearance (value (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0)))
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius target error)) (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)))
                 (:instance lw-polynomial-factor-log-sum-rational
                   (roots (lw-polynomial-normalized-factor-roots (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (lw-euler-circle-outer-radius (cons rate 0) radius) epsilon))
                   (point (cons (- 1 rate) 0)))
                 (:instance lw-complex-quotient-rational (numerator (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0))) (denominator (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0)))
                 (:instance lw-polynomial-disk-factor-sum-error
                   (coefficients (lw-euler-circle-global-polynomial (cons rate 0) radius target error)) (center (cons (- 1 rate) 0))
                   (outer-radius (lw-euler-circle-outer-radius (cons rate 0) radius)) (inner-radius radius) (clearance 1/8) (numerator-cap (lw-euler-circle-global-derivative-cap (cons rate 0) radius)))
                 (:instance lw-complex-quotient-difference-bound
                   (numerator (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0))) (denominator (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0))
                   (approximate-numerator (cons (car (lw-euler-bounds value-error)) 0)) (approximate-denominator (cons 1 0))
                   (left-clearance 1/4) (right-clearance 1)
                   (numerator-cap 2) (numerator-error (lw-euler-circle-at-one-derivative-error error value-error)) (denominator-error (lw-euler-circle-at-one-value-error rate radius error value-error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots (cons rate 0) radius target error epsilon) (cons (- 1 rate) 0))) (middle (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0)) (lw-complex-polynomial (lw-euler-circle-global-polynomial (cons rate 0) radius target error) (cons (- 1 rate) 0) 0))) (right (cons (car (lw-euler-bounds value-error)) 0))
                   (radius (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius (cons rate 0) radius) radius) 1/8 (lw-euler-circle-global-derivative-cap (cons rate 0) radius)) epsilon)) (other-radius (+ (* 4 (lw-euler-circle-at-one-derivative-error error value-error)) (* 8 (lw-euler-circle-at-one-value-error rate radius error value-error))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-factor-roots lw-euler-circle-at-one-log-error
              lw-euler-circle-at-one-value-error lw-complex-norm-square
              lw-complex-quotient lw-complex-mul-one lw-ecao-real-pair (:executable-counterpart lw-complex-reciprocal)
              (:executable-counterpart lw-complexp)
              lw-ecao-left-commutes lw-ecao-left-distributes lw-ecao-fold-constants
              lw-ecao-times-negative lw-ecao-negative-times lw-ecao-zero-times
              lw-ecao-minus-one lw-ecao-double-negative lw-ecao-add-cancel lw-ecao-double lw-ecao-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
