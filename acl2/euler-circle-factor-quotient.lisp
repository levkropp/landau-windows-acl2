(in-package "ACL2")

(include-book "euler-circle-global-quotient")
(include-book "polynomial-disk-factor-quotient")
(include-book "unit-square-pole-split")

; Use the Euler polynomial already shared by the circle value and derivative.

(local (defthm lw-cfq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfq-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfq-times-negative)))))

(local (defthm lw-cfq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cfq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cfq-left-commutes)))))

(defun lw-euler-circle-factor-roots (center radius target error epsilon)
 (lw-polynomial-normalized-factor-roots
  (lw-euler-circle-global-polynomial center radius target error)
  (lw-euler-circle-outer-radius center radius) epsilon))

(local (defthm lw-cfq-half-margin
 (implies (and (lw-complexp value) (rationalp cap) (< 0 cap)
               (<= (* cap cap) (lw-complex-norm-square value)))
  (not (lw-complex-diskp value (* 1/2 cap))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-norm-square (point value) (radius (* 1/2 cap))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cfq-left-commutes lw-cfq-left-distributes lw-cfq-fold-constants lw-cfq-times-negative lw-cfq-negative-times lw-cfq-zero-times lw-cfq-minus-one lw-cfq-double-negative lw-cfq-add-cancel lw-cfq-double lw-cfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-cfq-input-clearance
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
  (and (lw-complex-diskp (lw-complex-scale radius point) radius) (lw-complexp (lw-complex-scale radius point))
       (rationalp (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (< 0 (lw-euler-circle-anchor-min plus-arcs minus-arcs))
       (not (lw-complex-diskp (lw-euler-circle-global-polynomial-value center radius point target error) (* 1/2 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-euler-circle-global-shift-data
        lw-euler-circle-anchor-min-data lw-euler-circle-global-polynomial-clearance
        (:instance lw-cfq-half-margin (value (lw-euler-circle-global-polynomial-value center radius point target error)) (cap (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cfq-left-commutes lw-cfq-left-distributes lw-cfq-fold-constants lw-cfq-times-negative lw-cfq-negative-times lw-cfq-zero-times lw-cfq-minus-one lw-cfq-double-negative lw-cfq-add-cancel lw-cfq-double lw-cfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-euler-circle-factor-margin
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
  (and (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon))
       (not (equal (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-circle-global-polynomial center radius target error) (lw-euler-circle-outer-radius center radius) epsilon) (lw-complex-scale radius point) 0) (cons 0 0)))
       (<= (* (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-circle-global-polynomial center radius target error) (lw-euler-circle-outer-radius center radius) epsilon) (lw-complex-scale radius point) 0)))))
 :hints (("Goal"
  :use (lw-cfq-input-clearance lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
        (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)))
        (:instance lw-polynomial-disk-factor-margin (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius))
           (inner-radius radius) (center (lw-complex-scale radius point)) (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-factor-roots lw-euler-circle-global-polynomial-value lw-cfq-left-commutes lw-cfq-left-distributes lw-cfq-fold-constants lw-cfq-times-negative lw-cfq-negative-times lw-cfq-zero-times lw-cfq-minus-one lw-cfq-double-negative lw-cfq-add-cancel lw-cfq-double lw-cfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cfq-derivative-identity
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
  (equal (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) (lw-complex-scale radius point)) (lw-euler-circle-global-derivative-value center radius point target error)))
 :hints (("Goal"
  :use (lw-euler-circle-global-polynomials-valid lw-euler-circle-global-shift-data
        lw-euler-circle-global-derivative-identity
        (:instance lw-polynomial-derivative-coefficients-evaluation (coefficients (lw-euler-circle-global-polynomial center radius target error)) (point (lw-complex-scale radius point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-global-derivative-value lw-cfq-left-commutes lw-cfq-left-distributes lw-cfq-fold-constants lw-cfq-times-negative lw-cfq-negative-times lw-cfq-zero-times lw-cfq-minus-one lw-cfq-double-negative lw-cfq-add-cancel lw-cfq-double lw-cfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-euler-circle-factor-pole-sum-quotient-error
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)) (lw-euler-circle-global-quotient center radius point target error)) (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)) epsilon)))
 :hints (("Goal"
  :use (lw-cfq-input-clearance lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
        lw-cfq-derivative-identity lw-euler-circle-global-derivative-cap-data lw-euler-circle-global-derivative-bound
        (:instance lw-polynomial-disk-factor-sum-error (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius))
         (inner-radius radius) (center (lw-complex-scale radius point)) (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (numerator-cap (lw-euler-circle-global-derivative-cap center radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-factor-roots lw-euler-circle-global-polynomial-value lw-euler-circle-global-quotient lw-cfq-left-commutes lw-cfq-left-distributes lw-cfq-fold-constants lw-cfq-times-negative lw-cfq-negative-times lw-cfq-zero-times lw-cfq-minus-one lw-cfq-double-negative lw-cfq-add-cancel lw-cfq-double lw-cfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-circle-native-factor-pole-sum-error
 (implies (and (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error)) (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error))))
 :hints (("Goal"
  :use (lw-cfq-input-clearance lw-euler-circle-factor-margin lw-euler-circle-factor-pole-sum-quotient-error
        lw-euler-circle-global-log-comparison lw-euler-circle-global-quotient-rational lw-euler-circle-log-value-rational
        (:instance lw-polynomial-factor-log-sum-rational (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (point (lw-complex-scale radius point)))
        (:instance lw-complex-difference-triangle (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (middle (lw-euler-circle-global-quotient center radius point target error)) (right (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))
                   (radius (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)) epsilon)) (other-radius (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cfq-left-commutes lw-cfq-left-distributes lw-cfq-fold-constants lw-cfq-times-negative lw-cfq-negative-times lw-cfq-zero-times lw-cfq-minus-one lw-cfq-double-negative lw-cfq-add-cancel lw-cfq-double lw-cfq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
