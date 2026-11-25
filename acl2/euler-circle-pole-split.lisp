(in-package "ACL2")

(include-book "euler-circle-factor-quotient")
(include-book "circle-pole-split")
(include-book "polynomial-boundary-factors")

; Every rational factor on the proposed radius would contradict clearance.

(local (defthm lw-ecps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecps-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecps-times-negative)))))

(local (defthm lw-ecps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecps-left-commutes)))))

(local (defthm lw-ecps-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ecps-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ecps-square-scale
 (implies (and (rationalp factor) (lw-complexp root))
  (equal (lw-complex-norm-square (lw-complex-scale factor root))
         (* factor factor (lw-complex-norm-square root))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complexp lw-complex-norm-square lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ecps-inverse-square
 (implies (and (rationalp radius) (< 0 radius))
  (equal (* (/ radius) (/ radius) radius radius) 1))
 :hints (("Goal"
  :use ((:instance lw-ecps-inverse-factor (divisor radius) (coefficient 1)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ecps-inverse-rational lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-ecps-unit-scaling
 (implies (and (lw-complexp root) (rationalp radius) (< 0 radius)
               (equal (lw-complex-norm-square root) (* radius radius)))
  (and (lw-complexp (lw-complex-scale (/ radius) root))
       (equal (lw-complex-norm-square (lw-complex-scale (/ radius) root)) 1)
       (equal (lw-complex-scale radius (lw-complex-scale (/ radius) root)) root)))
 :hints (("Goal"
  :use ((:instance lw-ecps-inverse-factor (divisor radius) (coefficient (car root)))
        (:instance lw-ecps-inverse-factor (divisor radius) (coefficient (cdr root)))
        (:instance lw-ecps-square-scale (factor (/ radius)))
        lw-ecps-inverse-square)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complexp cons-car-cdr lw-ecps-product-rational lw-ecps-inverse-rational lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-ecps-root-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
  (and (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon)) (lw-complexp (lw-polynomial-leading (lw-polynomial-trim (lw-euler-circle-global-polynomial center radius target error))))))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
        (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-factor-roots lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-euler-circle-boundary-root-excluded
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (not (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius)))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-ecps-root-data lw-euler-circle-global-polynomials-valid
        (:instance lw-circle-boundary-root-data (roots (lw-euler-circle-factor-roots center radius target error epsilon)))
        (:instance lw-ecps-unit-scaling (root (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius)))
        (:instance lw-euler-circle-factor-margin (point (lw-complex-scale (/ radius) (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius))))
        (:instance lw-polynomial-disk-factor-evaluation (point (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)))
        (:instance lw-polynomial-factor-member-zero (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (root (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-circle-global-polynomial center radius target error))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-factor-roots lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-exterior-roots-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (lw-circle-exterior-rootsp (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-ecps-root-data lw-euler-circle-boundary-root-excluded
        (:instance lw-circle-exterior-roots-data (roots (lw-euler-circle-factor-roots center radius target error epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-native-split-pole-sum-error
 (implies (and (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add (lw-polynomial-factor-log-sum (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (lw-complex-scale radius point))
                                   (lw-polynomial-factor-log-sum (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (lw-complex-scale radius point))) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point value-error))
   (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (+ (* (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs) error) value-error))))
 :hints (("Goal"
  :use (lw-euler-circle-global-shift-data lw-ecps-root-data lw-euler-circle-native-factor-pole-sum-error
        (:instance lw-circle-factor-log-sum-split (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (point (lw-complex-scale radius point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ecps-left-commutes lw-ecps-left-distributes lw-ecps-fold-constants lw-ecps-times-negative lw-ecps-negative-times lw-ecps-zero-times lw-ecps-minus-one lw-ecps-double-negative lw-ecps-add-cancel lw-ecps-double lw-ecps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
