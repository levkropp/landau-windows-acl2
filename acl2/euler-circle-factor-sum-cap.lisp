(in-package "ACL2")

(include-book "euler-circle-factor-quotient")

; The full reciprocal sum has a cap fixed by the circle cover.

(local (defthm lw-cfs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfs-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfs-times-negative)))))

(local (defthm lw-cfs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cfs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cfs-left-commutes)))))

(local (defthm lw-cfs-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-cfs-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-cfs-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b))) :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-circle-factor-sum-cap (center radius plus-arcs minus-arcs)
 (+ (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
    (* (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)))))

(local (defthm lw-cfs-positive-cost
 (implies (and (rationalp gap) (< 0 gap) (rationalp clearance) (< 0 clearance)
               (rationalp cap) (< 0 cap))
  (and (rationalp (lw-disk-factor-quotient-cost gap clearance cap))
       (< 0 (lw-disk-factor-quotient-cost gap clearance cap))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value gap))
        (:instance lw-reciprocal-positive (value clearance))
        (:instance lw-cfs-positive-product (a (/ clearance)) (b (/ gap)))
        (:instance lw-cfs-positive-product (a (/ clearance)) (b (/ clearance)))
        (:instance lw-cfs-positive-product (a cap) (b (* (/ clearance) (/ clearance)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-disk-factor-quotient-cost lw-cfs-inverse-rational lw-cfs-product-rational lw-cfs-sum-rational lw-cfs-left-commutes lw-cfs-left-distributes lw-cfs-fold-constants lw-cfs-times-negative lw-cfs-negative-times lw-cfs-zero-times lw-cfs-minus-one lw-cfs-double-negative lw-cfs-add-cancel lw-cfs-double lw-cfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-circle-factor-sum-cap-data
 (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
  (and (rationalp (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)) (< 0 (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-euler-circle-global-derivative-cap-data
        (:instance lw-euler-circle-anchor-min-data (point (cons 1 0)))
        (:instance lw-reciprocal-positive (value (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
        (:instance lw-cfs-positive-cost (gap (- (lw-euler-circle-outer-radius center radius) radius)) (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (cap (lw-euler-circle-global-derivative-cap center radius)))
        (:instance lw-cfs-positive-product (a (lw-euler-circle-global-derivative-cap center radius)) (b (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
        (:instance lw-cfs-positive-product (a (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (b (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-factor-sum-cap lw-cfs-inverse-rational lw-cfs-product-rational lw-cfs-sum-rational (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-norm-square) lw-cfs-left-commutes lw-cfs-left-distributes lw-cfs-fold-constants lw-cfs-times-negative lw-cfs-negative-times lw-cfs-zero-times lw-cfs-minus-one lw-cfs-double-negative lw-cfs-add-cancel lw-cfs-double lw-cfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cfs-difference-add-cancel
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-add (lw-complex-sub a b) b) a))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-add lw-complex-sub lw-complexp lw-cfs-left-commutes lw-cfs-left-distributes lw-cfs-fold-constants lw-cfs-times-negative lw-cfs-negative-times lw-cfs-zero-times lw-cfs-minus-one lw-cfs-double-negative lw-cfs-add-cancel lw-cfs-double lw-cfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-circle-factor-sum-bound
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (lw-complex-diskp (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)) (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
 :hints (("Goal"
  :use (lw-euler-circle-factor-pole-sum-quotient-error lw-euler-circle-global-quotient-cap
        lw-euler-circle-global-quotient-rational lw-euler-circle-factor-margin lw-euler-circle-outer-data
        lw-euler-circle-global-shift-data lw-euler-circle-anchor-min-data lw-euler-circle-global-derivative-cap-data
        (:instance lw-cfs-positive-cost (gap (- (lw-euler-circle-outer-radius center radius) radius)) (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (cap (lw-euler-circle-global-derivative-cap center radius)))
        (:instance lw-cfs-multiply-order (a epsilon) (b (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (factor (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius))))
        (:instance lw-polynomial-factor-log-sum-rational (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (point (lw-complex-scale radius point)))
        (:instance lw-cfs-difference-add-cancel (a (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (b (lw-euler-circle-global-quotient center radius point target error)))
        (:instance lw-complex-add-disk (left (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)) (lw-euler-circle-global-quotient center radius point target error))) (right (lw-euler-circle-global-quotient center radius point target error))
         (radius (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)) epsilon)) (other-radius (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs)))))
        (:instance lw-complex-disk-enlarge (point (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (radius (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (* (lw-euler-circle-global-derivative-cap center radius) (/ (lw-euler-circle-anchor-min plus-arcs minus-arcs))))) (cap (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-factor-sum-cap lw-cfs-inverse-rational lw-cfs-product-rational lw-cfs-sum-rational lw-cfs-left-commutes lw-cfs-left-distributes lw-cfs-fold-constants lw-cfs-times-negative lw-cfs-negative-times lw-cfs-zero-times lw-cfs-minus-one lw-cfs-double-negative lw-cfs-add-cancel lw-cfs-double lw-cfs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
