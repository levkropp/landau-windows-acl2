(in-package "ACL2")

(include-book "circle-exterior-projection-difference")
(include-book "euler-circle-count-requests")
(include-book "polynomial-cauchy-caps")

(local
 (defun lw-ecxc-inputp (center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index)
   (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (natp left-target) (rationalp left-error) (< 0 left-error) (<= left-error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) left-error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp left-epsilon) (< 0 left-epsilon) (<= left-epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp right-target) (rationalp right-error) (< 0 right-error) (<= right-error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) right-error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp right-epsilon) (< 0 right-epsilon) (<= right-epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index))))

(local (defthm lw-ecxc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecxc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecxc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecxc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecxc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecxc-times-negative)))))

(local (defthm lw-ecxc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecxc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecxc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecxc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecxc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecxc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecxc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-ecxc-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ecxc-factor-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (natp target) (rationalp error) (< 0 error) (<= error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
            (and (rationalp radius) (< 0 radius)
                 (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon))
                 (not (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius target error epsilon) radius))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
                  lw-euler-circle-boundary-root-excluded
                  (:instance lw-polynomial-disk-factor-data
                    (coefficients (lw-euler-circle-global-polynomial center radius target error))
                    (outer-radius (lw-euler-circle-outer-radius center radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-factor-roots lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-input-data
   (implies (lw-ecxc-inputp center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index)
            (and (rationalp radius) (< 0 radius) (natp index)
                 (lw-ray-pointsp (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon)) (lw-ray-pointsp (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon))
                 (not (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius))
                 (not (lw-circle-boundary-root (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius))))
   :hints (("Goal"
            :use ((:instance lw-ecxc-factor-data (target left-target) (error left-error) (epsilon left-epsilon))
                  (:instance lw-ecxc-factor-data (target right-target) (error right-error) (epsilon right-epsilon)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-inputp lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-approximation-data
   (implies (and (rationalp auxiliary-error) (< 0 auxiliary-error))
            (and (rationalp (* 1/4 auxiliary-error)) (< 0 (* 1/4 auxiliary-error))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ecxc-coefficient-data
   (implies (and (lw-ecxc-inputp center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index) (rationalp auxiliary-error) (< 0 auxiliary-error))
            (and (lw-complex-coefficientsp (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)))
                 (lw-complexp (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) radius index)))
                 (natp (+ 1 (lw-circle-exterior-projection-common-degree (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius (* 1/4 auxiliary-error)) index))
                 (equal (lw-complex-coefficient-at (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)) (+ 1 (lw-circle-exterior-projection-common-degree (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius (* 1/4 auxiliary-error)) index) 0) (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) radius index)))))
   :hints (("Goal"
            :use (lw-ecxc-input-data
                  (:instance lw-circle-exterior-projection-difference-data
                    (left (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon)) (right (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon)) (target index) (error (* 1/4 auxiliary-error)))
                  (:instance lw-complex-coefficient-at-rational
                    (coefficients (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error))) (target (+ 1 (lw-circle-exterior-projection-common-degree (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius (* 1/4 auxiliary-error)) index)) (offset 0)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-approximation-data lw-circle-exterior-projection-common-degree lw-ecxc-length-natural max lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-shared-difference
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp value))
            (equal (lw-complex-sub (lw-complex-sub a value) (lw-complex-sub b value))
                   (lw-complex-sub a b)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-sub consp lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ecxc-factor-sum-comparison
   (implies (and (lw-ecxc-inputp center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index) (rationalp auxiliary-error) (< 0 auxiliary-error) (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-complex-scale radius point)) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) (lw-complex-scale radius point)))
                              (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon (* 1/4 auxiliary-error)) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon (* 1/4 auxiliary-error)))))
   :hints (("Goal"
            :use (lw-ecxc-input-data lw-euler-circle-global-shift-data
                  (:instance lw-euler-circle-log-value-rational (value-error (* 1/4 auxiliary-error)))
                  (:instance lw-euler-circle-native-factor-pole-sum-error
                   (target left-target) (error left-error) (epsilon left-epsilon) (value-error (* 1/4 auxiliary-error)))
                  (:instance lw-euler-circle-native-factor-pole-sum-error
                   (target right-target) (error right-error) (epsilon right-epsilon) (value-error (* 1/4 auxiliary-error)))
                  (:instance lw-complex-sub-disk
                   (left (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-complex-scale radius point)) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point (* 1/4 auxiliary-error))))
                   (right (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) (lw-complex-scale radius point)) (lw-euler-circle-log-value center radius plus-arcs minus-arcs point (* 1/4 auxiliary-error))))
                   (radius (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon (* 1/4 auxiliary-error))) (other-radius (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon (* 1/4 auxiliary-error)))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-inputp lw-ecxc-approximation-data lw-euler-circle-count-quotient-error lw-ecxc-shared-difference lw-polynomial-factor-log-sum-rational lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-factor-cost-data
   (implies (and (rationalp gap) (< 0 gap) (rationalp clearance) (< 0 clearance)
                 (rationalp derivative-cap) (< 0 derivative-cap))
            (and (rationalp (lw-disk-factor-quotient-cost gap clearance derivative-cap)) (<= 0 (lw-disk-factor-quotient-cost gap clearance derivative-cap))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-disk-factor-quotient-cost lw-reciprocal-positive lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-cap-data
   (implies (lw-ecxc-inputp center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index)
            (and (rationalp (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0))) (<= 0 (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-global-quotient-cost-data
                  (:instance lw-ecxc-factor-cost-data
                    (gap (- (lw-euler-circle-outer-radius center radius) radius))
                    (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                    (derivative-cap (lw-euler-circle-global-derivative-cap center radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-inputp lw-euler-circle-count-quotient-error lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-radius-budget
   (implies (and (rationalp left) (rationalp right) (rationalp auxiliary-error))
            (equal (+ (+ (+ left (* 1/4 auxiliary-error)) (+ right (* 1/4 auxiliary-error)))
                      (* 2 (* 1/4 auxiliary-error)))
                   (+ (+ left right) auxiliary-error)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ecxc-combined-bound
   (implies (and (lw-ecxc-inputp center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index) (rationalp auxiliary-error) (< 0 auxiliary-error) (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)) point 0) (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)))
   :hints (("Goal"
            :use (lw-ecxc-input-data lw-ecxc-cap-data lw-ecxc-factor-sum-comparison
                  (:instance lw-circle-exterior-projection-difference-bound
                    (left (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon)) (right (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon)) (target index) (error (* 1/4 auxiliary-error)) (cap (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon (* 1/4 auxiliary-error)) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon (* 1/4 auxiliary-error))))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-approximation-data lw-euler-circle-count-quotient-error lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-comparison-samples
   (implies (and (lw-ecxc-inputp center radius plus-arcs minus-arcs left-target left-error left-epsilon right-target right-error right-epsilon index) (rationalp auxiliary-error) (< 0 auxiliary-error) (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)) (lw-cauchy-orbit-rotation degree) 0 count (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)) (lw-cauchy-orbit-rotation degree) 0 count (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-cauchy-boundary-check lw-cauchy-orbit-data lw-cauchy-orbit-power-norm-one lw-complex-power-rational lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-ecxc-combined-bound (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-circle-exterior-coefficient-comparison-error
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (natp left-target) (rationalp left-error) (< 0 left-error) (<= left-error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) left-error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp left-epsilon) (< 0 left-epsilon) (<= left-epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp right-target) (rationalp right-error) (< 0 right-error) (<= right-error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) right-error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp right-epsilon) (< 0 right-epsilon) (<= right-epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index) (rationalp auxiliary-error) (< 0 auxiliary-error))
           (lw-complex-diskp (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) radius index)) (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)))
  :hints (("Goal"
           :use (lw-ecxc-coefficient-data lw-ecxc-cap-data
                 (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error))) (cap (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)))
                 (:instance lw-ecxc-comparison-samples (degree (len (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)))) (count (lw-cauchy-coefficient-count (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)) (len (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error))) (lw-polynomial-cap-test-error (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error)) (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)))))
                 (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error))) (cap (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)))
                 (:instance lw-polynomial-capped-coefficient-at
                   (coefficients (lw-circle-exterior-projection-difference (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius index (* 1/4 auxiliary-error))) (cap (+ (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0)) auxiliary-error)) (target (+ 1 (lw-circle-exterior-projection-common-degree (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius (* 1/4 auxiliary-error)) index)) (offset 0)))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-inputp lw-polynomial-cauchy-cap-check lw-ecxc-length-natural lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-exterior-coefficient-comparison
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (natp left-target) (rationalp left-error) (< 0 left-error) (<= left-error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) left-error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp left-epsilon) (< 0 left-epsilon) (<= left-epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp right-target) (rationalp right-error) (< 0 right-error) (<= right-error 1)
   (<= (* (lw-euler-circle-outer-gap center radius) right-error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
   (rationalp right-epsilon) (< 0 right-epsilon) (<= right-epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index))
           (lw-complex-diskp (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) radius index)) (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0))))
  :hints (("Goal"
           :use (lw-ecxc-cap-data
                 (:instance lw-ecxc-coefficient-data (auxiliary-error 1))
                 (:instance lw-complex-disk-gap-excludes (point (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) radius index))) (radius (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0))))
                 (:instance lw-euler-circle-exterior-coefficient-comparison-error
                   (auxiliary-error (lw-disk-gap-error (lw-complex-norm-square (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius left-target left-error left-epsilon) radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius right-target right-error right-epsilon) radius) radius index))) (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs left-error left-epsilon 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs right-error right-epsilon 0))))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxc-inputp lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

; Choose the factor accuracy by dividing the desired coefficient error
; by the same fixed quotient cost at every index and refinement.
(defun lw-euler-circle-exterior-model-request (center radius plus-arcs minus-arcs precision)
  (lw-euler-circle-count-request center radius plus-arcs minus-arcs (* precision (/ (+ 1 (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs 1 1 0))))))

(defun lw-euler-circle-exterior-coefficient-value (center radius plus-arcs minus-arcs target index precision)
  (let ((request (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision)))
    (lw-circle-exterior-coefficient
     (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target request request) radius)
     radius index)))

(local
 (defthm lw-ecxc-cost-data
   (implies (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
            (and (rationalp (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius))) (<= 0 (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) radius) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)) (lw-euler-circle-global-derivative-cap center radius)))
                 (rationalp (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs)) (<= 0 (lw-euler-circle-global-quotient-cost center radius plus-arcs minus-arcs))
                 (rationalp (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs 1 1 0)) (<= 0 (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs 1 1 0))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-global-quotient-cost-data
                  (:instance lw-ecxc-factor-cost-data
                    (gap (- (lw-euler-circle-outer-radius center radius) radius))
                    (clearance (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                    (derivative-cap (lw-euler-circle-global-derivative-cap center radius))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-count-quotient-error lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local (defthm lw-ecxc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecxc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecxc-left-commutes)))))
(local
 (defthm lw-ecxc-precision-product
   (implies (and (rationalp cost) (<= 0 cost) (rationalp precision) (< 0 precision)
                 (rationalp request) (<= request (* precision (/ (+ 1 cost)))))
            (and (< 0 (* precision (/ (+ 1 cost))))
                 (<= (* cost request) precision)))
   :hints (("Goal"
            :use ((:instance lw-ecxc-multiply-order (a request) (b (* precision (/ (+ 1 cost)))) (factor cost))
                  (:instance lw-ecxc-multiply-order (a cost) (b (+ 1 cost)) (factor (* (/ (+ 1 cost)) precision)))
                  (:instance lw-ecxc-inverse-factor (divisor (+ 1 cost)) (coefficient precision)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-reciprocal-positive lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ecxc-model-request-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                 (natp target) (rationalp precision) (< 0 precision))
            (and (natp target)
                 (rationalp (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision)) (< 0 (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision)) (<= (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision) 1)
                 (<= (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision)) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                 (<= (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision) (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))
                 (<= (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision) (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision) 0) precision)))
   :hints (("Goal"
            :use (lw-ecxc-cost-data
                  (:instance lw-euler-circle-count-request-adequate (request (* precision (/ (+ 1 (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs 1 1 0))))))
                  (:instance lw-ecxc-precision-product
                    (cost (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs 1 1 0)) (request (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs precision)))
                  (:instance lw-ecxc-precision-product
                    (cost (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs 1 1 0)) (request 0)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-exterior-model-request lw-euler-circle-count-modelp lw-euler-circle-count-quotient-error lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-exterior-coefficient-cauchy
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp left-target) (natp right-target) (natp index)
                (rationalp left-precision) (< 0 left-precision)
                (rationalp right-precision) (< 0 right-precision))
           (lw-complex-diskp
            (lw-complex-sub (lw-euler-circle-exterior-coefficient-value center radius plus-arcs minus-arcs left-target index left-precision) (lw-euler-circle-exterior-coefficient-value center radius plus-arcs minus-arcs right-target index right-precision))
            (+ left-precision right-precision)))
  :hints (("Goal"
           :use ((:instance lw-ecxc-model-request-data (target left-target) (precision left-precision))
                 (:instance lw-ecxc-model-request-data (target right-target) (precision right-precision))
                 (:instance lw-euler-circle-exterior-coefficient-comparison
                   (left-error (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs left-precision)) (left-epsilon (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs left-precision)) (right-error (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs right-precision)) (right-epsilon (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs right-precision)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-euler-circle-exterior-coefficient-value center radius plus-arcs minus-arcs left-target index left-precision) (lw-euler-circle-exterior-coefficient-value center radius plus-arcs minus-arcs right-target index right-precision)))
                   (radius (+ (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs left-precision) (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs left-precision) 0) (lw-euler-circle-count-quotient-error center radius plus-arcs minus-arcs (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs right-precision) (lw-euler-circle-exterior-model-request center radius plus-arcs minus-arcs right-precision) 0)))
                   (cap (+ left-precision right-precision))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-exterior-coefficient-value lw-ecxc-left-commutes lw-ecxc-left-distributes lw-ecxc-fold-constants lw-ecxc-times-negative lw-ecxc-negative-times lw-ecxc-zero-times lw-ecxc-minus-one lw-ecxc-double-negative lw-ecxc-add-cancel lw-ecxc-double lw-ecxc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
