(in-package "ACL2")

(include-book "euler-circle-factor-sum-cap")
(include-book "euler-circle-pole-split")
(include-book "circle-interior-root-clearance")
(include-book "circle-exterior-coefficient-bound")

; The actual Euler factor split generates the regular coefficient checks.

(local (defthm lw-ece-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ece-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ece-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ece-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ece-times-negative (a b) (b a)))
                 :in-theory (disable lw-ece-times-negative)))))

(local (defthm lw-ece-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ece-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ece-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ece-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ece-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ece-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ece-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ece-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ece-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ece-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ece-left-commutes)))))

(local (defthm lw-ece-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-ece-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-ece-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-ece-natural-length
 (natp (len roots)) :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-circle-exterior-cap (center radius plus-arcs minus-arcs target error epsilon)
 (let* ((roots (lw-euler-circle-factor-roots center radius target error epsilon))
        (inside (lw-circle-pole-roots roots radius)))
   (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)
      (* (len inside) (/ (lw-circle-interior-root-clearance inside radius))))))

(local (defthm lw-ece-factor-roots-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon)))
 :hints (("Goal"
  :use ((:instance lw-euler-circle-factor-margin (point (cons 1 0))))
  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-norm-square) lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-euler-circle-exterior-cap-data
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (and (rationalp (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)) (< 0 (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon))))
 :hints (("Goal"
  :use (lw-ece-factor-roots-data lw-euler-circle-outer-data lw-euler-circle-factor-sum-cap-data
        (:instance lw-circle-interior-root-clearance-data (roots (lw-euler-circle-factor-roots center radius target error epsilon)))
        (:instance lw-reciprocal-positive (value (lw-circle-interior-root-clearance (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius)))
        (:instance lw-ece-multiply-order (a 0) (b (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius))) (factor (/ (lw-circle-interior-root-clearance (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-exterior-cap lw-ece-inverse-rational lw-ece-product-rational lw-ece-sum-rational lw-ece-natural-length lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-circle-exterior-sum-bound
 (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (lw-complex-diskp (lw-polynomial-factor-log-sum (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (lw-complex-scale radius point)) (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
 :hints (("Goal"
  :use (lw-ece-factor-roots-data lw-euler-circle-outer-data lw-euler-circle-global-shift-data lw-euler-circle-factor-sum-bound
        (:instance lw-circle-pole-split-valid (roots (lw-euler-circle-factor-roots center radius target error epsilon)))
        (:instance lw-circle-interior-root-clearance-data (roots (lw-euler-circle-factor-roots center radius target error epsilon)))
        (:instance lw-circle-interior-root-clearances-generated (roots (lw-euler-circle-factor-roots center radius target error epsilon)))
        (:instance lw-polynomial-factor-log-sum-clearance-bound (roots (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (point (lw-complex-scale radius point)) (clearance (lw-circle-interior-root-clearance (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius)))
        (:instance lw-circle-factor-log-sum-split (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (point (lw-complex-scale radius point)))
        (:instance lw-polynomial-factor-log-sum-rational (roots (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (point (lw-complex-scale radius point)))
        (:instance lw-polynomial-factor-log-sum-rational (roots (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (point (lw-complex-scale radius point)))
        (:instance lw-complex-sub-add-cancel (a (lw-polynomial-factor-log-sum (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (lw-complex-scale radius point))) (b (lw-polynomial-factor-log-sum (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (lw-complex-scale radius point))))
        (:instance lw-complex-sub-disk (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (right (lw-polynomial-factor-log-sum (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) (lw-complex-scale radius point))) (radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)) (other-radius (* (len (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (/ (lw-circle-interior-root-clearance (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-circle-exterior-cap lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-ece-exterior-sample-generation
 (implies (and (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (natp count) (lw-complexp rotation) (equal (lw-complex-norm-square rotation) 1))
  (lw-circle-exterior-sample-check (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius rotation count (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
 :hints (("Goal" :induct (lw-circle-exterior-sample-check (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius rotation count (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-sample-check lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-power-rational (point rotation) (index (- count 1)))
          (:instance lw-complex-norm-square-power (point rotation) (index (- count 1)))
          (:instance lw-euler-circle-exterior-sum-bound (point (lw-complex-power rotation (- count 1)))))
    :in-theory (union-theories
 '(fold-consts-in-+ lw-rational-power-one lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))))

(defthm lw-euler-circle-exterior-coefficient-generated-check
 (implies (and (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (natp index) (rationalp coefficient-error) (< 0 coefficient-error)) (lw-circle-exterior-coefficient-check (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index coefficient-error (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-euler-circle-exterior-roots-data lw-euler-circle-exterior-cap-data
        (:instance lw-circle-exterior-coefficient-sample-count-data
         (roots (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (target index) (error coefficient-error) (bound (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
        (:instance lw-cauchy-orbit-data (degree (len (lw-circle-exterior-polynomial (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index coefficient-error))))
        (:instance lw-cauchy-orbit-norm-one (degree (len (lw-circle-exterior-polynomial (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index coefficient-error))))
        (:instance lw-ece-exterior-sample-generation (rotation (lw-cauchy-orbit-rotation (len (lw-circle-exterior-polynomial (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index coefficient-error)))) (count (lw-circle-exterior-coefficient-sample-count (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index coefficient-error (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-coefficient-check lw-ece-natural-length lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-circle-exterior-coefficient-bound
 (implies (and (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (natp index) (rationalp coefficient-error) (< 0 coefficient-error))
  (lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index) (+ (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon) coefficient-error)))
 :hints (("Goal"
  :use (lw-euler-circle-outer-data lw-euler-circle-exterior-roots-data lw-euler-circle-exterior-cap-data
        lw-euler-circle-exterior-coefficient-generated-check
        (:instance lw-circle-exterior-coefficient-check-sound
         (roots (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (target index) (error coefficient-error) (bound (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-circle-exterior-coefficient-cap
 (implies (and (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
               (natp target) (rationalp error) (< 0 error) (<= error 1)
               (<= (* (lw-euler-circle-outer-gap center radius) error) (lw-euler-circle-anchor-min plus-arcs minus-arcs))
               (rationalp epsilon) (< 0 epsilon) (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs)))) (natp index))
  (lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index) (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
 :hints (("Goal" :cases ((lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index) (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
  :use (lw-euler-circle-outer-data lw-euler-circle-exterior-roots-data lw-euler-circle-exterior-cap-data
        (:instance lw-circle-exterior-polynomial-valid (roots (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (target index) (error 1))
        (:instance lw-circle-exterior-polynomial-coefficient (roots (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius)) (target index) (error 1))
        (:instance lw-complex-coefficient-at-rational (coefficients (lw-circle-exterior-polynomial (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index 1)) (target index) (offset 0))
        (:instance lw-complex-disk-gap-excludes (point (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index)) (radius (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))
        (:instance lw-euler-circle-exterior-coefficient-bound (coefficient-error (lw-disk-gap-error (lw-complex-norm-square (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index)) (lw-euler-circle-exterior-cap center radius plus-arcs minus-arcs target error epsilon)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ece-left-commutes lw-ece-left-distributes lw-ece-fold-constants lw-ece-times-negative lw-ece-negative-times lw-ece-zero-times lw-ece-minus-one lw-ece-double-negative lw-ece-add-cancel lw-ece-double lw-ece-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
