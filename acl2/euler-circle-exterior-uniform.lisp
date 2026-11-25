(in-package "ACL2")

(include-book "circle-exterior-projection")
(include-book "euler-circle-factor-sum-cap")
(include-book "euler-circle-pole-split")
(include-book "polynomial-cauchy-caps")

; The full quotient cap controls the exterior coefficients at every order
; and factor request, even when the interior list approaches the contour.

(local (defthm lw-ecxu-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecxu-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecxu-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecxu-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecxu-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecxu-times-negative)))))

(local (defthm lw-ecxu-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecxu-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecxu-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecxu-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecxu-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecxu-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecxu-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-ecxu-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ecxu-factor-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))))
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
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-factor-roots lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ecxu-projection-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index) (rationalp extraction-error) (< 0 extraction-error))
            (and (lw-complex-coefficientsp (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))))
                 (lw-complexp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index))
                 (equal (lw-complex-coefficient-at (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)) index) 0) (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index))))
   :hints (("Goal"
            :use (lw-ecxu-factor-data (:instance lw-circle-exterior-projection-data
                    (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (target index) (error extraction-error) (degree (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))))
                  (:instance lw-complex-coefficient-at-rational
                    (coefficients (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (target (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)) index)) (offset 0)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxu-length-natural lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ecxu-unit-power
   (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp power))
            (lw-complex-diskp (lw-complex-power point power) 1))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (radius 1))
                  (:instance lw-complex-power-disk (radius 1) (index power)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-one lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ecxu-weighted-bound
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index) (rationalp extraction-error) (< 0 extraction-error)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-mul (lw-complex-power point (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
   :hints (("Goal"
            :use (lw-euler-circle-factor-sum-bound lw-euler-circle-factor-sum-cap-data
                  (:instance lw-ecxu-unit-power (power (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))))
                  (:instance lw-complex-mul-disk (left (lw-complex-power point (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))))) (radius 1)
                    (right (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point))) (other-radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxu-length-natural lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ecxu-projection-point-bound
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index) (rationalp extraction-error) (< 0 extraction-error)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) point 0) (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)))
   :hints (("Goal"
            :use (lw-ecxu-factor-data lw-ecxu-weighted-bound lw-ecxu-projection-data
                  (:instance lw-complex-disk-data (point (lw-complex-mul (lw-complex-power point (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)))) (radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
                  (:instance lw-circle-exterior-projection-error
                    (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (target index) (error extraction-error) (degree (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))))
                  (:instance lw-complex-difference-symmetric
                    (left (lw-complex-mul (lw-complex-power point (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)))) (right (lw-complex-polynomial (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) point 0)) (radius extraction-error))
                  (:instance lw-complex-difference-triangle
                    (left (lw-complex-polynomial (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) point 0)) (middle (lw-complex-mul (lw-complex-power point (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale radius point)))) (right (cons 0 0))
                    (radius extraction-error) (other-radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxu-length-natural lw-complex-polynomial-rational lw-complex-sub-zero lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ecxu-projection-samples
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index) (rationalp extraction-error) (< 0 extraction-error)
                 (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) (lw-cauchy-orbit-rotation degree) 0 count (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) (lw-cauchy-orbit-rotation degree) 0 count (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-cauchy-boundary-check lw-cauchy-orbit-data lw-cauchy-orbit-power-norm-one lw-complex-power-rational lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-ecxu-projection-point-bound
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))))

(defthm lw-euler-circle-exterior-uniform-error-bound
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index) (rationalp extraction-error) (< 0 extraction-error))
           (lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index) (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)))
  :hints (("Goal"
           :use (lw-ecxu-projection-data lw-euler-circle-factor-sum-cap-data
                 (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (cap (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)))
                 (:instance lw-ecxu-projection-samples
                   (degree (len (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))))
                   (count (lw-cauchy-coefficient-count (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))
                             (len (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (lw-polynomial-cap-test-error (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error))) (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)))))
                 (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (cap (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)))
                 (:instance lw-polynomial-capped-coefficient-at (coefficients (lw-circle-exterior-projection (lw-euler-circle-factor-roots center radius target error epsilon) radius index extraction-error (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)))) (cap (+ (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) extraction-error)) (target (+ 1 (len (lw-circle-projection-interior (lw-euler-circle-factor-roots center radius target error epsilon) radius extraction-error)) index)) (offset 0)))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-cauchy-cap-check lw-ecxu-length-natural lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-exterior-uniform-cap
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (natp target) (rationalp error) (< 0 error) (<= error 1)
                (<= (* (lw-euler-circle-outer-gap center radius) error)
                    (lw-euler-circle-anchor-min plus-arcs minus-arcs))
                (rationalp epsilon) (< 0 epsilon)
                (<= epsilon (* 1/4 (lw-euler-circle-anchor-min plus-arcs minus-arcs))) (natp index))
           (lw-complex-diskp (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index) (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
  :hints (("Goal"
           :use (lw-euler-circle-factor-sum-cap-data
                 (:instance lw-ecxu-projection-data (extraction-error 1))
                 (:instance lw-complex-disk-gap-excludes (point (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index)) (radius (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))
                 (:instance lw-euler-circle-exterior-uniform-error-bound
                   (extraction-error (lw-disk-gap-error (lw-complex-norm-square (lw-circle-exterior-coefficient (lw-circle-exterior-roots (lw-euler-circle-factor-roots center radius target error epsilon) radius) radius index)) (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-ecxu-length-natural lw-ecxu-left-commutes lw-ecxu-left-distributes lw-ecxu-fold-constants lw-ecxu-times-negative lw-ecxu-negative-times lw-ecxu-zero-times lw-ecxu-minus-one lw-ecxu-double-negative lw-ecxu-add-cancel lw-ecxu-double lw-ecxu-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
