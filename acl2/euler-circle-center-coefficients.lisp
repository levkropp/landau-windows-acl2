(in-package "ACL2")

(include-book "euler-circle-center-native-quotient")
(include-book "polynomial-cauchy-caps")

; On the inner disk all roots of the outer model are exterior. The contour
; is parameterized by point in the unit disk and physical offset rho*point.
(defun lw-euler-circle-center-coefficient-difference (center radius target error epsilon anchor-error index extraction-error native-error)
  (let ((factor-model (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error))
        (native-model (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0)))
    (lw-polynomial-disk-difference factor-model native-model 1
      (+ (len factor-model) (len native-model)))))

(defun lw-euler-circle-center-coefficient-error (center radius anchor-error error epsilon extraction-error native-error value-error)
  (+ (+ extraction-error (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error))) (+ (* (lw-euler-uniform-log-model-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error) (lw-euler-uniform-log-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error native-error)) (* (lw-euler-uniform-log-node-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error) value-error))))

(local (defthm lw-eccf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eccf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eccf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eccf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eccf-times-negative (a b) (b a)))
                 :in-theory (disable lw-eccf-times-negative)))))

(local (defthm lw-eccf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eccf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eccf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eccf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eccf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eccf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eccf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-eccf-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-eccf-model-data
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error))
            (and (rationalp (lw-euler-circle-center-radius center radius anchor-error)) (< 0 (lw-euler-circle-center-radius center radius anchor-error))
                 (lw-complex-coefficientsp (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error))
                 (lw-complex-coefficientsp (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error))
                 (lw-complex-coefficientsp (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0))
                 (lw-complex-coefficientsp (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error))
                 (equal (lw-complex-coefficient-at (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error) index 0) (lw-circle-exterior-coefficient (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index))))
   :hints (("Goal"
            :use (lw-euler-circle-center-model-data lw-euler-circle-center-roots-exterior
                  lw-euler-circle-outer-data
                  (:instance lw-euler-uniform-log-polynomial-valid
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius))
                    (target index) (error native-error))
                  (:instance lw-circle-exterior-polynomial-valid
                    (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius (lw-euler-circle-center-radius center radius anchor-error))
                    (target index) (error extraction-error))
                  (:instance lw-circle-exterior-polynomial-coefficient
                    (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius (lw-euler-circle-center-radius center radius anchor-error))
                    (target index) (error extraction-error)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-center-coefficient-difference lw-polynomial-rescale-valid lw-polynomial-disk-difference-valid lw-eccf-length-natural lw-eccf-left-commutes lw-eccf-left-distributes lw-eccf-fold-constants lw-eccf-times-negative lw-eccf-negative-times lw-eccf-zero-times lw-eccf-minus-one lw-eccf-double-negative lw-eccf-add-cancel lw-eccf-double lw-eccf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccf-scaled-disk-data
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point 1))
            (and (lw-complexp point)
                 (lw-complex-diskp (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point) (lw-euler-circle-center-radius center radius anchor-error))
                 (lw-complex-diskp (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point) (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error))
                 (rationalp (car (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)))
                 (rationalp (cdr (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)))
                 (rationalp (+ (car center) (car (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point))))
                 (< 0 (+ (car center) (car (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point))))))
   :hints (("Goal"
            :use (lw-euler-circle-center-model-data lw-euler-circle-outer-data
                  (:instance lw-euler-neighborhood-data (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                  (:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-scale-disk (factor (lw-euler-circle-center-radius center radius anchor-error)) (radius 1))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)) (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)))
                  (:instance lw-euler-disk-point-data (rate (car center)) (height (cdr center))
                    (offset (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)) (radius (lw-euler-circle-center-radius center radius anchor-error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp abs lw-eccf-left-commutes lw-eccf-left-distributes lw-eccf-fold-constants lw-eccf-times-negative lw-eccf-negative-times lw-eccf-zero-times lw-eccf-minus-one lw-eccf-double-negative lw-eccf-add-cancel lw-eccf-double lw-eccf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccf-point-comparison
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error)
                (lw-complex-diskp point 1))
            (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error) point 0) (lw-complex-polynomial (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point) 0)) (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
   :hints (("Goal"
            :use (lw-eccf-model-data lw-eccf-scaled-disk-data lw-euler-circle-center-model-data lw-euler-circle-outer-data
                  lw-euler-circle-center-roots-exterior
                  (:instance lw-circle-exterior-roots-typed (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius (lw-euler-circle-center-radius center radius anchor-error)))
                  (:instance lw-circle-exterior-polynomial-error (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius (lw-euler-circle-center-radius center radius anchor-error))
                    (target index) (error extraction-error))
                  (:instance lw-euler-circle-center-native-factor-error (point (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)))
                  (:instance lw-euler-circle-center-native-quotient-comparison (point (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)))
                  (:instance lw-complex-euler-uniform-log-node-comparison
                    (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius))
                    (point (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point)) (target index) (error native-error) (request value-error)
                    (coefficient-radius (* 1/2 (+ (car center) (car (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point))))))
                  (:instance lw-complex-difference-symmetric (left (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point))) (right (lw-complex-polynomial (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error) point 0)) (radius extraction-error))
                  (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error) point 0)) (middle (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point))) (right (lw-euler-circle-center-native-quotient center (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point) value-error))
                   (radius extraction-error) (other-radius (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error))))
                  (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error) point 0)) (middle (lw-euler-circle-center-native-quotient center (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point) value-error)) (right (lw-complex-polynomial (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-complex-scale (lw-euler-circle-center-radius center radius anchor-error) point) 0))
                   (radius (+ extraction-error (+ (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) epsilon) (lw-euler-circle-center-native-quotient-error center radius anchor-error error value-error)))) (other-radius (+ (* (lw-euler-uniform-log-model-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error) (lw-euler-uniform-log-request (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error native-error)) (* (lw-euler-uniform-log-node-cost (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error) value-error)))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-center-coefficient-error lw-euler-circle-center-native-quotient lw-complex-scale-rational lw-polynomial-factor-log-sum-rational lw-complex-polynomial-rational lw-eccf-left-commutes lw-eccf-left-distributes lw-eccf-fold-constants lw-eccf-times-negative lw-eccf-negative-times lw-eccf-zero-times lw-eccf-minus-one lw-eccf-double-negative lw-eccf-add-cancel lw-eccf-double lw-eccf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccf-difference-bound
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error)
                (lw-complex-diskp point 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error) point 0) (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
   :hints (("Goal"
            :use (lw-eccf-model-data lw-eccf-scaled-disk-data lw-eccf-point-comparison
                  (:instance lw-polynomial-disk-difference-evaluation
                    (left (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error)) (right (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0)) (radius 1)
                    (count (+ (len (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error)) (len (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0)))))
                  (:instance lw-polynomial-rescale-evaluation
                    (coefficients (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error)) (factor (lw-euler-circle-center-radius center radius anchor-error)) (offset 0)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-coefficient-difference lw-eccf-length-natural lw-complex-scale-one lw-eccf-left-commutes lw-eccf-left-distributes lw-eccf-fold-constants lw-eccf-times-negative lw-eccf-negative-times lw-eccf-zero-times lw-eccf-minus-one lw-eccf-double-negative lw-eccf-add-cancel lw-eccf-double lw-eccf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-eccf-samples-pass
   (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error) (natp degree) (natp count))
            (lw-cauchy-boundary-check (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error) (lw-cauchy-orbit-rotation degree) 0 count (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
   :hints (("Goal" :induct (lw-cauchy-boundary-check (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error) (lw-cauchy-orbit-rotation degree) 0 count (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-cauchy-boundary-check lw-cauchy-orbit-data lw-complex-unit-power lw-eccf-left-commutes lw-eccf-left-distributes lw-eccf-fold-constants lw-eccf-times-negative lw-eccf-negative-times lw-eccf-zero-times lw-eccf-minus-one lw-eccf-double-negative lw-eccf-add-cancel lw-eccf-double lw-eccf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-eccf-difference-bound
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- count 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-circle-center-coefficient-comparison
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
                (natp index) (rationalp extraction-error) (< 0 extraction-error)
                (rationalp native-error) (< 0 native-error)
                (rationalp value-error) (< 0 value-error) (<= value-error anchor-error))
           (lw-complex-diskp (lw-complex-sub (lw-circle-exterior-coefficient (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index) (lw-complex-coefficient-at (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0) index 0)) (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
  :hints (("Goal"
           :use (lw-eccf-model-data
                 (:instance lw-complex-coefficient-at-rational (coefficients (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error)) (target index) (offset 0))
                 (:instance lw-complex-coefficient-at-rational (coefficients (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error)) (target index) (offset 0))
                 (:instance lw-eccf-difference-bound (point (cons 1 0)))
                 (:instance lw-complex-disk-data
                   (point (lw-complex-polynomial (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error) (cons 1 0) 0)) (radius (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
                 (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error)) (cap (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
                 (:instance lw-eccf-samples-pass (degree (len (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error))) (count (lw-cauchy-coefficient-count (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error) (len (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error)) (lw-polynomial-cap-test-error (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error) (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))))
                 (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-euler-circle-center-coefficient-difference center radius target error epsilon anchor-error index extraction-error native-error)) (cap (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error)))
                 (:instance lw-polynomial-disk-difference-capped-coefficient
                   (left (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error)) (right (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0)) (radius 1) (count (+ (len (lw-circle-exterior-polynomial (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error) index extraction-error)) (len (lw-polynomial-rescale (lw-euler-uniform-log-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error index native-error) (lw-euler-circle-center-radius center radius anchor-error) 0)))) (cap (lw-euler-circle-center-coefficient-error center radius anchor-error error epsilon extraction-error native-error value-error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-complex-diskp) lw-euler-circle-center-coefficient-difference lw-polynomial-cauchy-cap-check lw-eccf-length-natural lw-polynomial-rescale-coefficient lw-rational-power-rational lw-complex-scale-rational lw-rational-power-one lw-complex-scale-one lw-eccf-left-commutes lw-eccf-left-distributes lw-eccf-fold-constants lw-eccf-times-negative lw-eccf-negative-times lw-eccf-zero-times lw-eccf-minus-one lw-eccf-double-negative lw-eccf-add-cancel lw-eccf-double lw-eccf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
