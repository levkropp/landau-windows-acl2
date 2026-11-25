(in-package "ACL2")

(include-book "polynomial-factor-accuracy")
(include-book "polynomial-factor-coefficients")
(include-book "polynomial-local-derivative-comparison")

; Use circles of radius 1/2 within the certified radius-two approximation disk.

(local (defthm lw-pad-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pad-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pad-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pad-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pad-times-negative (a b) (b a)))
                 :in-theory (disable lw-pad-times-negative)))))

(local (defthm lw-pad-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pad-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pad-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pad-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pad-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pad-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pad-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pad-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pad-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pad-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pad-left-commutes)))))

(defun lw-polynomial-square-factor-polynomial (coefficients count tolerance)
 (lw-polynomial-factor-coefficients
  (lw-polynomial-square-accurate-roots coefficients count tolerance)
  (lw-polynomial-leading (lw-polynomial-trim coefficients))))

(defthm lw-polynomial-square-factor-polynomial-valid
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complex-coefficientsp (lw-polynomial-square-factor-polynomial coefficients count tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-data
        (:instance lw-polynomial-factor-coefficients-valid (roots (lw-polynomial-square-accurate-roots coefficients count tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-factor-polynomial lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-factor-polynomial-value-error
 (implies (and (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complex-diskp point 2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0) (lw-complex-polynomial (lw-polynomial-square-factor-polynomial coefficients count tolerance) point 0))
   (lw-polynomial-square-factor-request coefficients count tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-data lw-polynomial-square-accurate-disk-approximation
        (:instance lw-complex-disk-data (radius 2))
        (:instance lw-polynomial-factor-coefficients-evaluation (roots (lw-polynomial-square-accurate-roots coefficients count tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-factor-polynomial lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-pad-centered-sample
 (implies (and (lw-complex-diskp center 3/2) (lw-complex-diskp point 1))
  (lw-complex-diskp (lw-complex-add center (lw-complex-scale 1/2 point)) 2))
 :hints (("Goal"
  :use ((:instance lw-complex-scale-disk (factor 1/2) (radius 1))
        (:instance lw-complex-add-disk (left center) (right (lw-complex-scale 1/2 point))
                    (radius 3/2) (other-radius 1/2)))
  :in-theory (union-theories
 '(fold-consts-in-+ abs lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defun lw-pad-countdown (samples)
 (declare (xargs :measure (nfix samples) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp samples) 0 (lw-pad-countdown (- samples 1)))))

(local (defthm lw-pad-generated-boundary-check
 (implies (and (and (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complex-diskp center 3/2)) (lw-complex-diskp point 1) (natp samples)) (lw-cauchy-boundary-check (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2) point 0 samples (lw-polynomial-square-factor-request coefficients count tolerance)))
 :hints (("Goal" :induct (lw-pad-countdown samples)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-pad-countdown) lw-cauchy-boundary-check lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use (lw-polynomial-square-factor-polynomial-valid
          (:instance lw-complex-disk-data (point center) (radius 3/2))
          (:instance lw-complex-power-disk (radius 1) (index (- samples 1)))
          (:instance lw-complex-disk-data (point (lw-complex-power point (- samples 1))) (radius 1))
          (:instance lw-pad-centered-sample (point (lw-complex-power point (- samples 1))))
          (:instance lw-polynomial-local-difference-evaluation
           (left coefficients) (right (lw-polynomial-square-factor-polynomial coefficients count tolerance)) (radius 1/2) (point (lw-complex-power point (- samples 1))))
          (:instance lw-polynomial-square-factor-polynomial-value-error (point (lw-complex-add center (lw-complex-scale 1/2 (lw-complex-power point (- samples 1)))))))
    :in-theory (union-theories
 '(fold-consts-in-+ lw-rational-power-one lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
    :do-not-induct t)))))

(local (defthm lw-pad-unscale-half
 (implies (and (lw-complexp point) (lw-complex-diskp (lw-complex-scale 1/2 point) cap))
  (lw-complex-diskp point (* 2 cap)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-diskp lw-complex-scale lw-complexp lw-diskp lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))))

(defthm lw-polynomial-square-factor-derivative-error
 (implies (and (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complex-diskp center 3/2))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial-derivative coefficients center) (lw-complex-polynomial-derivative (lw-polynomial-square-factor-polynomial coefficients count tolerance) center)) (* 2 (lw-polynomial-square-factor-request coefficients count tolerance))))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-polynomial-valid lw-polynomial-square-factor-request-data
        (:instance lw-complex-disk-data (point center) (radius 3/2))
        (:instance lw-polynomial-local-difference-valid (left coefficients) (right (lw-polynomial-square-factor-polynomial coefficients count tolerance)) (radius 1/2))
        (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2)) (cap (lw-polynomial-square-factor-request coefficients count tolerance)))
        (:instance lw-cauchy-orbit-data (degree (len (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2))))
        (:instance lw-pad-generated-boundary-check
         (point (lw-cauchy-orbit-rotation (len (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2))))
         (samples (lw-cauchy-coefficient-count (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2) (len (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2)) (lw-polynomial-cap-test-error (lw-polynomial-local-difference coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance) center 1/2) (lw-polynomial-square-factor-request coefficients count tolerance)))))
        (:instance lw-polynomial-local-difference-derivative (left coefficients) (right (lw-polynomial-square-factor-polynomial coefficients count tolerance)) (radius 1/2) (cap (lw-polynomial-square-factor-request coefficients count tolerance)))
        (:instance lw-complex-polynomial-derivative-rational (point center))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-polynomial-square-factor-polynomial coefficients count tolerance)) (point center))
        (:instance lw-complex-operations-rational
         (left (lw-complex-polynomial-derivative coefficients center))
         (right (lw-complex-polynomial-derivative (lw-polynomial-square-factor-polynomial coefficients count tolerance) center)) (factor 1))
        (:instance lw-pad-unscale-half (point (lw-complex-sub (lw-complex-polynomial-derivative coefficients center) (lw-complex-polynomial-derivative (lw-polynomial-square-factor-polynomial coefficients count tolerance) center))) (cap (lw-polynomial-square-factor-request coefficients count tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-cauchy-cap-check lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-unit-square-point-in-derivative-disk
 (implies (lw-unit-square-pointp point) (lw-complex-diskp point 3/2))
 :hints (("Goal" :use (lw-unit-square-point-coordinates) :nonlinearp t
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-diskp lw-diskp lw-pad-left-commutes lw-pad-left-distributes lw-pad-fold-constants lw-pad-times-negative lw-pad-negative-times lw-pad-zero-times lw-pad-minus-one lw-pad-double-negative lw-pad-add-cancel lw-pad-double lw-pad-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
