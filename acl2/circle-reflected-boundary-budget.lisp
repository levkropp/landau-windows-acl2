(in-package "ACL2")

(include-book "circle-inner-factor-count-bound")
(include-book "circle-reflected-harnack-lower")
(include-book "cauchy-boundary-geometric-bound")

; Transfer the original unit-boundary cap to the reflected polynomial.
; Its center lower bound can also be inherited from the original.

(local (defthm lw-crbb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crbb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crbb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crbb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crbb-times-negative (a b) (b a)))
                 :in-theory (disable lw-crbb-times-negative)))))

(local (defthm lw-crbb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crbb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crbb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crbb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crbb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crbb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crbb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crbb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crbb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-boundary-value-cap (cap scale)
  (/ (+ 1 cap) (- 1 scale)))

(defun lw-circle-reflected-boundary-square-cap (cap scale)
  (let ((value-cap (lw-circle-reflected-boundary-value-cap cap scale)))
    (* value-cap value-cap)))

(local
 (defthm lw-crbb-length-natural
   (natp (len coefficients))
   :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-crbb-scale-cap-data
   (implies (and (rationalp scale) (< 0 scale) (< (* scale scale) 1)
                 (rationalp cap) (<= 0 cap))
            (and (< scale 1) (rationalp (lw-circle-reflected-boundary-value-cap cap scale)) (< 0 (lw-circle-reflected-boundary-value-cap cap scale))
                 (rationalp (lw-circle-reflected-boundary-square-cap cap scale)) (< 0 (lw-circle-reflected-boundary-square-cap cap scale))))
   :hints (("Goal"
            :use ((:instance lw-crbb-multiply-order (a 1) (b scale) (factor scale))
                  (:instance lw-reciprocal-positive (value (- 1 scale)))
                  (:instance lw-crbb-positive-product (a (+ 1 cap)) (b (/ (- 1 scale))))
                  (:instance lw-crbb-positive-product (a (lw-circle-reflected-boundary-value-cap cap scale)) (b (lw-circle-reflected-boundary-value-cap cap scale))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-boundary-value-cap lw-circle-reflected-boundary-square-cap
              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crbb-reflected-cap
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square)
                 (rationalp cap) (<= 0 cap)
                 (lw-circle-factor-boundary-check roots leading cutoff-square cap) (lw-complex-diskp point scale))
            (lw-complex-diskp (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0) (lw-circle-reflected-boundary-value-cap cap scale)))
   :hints (("Goal"
            :use (lw-crbb-scale-cap-data lw-circle-reflected-factor-polynomial-valid
                  lw-circle-factor-boundary-check-reflected
                  (:instance lw-cauchy-polynomial-boundary-geometric-bound
                    (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (degree (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) (error 1) (radius scale)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-crbb-length-natural lw-circle-reflected-boundary-value-cap
              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defun lw-crbb-sample-induct (samples)
   (declare (xargs :measure (nfix samples)
                   :hints (("Goal" :in-theory (theory 'ground-zero)))))
   (if (zp samples) 0 (lw-crbb-sample-induct (- samples 1)))))

(local
 (defthm lw-crbb-square-boundary-check
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square)
                 (rationalp cap) (<= 0 cap)
                 (lw-circle-factor-boundary-check roots leading cutoff-square cap) (lw-complex-diskp point 1) (natp samples))
            (lw-circle-reflected-square-boundary-check roots leading cutoff-square scale (lw-circle-reflected-boundary-square-cap cap scale) point samples))
   :hints (("Goal"
            :induct (lw-crbb-sample-induct samples)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-crbb-sample-induct) lw-circle-reflected-square-boundary-check
              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-unit-power (index (- samples 1)))
                        (:instance lw-complex-scale-disk (point (lw-complex-power point (- samples 1))) (factor scale) (radius 1))
                        (:instance lw-crbb-reflected-cap (point (lw-complex-scale scale (lw-complex-power point (- samples 1)))))
                        (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (lw-complex-scale scale (lw-complex-power point (- samples 1))) 0)) (radius (lw-circle-reflected-boundary-value-cap cap scale))))
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-boundary-square-cap lw-circle-reflected-value-square abs
              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-circle-reflected-harnack-boundary-generated
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square)
                 (rationalp cap) (<= 0 cap)
                 (lw-circle-factor-boundary-check roots leading cutoff-square cap) (rationalp center-lower) (< 0 center-lower)
                (<= center-lower (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0))))
           (lw-circle-reflected-harnack-boundary-check roots leading cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale)))
  :hints (("Goal"
           :use ((:instance lw-cauchy-orbit-data
                   (degree (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale))))))
                 (:instance lw-cauchy-coefficient-count-natural
                   (coefficients (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale)))
                   (degree (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale))))) (error 1))
                 (:instance lw-crbb-square-boundary-check
                   (point (lw-cauchy-orbit-rotation (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale))))))
                   (samples (lw-cauchy-coefficient-count
                    (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale))
                    (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower (lw-circle-reflected-boundary-square-cap cap scale)))) 1))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-crbb-length-natural lw-circle-reflected-harnack-boundary-check
              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-crbb-center-lower
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                 (rationalp cutoff-square) (<= 0 cutoff-square) (< cutoff-square 1)
                 (rationalp center-lower) (<= center-lower (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0))))
            (<= center-lower (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)) ))
   :hints (("Goal"
            :use (lw-circle-reflected-factor-center-growth lw-circle-reflected-factor-polynomial-valid
                  (:instance lw-complex-polynomial-rational (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (point (cons 0 0)) (offset 0))
                  (:instance lw-complex-norm-square-valid (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0) ))
                  (:instance lw-rational-power-monotone-base
                    (left cutoff-square) (right 1) (exponent (lw-circle-inner-factor-count roots cutoff-square)))
                  (:instance lw-crbb-multiply-order
                    (a (lw-rational-power cutoff-square (lw-circle-inner-factor-count roots cutoff-square))) (b 1)
                    (factor (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)) )))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-value-square lw-rational-power-one lw-rational-power-rational
              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-lower-from-original-boundary
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square)
                 (rationalp cap) (<= 0 cap)
                 (lw-circle-factor-boundary-check roots leading cutoff-square cap) (rationalp center-lower) (< 0 center-lower)
                (<= center-lower (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0)))
                (lw-complex-diskp point inner) (< inner 1))
           (let ((lower (lw-circle-reflected-square-lower center-lower (lw-circle-reflected-boundary-square-cap cap scale) inner)))
             (and (rationalp lower) (< 0 lower) (< lower (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point))))))
  :hints (("Goal"
           :use (lw-crbb-scale-cap-data lw-crbb-center-lower lw-circle-reflected-harnack-boundary-generated
                 (:instance lw-circle-reflected-harnack-lower-bound (boundary-cap (lw-circle-reflected-boundary-square-cap cap scale))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crbb-left-commutes lw-crbb-left-distributes lw-crbb-fold-constants
              lw-crbb-times-negative lw-crbb-negative-times lw-crbb-zero-times
              lw-crbb-minus-one lw-crbb-double-negative lw-crbb-add-cancel lw-crbb-double lw-crbb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
