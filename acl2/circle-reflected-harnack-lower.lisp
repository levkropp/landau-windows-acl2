(in-package "ACL2")

(include-book "circle-reflected-harnack-polynomial")
(include-book "cauchy-nonnegative-real-bound")

; An accepted squared boundary cap for the reflected model produces a
; positive lower bound on every strict inner disk.

(local (defthm lw-crhl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crhl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crhl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crhl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crhl-times-negative (a b) (b a)))
                 :in-theory (disable lw-crhl-times-negative)))))

(local (defthm lw-crhl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crhl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crhl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crhl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crhl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crhl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crhl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crhl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crhl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-square-boundary-check
    (roots leading cutoff-square scale boundary-cap point samples)
  (declare (xargs :measure (nfix samples)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp samples) t
    (and (<= (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale (lw-complex-power point (- samples 1)))) boundary-cap)
         (lw-circle-reflected-square-boundary-check roots leading cutoff-square scale boundary-cap point (- samples 1)))))

(defun lw-circle-reflected-harnack-boundary-check
    (roots leading cutoff-square scale center-lower boundary-cap)
  (let* ((coefficients (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap))
         (degree (* 2 (len coefficients))))
    (lw-circle-reflected-square-boundary-check roots leading cutoff-square scale boundary-cap (lw-cauchy-orbit-rotation degree) (lw-cauchy-coefficient-count coefficients degree 1))))

(local
 (defthm lw-crhl-square-data
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (lw-complex-diskp point 1))
            (and (rationalp (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0))) (< 0 (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))
                 (rationalp (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point))) (< 0 (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point)))))
   :hints (("Goal"
            :use ((:instance lw-complex-scale-disk (factor scale) (radius 1))
                  (:instance lw-complex-zero-disk (radius scale))
                  (:instance lw-circle-reflected-square-positive (point (cons 0 0)) (radius scale))
                  (:instance lw-circle-reflected-square-positive (point (lw-complex-scale scale point)) (radius scale)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-crhl-left-commutes lw-crhl-left-distributes lw-crhl-fold-constants
              lw-crhl-times-negative lw-crhl-negative-times lw-crhl-zero-times
              lw-crhl-minus-one lw-crhl-double-negative lw-crhl-add-cancel lw-crhl-double lw-crhl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crhl-boundary-real-positive
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (rationalp center-lower) (< 0 center-lower)
                 (rationalp boundary-cap) (<= 0 boundary-cap)
                 (<= center-lower (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))
                 (lw-complex-diskp point 1) (<= (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point)) boundary-cap))
            (<= 0 (car (lw-complex-polynomial (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) point 0))))
   :hints (("Goal"
            :use (lw-crhl-square-data lw-circle-reflected-harnack-error-data
                  lw-circle-reflected-harnack-log-comparison
                  (:instance lw-circle-reflected-log-boundary-positive
                    (center (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0))) (value (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point))) (real-part (car (lw-complex-polynomial (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) point 0))) (error (lw-circle-reflected-harnack-error roots cutoff-square scale))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-log-ratio
              lw-crhl-left-commutes lw-crhl-left-distributes lw-crhl-fold-constants
              lw-crhl-times-negative lw-crhl-negative-times lw-crhl-zero-times
              lw-crhl-minus-one lw-crhl-double-negative lw-crhl-add-cancel lw-crhl-double lw-crhl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defun lw-crhl-sample-induct (samples)
   (declare (xargs :measure (nfix samples)
                   :hints (("Goal" :in-theory (theory 'ground-zero)))))
   (if (zp samples) 0 (lw-crhl-sample-induct (- samples 1)))))

(local
 (defthm lw-crhl-convert-boundary-check
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (rationalp center-lower) (< 0 center-lower)
                 (rationalp boundary-cap) (<= 0 boundary-cap)
                 (<= center-lower (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))
                 (lw-complex-diskp point 1) (natp samples)
                 (lw-circle-reflected-square-boundary-check roots leading cutoff-square scale boundary-cap point samples))
            (lw-cauchy-nonnegative-real-check (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) point samples))
   :hints (("Goal"
            :induct (lw-crhl-sample-induct samples)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-crhl-sample-induct) lw-circle-reflected-square-boundary-check
              lw-cauchy-nonnegative-real-check
              lw-crhl-left-commutes lw-crhl-left-distributes lw-crhl-fold-constants
              lw-crhl-times-negative lw-crhl-negative-times lw-crhl-zero-times
              lw-crhl-minus-one lw-crhl-double-negative lw-crhl-add-cancel lw-crhl-double lw-crhl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-unit-power (index (- samples 1)))
                        (:instance lw-crhl-boundary-real-positive (point (lw-complex-power point (- samples 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-crhl-length-natural
   (natp (len coefficients))
   :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-crhl-polynomial-check
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (rationalp center-lower) (< 0 center-lower)
                 (rationalp boundary-cap) (<= 0 boundary-cap)
                 (<= center-lower (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))
                 (lw-circle-reflected-harnack-boundary-check roots leading cutoff-square scale center-lower boundary-cap))
            (lw-cauchy-nonnegative-real-polynomial-check (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) 1))
   :hints (("Goal"
            :use ((:instance lw-cauchy-orbit-data (degree (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)))))
                  (:instance lw-cauchy-coefficient-count-natural (coefficients (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)) (degree (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)))) (error 1))
                  (:instance lw-crhl-convert-boundary-check (point (lw-cauchy-orbit-rotation (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)))))
                    (samples (lw-cauchy-coefficient-count (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) (* 2 (len (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap))) 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-harnack-boundary-check lw-cauchy-nonnegative-real-polynomial-check
              lw-crhl-length-natural
              lw-crhl-left-commutes lw-crhl-left-distributes lw-crhl-fold-constants
              lw-crhl-times-negative lw-crhl-negative-times lw-crhl-zero-times
              lw-crhl-minus-one lw-crhl-double-negative lw-crhl-add-cancel lw-crhl-double lw-crhl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-harnack-lower-bound
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (rationalp center-lower) (< 0 center-lower)
                 (rationalp boundary-cap) (<= 0 boundary-cap)
                 (<= center-lower (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))
                (lw-circle-reflected-harnack-boundary-check roots leading cutoff-square scale center-lower boundary-cap)
                (lw-complex-diskp point inner) (< inner 1))
           (and (rationalp (lw-circle-reflected-square-lower center-lower boundary-cap inner)) (< 0 (lw-circle-reflected-square-lower center-lower boundary-cap inner)) (< (lw-circle-reflected-square-lower center-lower boundary-cap inner) (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point)))))
  :hints (("Goal"
           :use (lw-crhl-polynomial-check lw-circle-reflected-harnack-polynomial-data lw-circle-reflected-log-offset-positive
                 (:instance lw-complex-disk-data (radius inner))
                 (:instance lw-complex-disk-enlarge (radius inner) (cap 1))
                 lw-crhl-square-data lw-circle-reflected-harnack-error-data lw-circle-reflected-harnack-log-comparison
                 (:instance lw-cauchy-nonnegative-real-polynomial-bound (coefficients (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)) (error 1) (radius inner))
                 (:instance lw-circle-reflected-square-lower-from-log
                   (center (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0))) (value (lw-circle-reflected-value-square roots leading cutoff-square (lw-complex-scale scale point))) (real-part (car (lw-complex-polynomial (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) point 0))) (error (lw-circle-reflected-harnack-error roots cutoff-square scale))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-log-interior-variation lw-circle-reflected-log-ratio
              lw-crhl-left-commutes lw-crhl-left-distributes lw-crhl-fold-constants
              lw-crhl-times-negative lw-crhl-negative-times lw-crhl-zero-times
              lw-crhl-minus-one lw-crhl-double-negative lw-crhl-add-cancel lw-crhl-double lw-crhl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
