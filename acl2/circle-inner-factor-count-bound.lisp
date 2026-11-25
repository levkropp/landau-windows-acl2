(in-package "ACL2")

(include-book "circle-factor-reflection")
(include-book "polynomial-quadratic-bounds")
(include-book "pole-dominance")

; Finite Jensen bound. The orbit size can depend on the polynomial degree.
; The numerical bound on the number of inner factors does not.

(local (defthm lw-cic-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cic-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cic-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cic-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cic-times-negative (a b) (b a)))
                 :in-theory (disable lw-cic-times-negative)))))

(local (defthm lw-cic-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cic-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cic-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cic-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cic-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cic-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cic-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cic-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cic-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cic-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cic-left-commutes)))))

(defun lw-circle-inner-factor-count-limit (cutoff-square center-square cap)
  (lw-resolvent-truncation-count cutoff-square
    (/ center-square (* 2 (+ 1 cap) (+ 1 cap)))))

(defun lw-circle-factor-boundary-check (roots leading cutoff-square cap)
  (let* ((reflected (lw-circle-reflected-factor-polynomial roots leading cutoff-square))
         (degree (len reflected)))
    (lw-cauchy-boundary-check (lw-polynomial-factor-coefficients roots leading)
      (lw-cauchy-orbit-rotation degree) 0
      (lw-cauchy-coefficient-count reflected degree 1) cap)))

(local
 (defthm lw-cic-reflected-length
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading))
            (posp (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))))
   :hints (("Goal"
            :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-factor-polynomial)
              lw-circle-reflected-factor-polynomial lw-circle-reflected-factor-polynomial-valid
              lw-circle-reflected-factor-slope lw-complex-conjugate-rational lw-complex-scale-rational
              lw-polynomial-multiply-linear-valid lw-ray-pointsp len endp
              lw-cic-left-commutes lw-cic-left-distributes lw-cic-fold-constants
              lw-cic-times-negative lw-cic-negative-times lw-cic-zero-times
              lw-cic-minus-one lw-cic-double-negative lw-cic-add-cancel lw-cic-double lw-cic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize)))))

(local
 (defun lw-cic-countdown (samples)
   (declare (xargs :measure (nfix samples) :hints (("Goal" :in-theory (theory 'ground-zero)))))
   (if (zp samples) 0 (lw-cic-countdown (- samples 1)))))

(local
 (defthm lw-cic-transfer-boundary
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                 (rationalp cap) (<= 0 cap) (natp degree) (natp samples)
                 (lw-cauchy-boundary-check (lw-polynomial-factor-coefficients roots leading) (lw-cauchy-orbit-rotation degree) 0 samples cap))
            (lw-cauchy-boundary-check (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (lw-cauchy-orbit-rotation degree) 0 samples cap))
   :hints (("Goal"
            :induct (lw-cic-countdown samples)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-cic-countdown) lw-cauchy-boundary-check
              lw-cic-left-commutes lw-cic-left-distributes lw-cic-fold-constants
              lw-cic-times-negative lw-cic-negative-times lw-cic-zero-times
              lw-cic-minus-one lw-cic-double-negative lw-cic-add-cancel lw-cic-double lw-cic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-cauchy-orbit-data
                        (:instance lw-cauchy-orbit-power-norm-one (index (- samples 1)))
                        (:instance lw-complex-power-rational (point (lw-cauchy-orbit-rotation degree)) (index (- samples 1)))
                        (:instance lw-circle-reflected-factor-boundary-norm
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- samples 1))))
                        lw-circle-reflected-factor-polynomial-valid lw-polynomial-factor-coefficients-valid
                        (:instance lw-complex-polynomial-rational (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square))
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- samples 1))) (offset 0))
                        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-factor-coefficients roots leading))
                          (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- samples 1))) (offset 0))
                        (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
                          (lw-complex-power (lw-cauchy-orbit-rotation degree) (- samples 1)) 0)) (radius cap))
                        (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading)
                          (lw-complex-power (lw-cauchy-orbit-rotation degree) (- samples 1)) 0)) (radius cap)))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-cic-center-cap
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                 (rationalp cap) (<= 0 cap)
                 (lw-circle-factor-boundary-check roots leading cutoff-square cap))
            (lw-complex-diskp (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0) (+ 1 cap)))
   :hints (("Goal"
            :use (lw-cic-reflected-length lw-circle-reflected-factor-polynomial-valid
                  (:instance lw-cauchy-coefficient-count-natural (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (degree (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) (error 1))
                  (:instance lw-cic-transfer-boundary (degree (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) (samples (lw-cauchy-coefficient-count (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) 1)))
                  (:instance lw-cauchy-finite-coefficient-bound (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (degree (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) (target 0) (error 1))
                  (:instance lw-complex-polynomial-at-zero (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)))
                  (:instance lw-complex-coefficient-at-nth (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (target 0) (offset 0)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-factor-boundary-check
              lw-cic-left-commutes lw-cic-left-distributes lw-cic-fold-constants
              lw-cic-times-negative lw-cic-negative-times lw-cic-zero-times
              lw-cic-minus-one lw-cic-double-negative lw-cic-add-cancel lw-cic-double lw-cic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cic-strict-limit
   (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1)
                 (rationalp center-square) (< 0 center-square)
                 (rationalp cap) (<= 0 cap)
                 (rationalp reflected-square) (<= 0 reflected-square)
                 (<= reflected-square (* (+ 1 cap) (+ 1 cap)))
                 (natp index)
                 (<= center-square (* (lw-rational-power ratio index) reflected-square)))
            (< index (lw-circle-inner-factor-count-limit ratio center-square cap)))
   :hints (("Goal"
            :use ((:instance lw-rational-power-computed-decay
                    (error (/ center-square (* 2 (+ 1 cap) (+ 1 cap)))))
                  (:instance lw-rational-power-nonnegative (base ratio) (exponent index))
                  (:instance lw-rational-power-rational (base ratio) (exponent index))
                  (:instance lw-cic-positive-product (a (+ 1 cap)) (b (+ 1 cap)))
                  (:instance lw-cic-positive-product (a (* (+ 1 cap) (+ 1 cap))) (b 2))
                  (:instance lw-reciprocal-positive (value (* 2 (+ 1 cap) (+ 1 cap))))
                  (:instance lw-cic-inverse-factor (divisor (* 2 (+ 1 cap) (+ 1 cap))) (coefficient center-square))
                  (:instance lw-cic-multiply-order
                    (a reflected-square) (b (* (+ 1 cap) (+ 1 cap))) (factor (lw-rational-power ratio index)))
                  (:instance lw-cic-multiply-order
                    (a (lw-rational-power ratio index)) (b (/ center-square (* 2 (+ 1 cap) (+ 1 cap))))
                    (factor (* 2 (+ 1 cap) (+ 1 cap)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-inner-factor-count-limit
              lw-cic-left-commutes lw-cic-left-distributes lw-cic-fold-constants
              lw-cic-times-negative lw-cic-negative-times lw-cic-zero-times
              lw-cic-minus-one lw-cic-double-negative lw-cic-add-cancel lw-cic-double lw-cic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(defthm lw-circle-inner-factor-count-bound
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (rationalp cutoff-square) (<= 0 cutoff-square) (< cutoff-square 1)
                (rationalp center-square) (< 0 center-square)
                (rationalp cap) (<= 0 cap)
                (<= center-square (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0)))
                (lw-circle-factor-boundary-check roots leading cutoff-square cap))
           (< (lw-circle-inner-factor-count roots cutoff-square) (lw-circle-inner-factor-count-limit cutoff-square center-square cap)))
  :hints (("Goal"
           :use (lw-circle-reflected-factor-center-growth lw-cic-center-cap
                 (:instance lw-complex-disk-data (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0)) (radius (+ 1 cap)))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0)) (radius (+ 1 cap)))
                 (:instance lw-complex-norm-square-valid (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0)))
                 (:instance lw-cic-strict-limit (ratio cutoff-square)
                   (index (lw-circle-inner-factor-count roots cutoff-square))
                   (reflected-square (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:type-prescription lw-circle-inner-factor-count)
              lw-cic-left-commutes lw-cic-left-distributes lw-cic-fold-constants
              lw-cic-times-negative lw-cic-negative-times lw-cic-zero-times
              lw-cic-minus-one lw-cic-double-negative lw-cic-add-cancel lw-cic-double lw-cic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-factor-boundary-check-reflected
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (rationalp cap) (<= 0 cap)
                (lw-circle-factor-boundary-check roots leading cutoff-square cap))
           (lw-cauchy-boundary-check (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
             (lw-cauchy-orbit-rotation (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) 0 (lw-cauchy-coefficient-count (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) 1) cap))
  :hints (("Goal"
           :use (lw-cic-reflected-length
                 (:instance lw-cauchy-coefficient-count-natural (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (degree (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) (error 1))
                 (:instance lw-cic-transfer-boundary (degree (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square))) (samples (lw-cauchy-coefficient-count (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (len (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) 1))))
           :in-theory (union-theories '(lw-circle-factor-boundary-check posp natp) (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
