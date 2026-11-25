(in-package "ACL2")

(include-book "circle-reflected-logarithm-comparison")
(include-book "circle-reflected-harnack-budget")

; Add a real constant to the doubled factor logarithm polynomial.
; Its constant term and pointwise comparison have fixed rational bounds.

(local (defthm lw-crhp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crhp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crhp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crhp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crhp-times-negative (a b) (b a)))
                 :in-theory (disable lw-crhp-times-negative)))))

(local (defthm lw-crhp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crhp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crhp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crhp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crhp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crhp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crhp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crhp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crhp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crhp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-crhp-left-commutes)))))

(defun lw-circle-reflected-harnack-tolerance (roots)
  (/ (* 32 (+ 1 (len roots)))))

(defun lw-circle-reflected-harnack-error (roots cutoff-square scale)
  (min (lw-circle-reflected-harnack-tolerance roots) (lw-complex-log-series-request (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots))))

(defun lw-circle-reflected-harnack-polynomial (roots cutoff-square scale center-lower boundary-cap)
  (let ((logarithm (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots)))))
    (lw-polynomial-add-constant (cons (lw-circle-reflected-log-offset center-lower boundary-cap) 0) (lw-polynomial-add logarithm logarithm))))

(local
 (defthm lw-crhp-length-natural
   (natp (len roots))
   :hints (("Goal" :induct (len roots) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-crhp-tolerance-data
   (and (rationalp (lw-circle-reflected-harnack-tolerance roots)) (< 0 (lw-circle-reflected-harnack-tolerance roots)) (<= (lw-circle-reflected-harnack-tolerance roots) 1)
        (<= (* 10 (len roots) (lw-circle-reflected-harnack-tolerance roots)) 1))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value (* 32 (+ 1 (len roots)))))
                  (:instance lw-reciprocal-antitone (left 1) (right (* 32 (+ 1 (len roots)))))
                  (:instance lw-crhp-multiply-order
                    (a (* 10 (len roots))) (b (* 32 (+ 1 (len roots))))
                    (factor (/ (* 32 (+ 1 (len roots))))))
                  (:instance lw-crhp-inverse-factor (divisor (* 32 (+ 1 (len roots)))) (coefficient 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-harnack-tolerance lw-crhp-length-natural
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-harnack-error-data
  (implies (and (rationalp scale) (< 0 scale)
                (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1))
           (and (natp (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots)))
                (rationalp (lw-circle-reflected-harnack-tolerance roots)) (< 0 (lw-circle-reflected-harnack-tolerance roots))
                (rationalp (lw-circle-reflected-harnack-error roots cutoff-square scale)) (< 0 (lw-circle-reflected-harnack-error roots cutoff-square scale)) (<= (lw-circle-reflected-harnack-error roots cutoff-square scale) 1)
                (<= (lw-circle-reflected-harnack-error roots cutoff-square scale) (lw-complex-log-series-request (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots)))
                (<= (* (len roots) (+ (lw-circle-reflected-harnack-tolerance roots) (* 9 (lw-circle-reflected-harnack-error roots cutoff-square scale)))) 1)))
  :hints (("Goal"
           :use (lw-crhp-tolerance-data
                 (:instance lw-complex-zero-disk (radius scale))
                 (:instance lw-circle-reflected-factor-argument-disk (root (cons 0 0)) (point (cons 0 0)) (inner-radius scale))
                 (:instance lw-complex-log-series-request-data (ratio (lw-circle-reflected-factor-ratio scale cutoff-square)) (tolerance (lw-circle-reflected-harnack-tolerance roots)))
                 (:instance lw-crhp-multiply-order
                   (a (lw-circle-reflected-harnack-error roots cutoff-square scale)) (b (lw-circle-reflected-harnack-tolerance roots)) (factor (* 9 (len roots)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-harnack-error lw-crhp-length-natural min
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-crhp-head-zero
   (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
                 (equal (lw-complex-polynomial coefficients (cons 0 0) 0) (cons 0 0)))
            (equal (car coefficients) (cons 0 0)))
   :hints (("Goal"
            :use (lw-complex-polynomial-at-zero (:instance lw-complex-coefficient-at-nth (target 0) (offset 0)))
            :expand ((len coefficients))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-crhp-length-natural nth len endp
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crhp-add-constant-data
   (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
                 (equal (car coefficients) (cons 0 0)) (rationalp constant))
            (let ((shifted (lw-polynomial-add-constant (cons constant 0)
                            (lw-polynomial-add coefficients coefficients))))
              (and (lw-complex-coefficientsp shifted) (consp shifted)
                   (equal (car shifted) (cons constant 0)))))
   :hints (("Goal"
            :use ((:instance lw-polynomial-add-valid (left coefficients) (right coefficients))
                  (:instance lw-polynomial-add-constant-valid (constant (cons constant 0))
                    (coefficients (lw-polynomial-add coefficients coefficients))))
            :expand ((lw-polynomial-add coefficients coefficients))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-add-constant lw-polynomial-add
              lw-complex-coefficientsp lw-complex-add-zero
              (:executable-counterpart lw-complex-add) lw-complexp endp
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-harnack-polynomial-data
  (implies (and (lw-ray-pointsp roots)
                (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (rationalp center-lower) (< 0 center-lower)
                (rationalp boundary-cap) (<= 0 boundary-cap))
           (and (lw-complex-coefficientsp (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)) (consp (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap))
                (equal (car (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap)) (cons (lw-circle-reflected-log-offset center-lower boundary-cap) 0))))
  :hints (("Goal"
           :use (lw-circle-reflected-log-offset-positive lw-circle-reflected-harnack-error-data
                 (:instance lw-circle-reflected-log-polynomial-data (count (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots))))
                 (:instance lw-crhp-head-zero (coefficients (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots)))))
                 (:instance lw-crhp-add-constant-data (coefficients (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots)))) (constant (lw-circle-reflected-log-offset center-lower boundary-cap))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-harnack-polynomial
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-crhp-evaluate-doubled-model
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (rationalp constant))
            (let* ((shifted (lw-polynomial-add-constant (cons constant 0) (lw-polynomial-add coefficients coefficients)))
                   (base (lw-complex-polynomial coefficients point 0))
                   (value (lw-complex-polynomial shifted point 0)))
              (and (rationalp (car value)) (rationalp (car base))
                   (equal (car value) (+ constant (* 2 (car base)))))))
   :hints (("Goal"
            :use ((:instance lw-polynomial-add-valid (left coefficients) (right coefficients))
                  (:instance lw-polynomial-add-evaluation (left coefficients) (right coefficients) (offset 0))
                  (:instance lw-polynomial-add-constant-evaluation (constant (cons constant 0))
                    (coefficients (lw-polynomial-add coefficients coefficients)))
                  (:instance lw-complex-polynomial-rational (offset 0)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-harnack-log-comparison
  (implies (and (lw-ray-pointsp roots)
                (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square) (rationalp center-lower) (< 0 center-lower)
                (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-complexp leading) (not (equal leading (cons 0 0))) (lw-complex-diskp point 1))
           (let* ((value (car (lw-complex-polynomial (lw-circle-reflected-harnack-polynomial roots cutoff-square scale center-lower boundary-cap) point 0)))
                  (log-ratio (lw-circle-reflected-log-ratio roots leading cutoff-square (lw-complex-scale scale point) (lw-circle-reflected-harnack-error roots cutoff-square scale))))
             (and (rationalp value)
                  (<= (abs (+ log-ratio (- value (lw-circle-reflected-log-offset center-lower boundary-cap)))) 1))))
  :hints (("Goal"
           :use (lw-circle-reflected-harnack-error-data lw-circle-reflected-log-offset-positive
                 (:instance lw-circle-reflected-logarithm-comparison (tolerance (lw-circle-reflected-harnack-tolerance roots)) (error (lw-circle-reflected-harnack-error roots cutoff-square scale)))
                 (:instance lw-complex-disk-data (radius 1))
                 (:instance lw-circle-reflected-log-polynomial-data (count (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots))))
                 (:instance lw-crhp-evaluate-doubled-model (coefficients (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) (lw-circle-reflected-harnack-tolerance roots)))) (constant (lw-circle-reflected-log-offset center-lower boundary-cap))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-harnack-polynomial lw-crhp-length-natural
              lw-crhp-left-commutes lw-crhp-left-distributes lw-crhp-fold-constants
              lw-crhp-times-negative lw-crhp-negative-times lw-crhp-zero-times
              lw-crhp-minus-one lw-crhp-double-negative lw-crhp-add-cancel lw-crhp-double lw-crhp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
