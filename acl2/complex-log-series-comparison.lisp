(in-package "ACL2")

(include-book "complex-log-grid-approximation")

; Compare the signed scalar logarithm with the real part of the finite
; polynomial sum of z^j/j. All three errors use the same mesh.

(local (defthm lw-cls-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cls-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cls-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cls-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cls-times-negative (a b) (b a)))
                 :in-theory (disable lw-cls-times-negative)))))

(local (defthm lw-cls-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cls-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cls-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cls-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cls-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cls-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cls-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cls-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cls-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cls-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cls-left-commutes)))))

(defun lw-complex-log-series-budget (ratio count mesh error)
  (let ((delta (* (/ mesh) ratio (/ (- 1 ratio)))))
    (+ (* mesh (+ (* 4 error) (* 19 delta delta)))
       (* 2 mesh delta (lw-rational-power ratio count))
       (* 2 count (/ mesh)))))

(local
 (defthm lw-cls-three-errors
   (implies (and (rationalp sampled) (rationalp integrated) (rationalp polynomial)
                 (rationalp logarithm) (rationalp path-error) (rationalp grid-error)
                 (rationalp series-error)
                 (<= (abs (+ logarithm (* 2 sampled))) path-error)
                 (<= (abs (- sampled integrated)) grid-error)
                 (<= (abs (- integrated polynomial)) series-error))
            (<= (abs (+ logarithm (* 2 polynomial)))
                (+ path-error (* 2 grid-error) (* 2 series-error))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-cls-left-commutes lw-cls-left-distributes lw-cls-fold-constants
              lw-cls-times-negative lw-cls-negative-times lw-cls-zero-times
              lw-cls-minus-one lw-cls-double-negative lw-cls-add-cancel lw-cls-double lw-cls-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cls-endpoint
   (implies (lw-complexp point)
            (equal (lw-complex-log-segment-factor point 1) (lw-complex-sub (cons 1 0) point)))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-segment-factor lw-complex-scale-one
              lw-cls-left-commutes lw-cls-left-distributes lw-cls-fold-constants
              lw-cls-times-negative lw-cls-negative-times lw-cls-zero-times
              lw-cls-minus-one lw-cls-double-negative lw-cls-add-cancel lw-cls-double lw-cls-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cls-polynomial-offset
   (implies (and (lw-complexp point) (natp count))
            (equal (lw-complex-polynomial (lw-complex-log-series-polynomial count) point 0) (lw-complex-polynomial (lw-complex-log-series-coefficients 1 count) point 1)))
   :hints (("Goal" :expand ((lw-complex-polynomial (cons (cons 0 0) (lw-complex-log-series-coefficients 1 count)) point 0))
                   :use ((:instance lw-complex-log-coefficients-data (mesh 1) (cells 1) (start 1))
                         (:instance lw-complex-polynomial-rational (coefficients (lw-complex-log-series-coefficients 1 count)) (offset 1))
                         (:instance lw-complex-power-rational (index 0)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-polynomial lw-complex-mul-zero lw-complex-add-zero endp
              lw-cls-left-commutes lw-cls-left-distributes lw-cls-fold-constants
              lw-cls-times-negative lw-cls-negative-times lw-cls-zero-times
              lw-cls-minus-one lw-cls-double-negative lw-cls-add-cancel lw-cls-double lw-cls-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cls-real-part-data
   (implies (and (lw-complexp a) (lw-complexp b))
            (and (rationalp (car a)) (rationalp (car b))
                 (equal (car (lw-complex-sub a b)) (- (car a) (car b)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub
              lw-cls-left-commutes lw-cls-left-distributes lw-cls-fold-constants
              lw-cls-times-negative lw-cls-negative-times lw-cls-zero-times
              lw-cls-minus-one lw-cls-double-negative lw-cls-add-cancel lw-cls-double lw-cls-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cls-reciprocal-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(defthm lw-complex-log-series-comparison
  (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                (posp mesh) (natp count)
                (<= (* (/ mesh) ratio (/ (- 1 ratio))) 1/4)
                (rationalp error) (< 0 error))
           (<= (abs (+ (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-sub (cons 1 0) point)) error)) (* 2 (car (lw-complex-polynomial (lw-complex-log-series-polynomial count) point 0)))))
               (lw-complex-log-series-budget ratio count mesh error)))
  :hints (("Goal"
           :use ((:instance lw-complex-disk-data (radius ratio))
                 (:instance lw-complex-disk-enlarge (radius ratio) (cap 1))
                 (:instance inverse-of-* (x mesh))
                 (:instance lw-complex-log-path-sum-bound (cells mesh))
                 (:instance lw-complex-log-grid-path-comparison (cells mesh))
                 (:instance lw-complex-log-path-sum-rational (cells mesh))
                 (:instance lw-complex-log-grid-series-comparison (start 1))
                 (:instance lw-complex-log-coefficients-data (cells mesh) (start 1))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-complex-log-grid-coefficients mesh mesh 1 count)) (offset 1))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-complex-log-series-coefficients 1 count)) (offset 1))
                 (:instance lw-complex-disk-coordinates (point (lw-complex-sub (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh mesh 1 count) point 1) (lw-complex-polynomial (lw-complex-log-series-coefficients 1 count) point 1)))
                   (radius (* count (/ mesh))))
                 (:instance lw-cls-real-part-data (a (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh mesh 1 count) point 1)) (b (lw-complex-polynomial (lw-complex-log-series-coefficients 1 count) point 1)))
                 (:instance lw-complex-ring-rational (left (cons 1 0)) (right point))
                 (:instance lw-complex-norm-square-valid (point (lw-complex-sub (cons 1 0) point)))
                 (:instance lw-complex-one-minus-norm-lower (radius ratio))
                 (:instance lw-cls-positive-product (a (- 1 ratio)) (b (- 1 ratio)))
                 (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
                 (:instance lw-cls-reciprocal-type (value mesh))
                 (:instance lw-cls-reciprocal-type (value (- 1 ratio)))
                 (:instance lw-rational-power-rational (base ratio) (exponent count))
                 (:instance lw-cls-three-errors (sampled (lw-complex-log-path-sum point mesh mesh))
                   (integrated (car (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh mesh 1 count) point 1))) (polynomial (car (lw-complex-polynomial (lw-complex-log-series-coefficients 1 count) point 1)))
                   (logarithm (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-sub (cons 1 0) point)) error)))
                   (path-error (* mesh (+ (* 4 error) (* 19 (* (/ mesh) ratio (/ (- 1 ratio))) (* (/ mesh) ratio (/ (- 1 ratio)))))))
                   (grid-error (* mesh (* (/ mesh) ratio (/ (- 1 ratio))) (lw-rational-power ratio count)))
                   (series-error (* count (/ mesh)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-budget lw-cls-endpoint lw-cls-polynomial-offset lw-intervalp
              lw-cls-left-commutes lw-cls-left-distributes lw-cls-fold-constants
              lw-cls-times-negative lw-cls-negative-times lw-cls-zero-times
              lw-cls-minus-one lw-cls-double-negative lw-cls-add-cancel lw-cls-double lw-cls-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
