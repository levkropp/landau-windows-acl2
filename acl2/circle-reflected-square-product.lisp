(in-package "ACL2")

(include-book "circle-reflected-factor-normalization")

; Separate the squared center factors from the normalized factors.
; Positivity on the strict disk permits signed logarithm comparisons.

(local (defthm lw-crsq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crsq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crsq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crsq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crsq-times-negative (a b) (b a)))
                 :in-theory (disable lw-crsq-times-negative)))))

(local (defthm lw-crsq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crsq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crsq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crsq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crsq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crsq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crsq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crsq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crsq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-unit-factor (root cutoff-square point)
  (lw-complex-sub (cons 1 0)
    (lw-complex-mul (lw-circle-reflected-factor-parameter root cutoff-square) point)))

(defun lw-circle-reflected-value-square (roots leading cutoff-square point)
  (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0)))

(defthm lw-circle-reflected-square-empty
  (implies (and (lw-complexp leading) (lw-complexp point))
           (equal (lw-circle-reflected-value-square nil leading cutoff-square point) (lw-complex-norm-square leading)))
  :hints (("Goal" :use ((:instance lw-circle-reflected-factor-evaluation (roots nil)))
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-value-square
              (:executable-counterpart lw-ray-pointsp) endp
              lw-crsq-left-commutes lw-crsq-left-distributes lw-crsq-fold-constants
              lw-crsq-times-negative lw-crsq-negative-times lw-crsq-zero-times
              lw-crsq-minus-one lw-crsq-double-negative lw-crsq-add-cancel lw-crsq-double lw-crsq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t)))

(defthm lw-circle-reflected-square-step
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                (rationalp cutoff-square) (<= 0 cutoff-square) (consp roots))
           (equal (lw-circle-reflected-value-square roots leading cutoff-square point)
                  (* (lw-complex-norm-square (lw-circle-reflected-factor-normalization (car roots) cutoff-square))
                     (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square point))
                     (lw-circle-reflected-value-square (cdr roots) leading cutoff-square point))))
  :hints (("Goal"
           :use (lw-circle-reflected-factor-evaluation
                 (:instance lw-circle-reflected-factor-normalization-valid (root (car roots)))
                 (:instance lw-circle-reflected-factor-polynomial-valid (roots (cdr roots)))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square)) (offset 0))
                 (:instance lw-complex-conjugate-rational (point (car roots)))
                 (:instance lw-complex-reciprocal-rational (point (car roots)))
                 (:instance lw-complex-ring-rational (left (lw-circle-reflected-factor-parameter (car roots) cutoff-square)) (right point))
                 (:instance lw-complex-ring-rational
                   (left (cons 1 0)) (right (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) point)))
                 (:instance lw-complex-ring-rational (left (lw-circle-reflected-factor-normalization (car roots) cutoff-square)) (right (lw-circle-reflected-unit-factor (car roots) cutoff-square point)))
                 (:instance lw-complex-norm-square-product (left (lw-circle-reflected-factor-normalization (car roots) cutoff-square)) (right (lw-circle-reflected-unit-factor (car roots) cutoff-square point)))
                 (:instance lw-complex-norm-square-product
                   (left (lw-complex-mul (lw-circle-reflected-factor-normalization (car roots) cutoff-square) (lw-circle-reflected-unit-factor (car roots) cutoff-square point))) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-unit-factor lw-circle-reflected-factor-parameter
              lw-circle-reflected-value-square lw-ray-pointsp endp
              lw-crsq-left-commutes lw-crsq-left-distributes lw-crsq-fold-constants
              lw-crsq-times-negative lw-crsq-negative-times lw-crsq-zero-times
              lw-crsq-minus-one lw-crsq-double-negative lw-crsq-add-cancel lw-crsq-double lw-crsq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-reflected-unit-square-positive
   (implies (and (lw-complexp root) (lw-complex-diskp point radius)
                 (rationalp cutoff-square) (rationalp radius) (< 0 radius)
                 (< (* radius radius) cutoff-square) (< cutoff-square 1))
            (and (rationalp (lw-complex-norm-square (lw-circle-reflected-factor-normalization root cutoff-square))) (< 0 (lw-complex-norm-square (lw-circle-reflected-factor-normalization root cutoff-square)))
                 (rationalp (lw-complex-norm-square (lw-circle-reflected-unit-factor root cutoff-square point))) (< 0 (lw-complex-norm-square (lw-circle-reflected-unit-factor root cutoff-square point)))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data)
                  (:instance lw-circle-reflected-factor-normalization-valid)
                  (:instance lw-circle-reflected-factor-argument-disk (inner-radius radius))
                  (:instance lw-complex-disk-data
                    (point (lw-complex-mul (lw-circle-reflected-factor-parameter root cutoff-square) point))
                    (radius (lw-circle-reflected-factor-ratio radius cutoff-square)))
                  (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-mul (lw-circle-reflected-factor-parameter root cutoff-square) point)))
                  (:instance lw-complex-one-minus-norm-lower (point (lw-complex-mul (lw-circle-reflected-factor-parameter root cutoff-square) point))
                    (radius (lw-circle-reflected-factor-ratio radius cutoff-square)))
                  (:instance lw-crsq-positive-product
                    (a (- 1 (lw-circle-reflected-factor-ratio radius cutoff-square)))
                    (b (- 1 (lw-circle-reflected-factor-ratio radius cutoff-square))))
                  (:instance lw-crsq-positive-product (a radius) (b radius))
                  (:instance lw-complex-norm-square-valid (point (lw-circle-reflected-factor-normalization root cutoff-square)))
                  (:instance lw-complex-norm-square-positive (point (lw-circle-reflected-factor-normalization root cutoff-square)))
                  (:instance lw-complex-norm-square-valid (point (lw-circle-reflected-unit-factor root cutoff-square point))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-unit-factor
              lw-crsq-left-commutes lw-crsq-left-distributes lw-crsq-fold-constants
              lw-crsq-times-negative lw-crsq-negative-times lw-crsq-zero-times
              lw-crsq-minus-one lw-crsq-double-negative lw-crsq-add-cancel lw-crsq-double lw-crsq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil)

(defthm lw-circle-reflected-square-positive
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                (lw-complex-diskp point radius) (rationalp radius) (< 0 radius)
                (rationalp cutoff-square) (< (* radius radius) cutoff-square) (< cutoff-square 1))
           (and (rationalp (lw-circle-reflected-value-square roots leading cutoff-square point)) (< 0 (lw-circle-reflected-value-square roots leading cutoff-square point))))
  :hints (("Goal"
           :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-factor-polynomial)
              lw-circle-reflected-square-empty lw-ray-pointsp endp
              lw-complex-norm-square-valid lw-complex-norm-square-positive
              lw-crsq-left-commutes lw-crsq-left-distributes lw-crsq-fold-constants
              lw-crsq-times-negative lw-crsq-negative-times lw-crsq-zero-times
              lw-crsq-minus-one lw-crsq-double-negative lw-crsq-add-cancel lw-crsq-double lw-crsq-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-disk-data)
                       (:instance lw-crsq-positive-product (a radius) (b radius))
                       lw-circle-reflected-square-step
                       (:instance lw-circle-reflected-unit-square-positive (root (car roots)))
                       (:instance lw-crsq-positive-product
                         (a (lw-complex-norm-square (lw-circle-reflected-factor-normalization (car roots) cutoff-square))) (b (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square point))))
                       (:instance lw-crsq-positive-product
                         (a (* (lw-complex-norm-square (lw-circle-reflected-factor-normalization (car roots) cutoff-square)) (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square point))))
                         (b (lw-circle-reflected-value-square (cdr roots) leading cutoff-square point))))
                 :do-not-induct t)))
  :rule-classes nil)
