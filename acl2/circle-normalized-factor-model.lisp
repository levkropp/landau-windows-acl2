(in-package "ACL2")

(include-book "circle-no-inner-factors")
(include-book "circle-pole-split")
(include-book "complex-exp")

; Transport a given physical factorization to unit-disk coordinates.

(local (defthm lw-cnfm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cnfm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cnfm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cnfm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cnfm-times-negative (a b) (b a)))
                 :in-theory (disable lw-cnfm-times-negative)))))

(local (defthm lw-cnfm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cnfm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cnfm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cnfm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cnfm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cnfm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cnfm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cnfm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnfm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnfm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cnfm-left-commutes)))))

(defun lw-circle-scale-factor-roots (roots factor)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots) nil
    (cons (lw-complex-scale factor (car roots))
          (lw-circle-scale-factor-roots (cdr roots) factor))))

(defun lw-circle-rescale-factor-leading (roots leading scale)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots) leading
    (lw-complex-scale scale (lw-circle-rescale-factor-leading (cdr roots) leading scale))))

(defthm lw-circle-scale-factor-roots-data
  (implies (and (lw-ray-pointsp roots) (rationalp factor))
           (lw-ray-pointsp (lw-circle-scale-factor-roots roots factor)))
  :hints (("Goal"
           :induct (lw-circle-scale-factor-roots roots factor)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-scale-factor-roots lw-ray-pointsp lw-complex-scale-rational endp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))))

(defthm lw-circle-rescale-factor-leading-rational
  (implies (and (lw-complexp leading) (rationalp scale))
           (lw-complexp (lw-circle-rescale-factor-leading roots leading scale)))
  :hints (("Goal"
           :induct (lw-circle-rescale-factor-leading roots leading scale)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-rescale-factor-leading lw-complex-scale-rational endp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))))

(local
 (defthm lw-cnfm-factor-leading-linearity
   (implies (and (lw-ray-pointsp roots) (lw-complexp point)
                 (lw-complexp leading) (rationalp factor))
            (equal (lw-polynomial-linear-factor-value roots (lw-complex-scale factor leading) point)
                   (lw-complex-scale factor (lw-polynomial-linear-factor-value roots leading point))))
   :hints (("Goal"
            :induct (lw-polynomial-linear-factor-value roots leading point)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-linear-factor-value lw-ray-pointsp lw-complex-scale-rational
               lw-polynomial-linear-factor-value-rational lw-complex-ring-rational lw-complex-scale-product endp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-cnfm-scale-difference
   (implies (and (lw-complexp point) (lw-complexp root) (rationalp scale) (< 0 scale))
            (equal (lw-complex-sub point (lw-complex-scale (/ scale) root))
                   (lw-complex-scale (/ scale) (lw-complex-sub (lw-complex-scale scale point) root))))
   :hints (("Goal"
            :use ((:instance lw-cnfm-inverse-factor (divisor scale) (coefficient (car point)))
                  (:instance lw-cnfm-inverse-factor (divisor scale) (coefficient (cdr point))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-sub
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-normalized-factor-evaluation
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                (rationalp scale) (< 0 scale))
           (equal (lw-polynomial-linear-factor-value (lw-circle-scale-factor-roots roots (/ scale)) (lw-circle-rescale-factor-leading roots leading scale) point)
                  (lw-polynomial-linear-factor-value roots leading (lw-complex-scale scale point))))
  :hints (("Goal"
           :induct (lw-circle-scale-factor-roots roots (/ scale))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-scale-factor-roots lw-circle-rescale-factor-leading
              lw-polynomial-linear-factor-value lw-ray-pointsp endp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cnfm-factor-leading-linearity
                         (roots (lw-circle-scale-factor-roots (cdr roots) (/ scale))) (leading (lw-circle-rescale-factor-leading (cdr roots) leading scale)) (factor scale))
                       (:instance lw-circle-scale-factor-roots-data (roots (cdr roots)) (factor (/ scale)))
                       (:instance lw-circle-rescale-factor-leading-rational (roots (cdr roots)))
                       (:instance lw-complex-scale-rational (factor scale))
                       (:instance lw-polynomial-linear-factor-value-rational
                         (roots (cdr roots)) (point (lw-complex-scale scale point)))
                       (:instance lw-polynomial-linear-factor-value-rational
                         (roots (lw-circle-scale-factor-roots (cdr roots) (/ scale))) (leading (lw-circle-rescale-factor-leading (cdr roots) leading scale)))
                       (:instance lw-complex-ring-rational (left (lw-complex-scale scale point)) (right (car roots)))
                       (:instance lw-cnfm-scale-difference (root (car roots)))
                       (:instance lw-complex-ring-rational (left (lw-complex-sub (lw-complex-scale scale point) (car roots))) (right (lw-polynomial-linear-factor-value (cdr roots) leading (lw-complex-scale scale point))))
                       (:instance lw-complex-mul-scales (left (/ scale)) (right scale) (a (lw-complex-sub (lw-complex-scale scale point) (car roots))) (b (lw-polynomial-linear-factor-value (cdr roots) leading (lw-complex-scale scale point))))
                       (:instance inverse-of-* (x scale)))
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-scale-one lw-polynomial-linear-factor-value
                     lw-circle-scale-factor-roots lw-circle-rescale-factor-leading lw-ray-pointsp endp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-cnfm-cancel-squared-scale
   (implies (and (rationalp scale) (< 0 scale) (rationalp component))
            (equal (* scale scale (/ scale) (/ scale) component) component))
   :hints (("Goal"
            :use ((:instance lw-cnfm-inverse-factor (divisor scale) (coefficient (* scale (/ scale) component)))
                  (:instance lw-cnfm-inverse-factor (divisor scale) (coefficient component)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnfm-normalized-norm
   (implies (and (lw-complexp root) (rationalp scale) (< 0 scale))
            (equal (* scale scale (lw-complex-norm-square (lw-complex-scale (/ scale) root)))
                   (lw-complex-norm-square root)))
   :hints (("Goal"
            :use ((:instance lw-cnfm-cancel-squared-scale (component (* (car root) (car root))))
                  (:instance lw-cnfm-cancel-squared-scale (component (* (cdr root) (cdr root)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-norm-square lw-complex-scale lw-complexp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-normalized-inner-count-empty
  (implies (and (lw-ray-pointsp roots) (rationalp scale) (< 0 scale) (rationalp radius) (< 0 radius)
                (rationalp cutoff-square) (< (* scale scale cutoff-square) (* radius radius))
                (endp (lw-circle-pole-roots roots radius)))
           (equal (lw-circle-inner-factor-count (lw-circle-scale-factor-roots roots (/ scale)) cutoff-square) 0))
  :hints (("Goal"
           :induct (lw-circle-scale-factor-roots roots (/ scale))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-scale-factor-roots lw-circle-pole-roots
              lw-circle-inner-factor-count lw-ray-pointsp endp
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cnfm-normalized-norm (root (car roots)))
                       (:instance lw-complex-scale-rational (factor (/ scale)) (point (car roots)))
                       (:instance lw-complex-norm-square-valid (point (lw-complex-scale (/ scale) (car roots))))
                       (:instance lw-cnfm-positive-product (a scale) (b scale))
                       (:instance lw-cnfm-multiply-order (a (lw-complex-norm-square (lw-complex-scale (/ scale) (car roots)))) (b cutoff-square) (factor (* scale scale))))
                  :do-not-induct t)))
  :rule-classes nil)

(defun lw-circle-normalized-factor-polynomial (roots leading scale)
  (lw-polynomial-factor-coefficients
    (lw-circle-scale-factor-roots roots (/ scale))
    (lw-circle-rescale-factor-leading roots leading scale)))

(defthm lw-circle-normalized-factor-polynomial-evaluation
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                (rationalp scale) (< 0 scale))
           (equal (lw-complex-polynomial (lw-circle-normalized-factor-polynomial roots leading scale) point 0)
                  (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading)
                                         (lw-complex-scale scale point) 0)))
  :hints (("Goal"
           :use (lw-circle-normalized-factor-evaluation lw-circle-rescale-factor-leading-rational
                 (:instance lw-complex-scale-rational (factor scale))
                 (:instance lw-circle-scale-factor-roots-data (factor (/ scale)))
                 (:instance lw-polynomial-factor-coefficients-evaluation
                   (point (lw-complex-scale scale point)))
                 (:instance lw-polynomial-factor-coefficients-evaluation
                   (roots (lw-circle-scale-factor-roots roots (/ scale)))
                   (leading (lw-circle-rescale-factor-leading roots leading scale))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-normalized-factor-polynomial
              lw-cnfm-left-commutes lw-cnfm-left-distributes lw-cnfm-fold-constants
              lw-cnfm-times-negative lw-cnfm-negative-times lw-cnfm-zero-times
              lw-cnfm-minus-one lw-cnfm-double-negative lw-cnfm-add-cancel lw-cnfm-double lw-cnfm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
