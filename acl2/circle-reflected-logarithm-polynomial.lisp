(in-package "ACL2")

(include-book "circle-reflected-factor-normalization")
(include-book "complex-log-series-precision")
(include-book "polynomial-affine")
(include-book "polynomial-quadratic-bounds")

; Build a single polynomial whose real part is the sum of the
; factor logarithm series. Scaling sets the physical disk radius.

(local (defthm lw-crlp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crlp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crlp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crlp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crlp-times-negative (a b) (b a)))
                 :in-theory (disable lw-crlp-times-negative)))))

(local (defthm lw-crlp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crlp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crlp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crlp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crlp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crlp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crlp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crlp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crlp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-log-polynomial (roots cutoff-square scale count)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots)
      (list (cons 0 0))
    (lw-polynomial-add (lw-polynomial-affine (lw-complex-log-series-polynomial count) (cons 0 0) (lw-complex-scale scale (lw-circle-reflected-factor-parameter (car roots) cutoff-square))) (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count))))

(local
 (defthm lw-crlp-length-natural
   (natp (len coefficients))
   :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(defthm lw-circle-reflected-log-series-data
   (implies (natp count)
            (and (lw-complex-coefficientsp (lw-complex-log-series-polynomial count))
                 (consp (lw-complex-log-series-polynomial count))
                 (equal (lw-complex-polynomial (lw-complex-log-series-polynomial count) (cons 0 0) 0) (cons 0 0))))
   :hints (("Goal"
            :use ((:instance lw-complex-log-coefficients-data (mesh 1) (cells 1) (start 1))
                  (:instance lw-complex-polynomial-at-zero (coefficients (lw-complex-log-series-polynomial count)))
                  (:instance lw-complex-coefficient-at-nth (coefficients (lw-complex-log-series-polynomial count)) (target 0) (offset 0)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-polynomial lw-complex-coefficientsp len nth endp
              lw-crlp-left-commutes lw-crlp-left-distributes lw-crlp-fold-constants
              lw-crlp-times-negative lw-crlp-negative-times lw-crlp-zero-times
              lw-crlp-minus-one lw-crlp-double-negative lw-crlp-add-cancel lw-crlp-double lw-crlp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t)))

(local
 (defthm lw-crlp-term-data
   (implies (and (lw-complexp root) (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (natp count))
            (let ((factor (lw-polynomial-affine (lw-complex-log-series-polynomial count) (cons 0 0)
                          (lw-complex-scale scale (lw-circle-reflected-factor-parameter root cutoff-square)))))
              (and (lw-complex-coefficientsp factor)
                   (consp factor)
                   (equal (lw-complex-polynomial factor (cons 0 0) 0) (cons 0 0)))))
   :hints (("Goal"
            :use (lw-circle-reflected-log-series-data lw-circle-reflected-factor-parameter-data
                  (:instance lw-complex-scale-rational (factor scale) (point (lw-circle-reflected-factor-parameter root cutoff-square)))
                  (:instance lw-polynomial-affine-valid
                    (coefficients (lw-complex-log-series-polynomial count)) (center (cons 0 0))
                    (slope (lw-complex-scale scale (lw-circle-reflected-factor-parameter root cutoff-square))))
                  (:instance lw-polynomial-affine-evaluation
                    (coefficients (lw-complex-log-series-polynomial count)) (center (cons 0 0)) (point (cons 0 0))
                    (slope (lw-complex-scale scale (lw-circle-reflected-factor-parameter root cutoff-square))))
                  (:instance lw-complex-mul-zero
                    (point (lw-complex-scale scale (lw-circle-reflected-factor-parameter root cutoff-square)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-polynomial lw-complex-add-zero lw-crlp-length-natural len endp
              (:executable-counterpart lw-complex-add)
              lw-crlp-left-commutes lw-crlp-left-distributes lw-crlp-fold-constants
              lw-crlp-times-negative lw-crlp-negative-times lw-crlp-zero-times
              lw-crlp-minus-one lw-crlp-double-negative lw-crlp-add-cancel lw-crlp-double lw-crlp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlp-add-nonempty
   (implies (or (consp left) (consp right))
            (consp (lw-polynomial-add left right)))
   :hints (("Goal" :in-theory (union-theories '(lw-polynomial-add endp) (theory 'minimal-theory))))
   :rule-classes nil))

(defthm lw-circle-reflected-log-polynomial-data
  (implies (and (lw-ray-pointsp roots) (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                (rationalp scale) (natp count))
           (and (lw-complex-coefficientsp (lw-circle-reflected-log-polynomial roots cutoff-square scale count))
                (consp (lw-circle-reflected-log-polynomial roots cutoff-square scale count))
                (equal (lw-complex-polynomial (lw-circle-reflected-log-polynomial roots cutoff-square scale count) (cons 0 0) 0) (cons 0 0))))
  :hints (("Goal"
           :induct (lw-circle-reflected-log-polynomial roots cutoff-square scale count)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-log-polynomial) lw-circle-reflected-log-polynomial
              lw-ray-pointsp lw-complex-coefficientsp
              lw-polynomial-add-valid len endp (:executable-counterpart lw-complex-add) (:executable-counterpart lw-complex-mul)
              lw-crlp-left-commutes lw-crlp-left-distributes lw-crlp-fold-constants
              lw-crlp-times-negative lw-crlp-negative-times lw-crlp-zero-times
              lw-crlp-minus-one lw-crlp-double-negative lw-crlp-add-cancel lw-crlp-double lw-crlp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-crlp-term-data (root (car roots)))
                       (:instance lw-crlp-add-nonempty
                         (left (lw-polynomial-affine (lw-complex-log-series-polynomial count) (cons 0 0) (lw-complex-scale scale (lw-circle-reflected-factor-parameter (car roots) cutoff-square))))
                         (right (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count)))
                       (:instance lw-polynomial-add-evaluation (left (lw-polynomial-affine (lw-complex-log-series-polynomial count) (cons 0 0) (lw-complex-scale scale (lw-circle-reflected-factor-parameter (car roots) cutoff-square)))) (right (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count))
                         (point (cons 0 0)) (offset 0)))
                 :expand ((lw-complex-polynomial (list (cons 0 0)) (cons 0 0) 0)
                           (lw-complex-polynomial nil (cons 0 0) 1)
                           (lw-complex-power (cons 0 0) 0))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-crlp-shift-argument
   (implies (and (lw-complexp point) (lw-complexp parameter) (rationalp scale))
            (equal (lw-complex-add (cons 0 0) (lw-complex-mul (lw-complex-scale scale parameter) point))
                   (lw-complex-mul parameter (lw-complex-scale scale point))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-scale lw-complex-mul
              lw-crlp-left-commutes lw-crlp-left-distributes lw-crlp-fold-constants
              lw-crlp-times-negative lw-crlp-negative-times lw-crlp-zero-times
              lw-crlp-minus-one lw-crlp-double-negative lw-crlp-add-cancel lw-crlp-double lw-crlp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(defthm lw-circle-reflected-log-polynomial-step
  (implies (and (lw-ray-pointsp roots) (consp roots) (lw-complexp point)
                (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                (rationalp scale) (natp count))
           (equal (lw-complex-polynomial (lw-circle-reflected-log-polynomial roots cutoff-square scale count) point 0)
                  (lw-complex-add (lw-complex-polynomial (lw-complex-log-series-polynomial count) (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point)) 0)
                                  (lw-complex-polynomial (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count) point 0))))
  :hints (("Goal"
           :use ((:instance lw-crlp-term-data (root (car roots)))
                 (:instance lw-circle-reflected-log-polynomial-data (roots (cdr roots)))
                 lw-circle-reflected-log-series-data
                 (:instance lw-circle-reflected-factor-parameter-data (root (car roots)))
                 (:instance lw-complex-scale-rational (point (lw-circle-reflected-factor-parameter (car roots) cutoff-square)) (factor scale))
                 (:instance lw-polynomial-affine-evaluation
                   (coefficients (lw-complex-log-series-polynomial count)) (center (cons 0 0)) (slope (lw-complex-scale scale (lw-circle-reflected-factor-parameter (car roots) cutoff-square))))
                 (:instance lw-polynomial-add-evaluation (left (lw-polynomial-affine (lw-complex-log-series-polynomial count) (cons 0 0) (lw-complex-scale scale (lw-circle-reflected-factor-parameter (car roots) cutoff-square)))) (right (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count)) (offset 0)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-log-polynomial lw-crlp-shift-argument lw-ray-pointsp endp
              lw-crlp-left-commutes lw-crlp-left-distributes lw-crlp-fold-constants
              lw-crlp-times-negative lw-crlp-negative-times lw-crlp-zero-times
              lw-crlp-minus-one lw-crlp-double-negative lw-crlp-add-cancel lw-crlp-double lw-crlp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
