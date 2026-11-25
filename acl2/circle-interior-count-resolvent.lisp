(in-package "ACL2")

(include-book "circle-exterior-resolvent")
(include-book "cauchy-resolvents")

; Multiplication by the contour offset turns an interior reciprocal into a
; resolvent in the conjugate unit variable, with constant coefficient one.

(local (defthm lw-cirv-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cirv-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cirv-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cirv-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cirv-times-negative (a b) (b a)))
                 :in-theory (disable lw-cirv-times-negative)))))

(local (defthm lw-cirv-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cirv-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cirv-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cirv-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cirv-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cirv-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cirv-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cirv-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cirv-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cirv-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cirv-left-commutes)))))

(local (defthm lw-cirv-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cirv-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cirv-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cirv-multiply-strict
 (implies (and (rationalp a) (rationalp b) (< a b) (rationalp factor) (< 0 factor))
  (< (* a factor) (* b factor)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-cirv-square-nonnegative
 (implies (rationalp x) (<= 0 (* x x)))
 :rule-classes nil
 :hints (("Goal" :cases ((<= 0 x))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-cirv-half-sum-square
 (implies (rationalp s)
  (<= s (* 1/2 (+ 1 s) 1/2 (+ 1 s))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lw-cirv-square-nonnegative (x (* 1/2 (- s 1))))) :in-theory (union-theories
 '(fold-consts-in-+ lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp nil :do-not-induct t))))

(local (defthm lw-cirv-square-scale
 (implies (and (rationalp factor) (lw-complexp root))
  (equal (lw-complex-norm-square (lw-complex-scale factor root))
         (* factor factor (lw-complex-norm-square root))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complexp lw-complex-norm-square lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cirv-inverse-square
 (implies (and (rationalp radius) (< 0 radius))
  (equal (* (/ radius) (/ radius) radius radius) 1))
 :hints (("Goal"
  :use ((:instance lw-cirv-inverse-factor (divisor radius) (coefficient 1)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cirv-inverse-rational lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(defun lw-circle-interior-count-ratio (root radius)
 (lw-complex-scale (/ radius) (lw-complex-conjugate root)))

(defun lw-circle-interior-count-ratio-cap (root radius)
 (* 1/2 (+ 1 (lw-complex-norm-square (lw-circle-interior-count-ratio root radius)))))

(local (defthm lw-cirv-conjugate-norm
 (implies (lw-complexp point)
  (equal (lw-complex-norm-square (lw-complex-conjugate point))
         (lw-complex-norm-square point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-conjugate lw-complex-norm-square lw-complexp lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cirv-ratio-norm-data
 (implies (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (lw-complex-norm-square root) (* radius radius)))
  (and (lw-complexp (lw-circle-interior-count-ratio root radius)) (rationalp (lw-complex-norm-square (lw-circle-interior-count-ratio root radius))) (<= 0 (lw-complex-norm-square (lw-circle-interior-count-ratio root radius))) (< (lw-complex-norm-square (lw-circle-interior-count-ratio root radius)) 1)))
 :hints (("Goal"
  :use (lw-cirv-inverse-square
        (:instance lw-complex-conjugate-rational (point root))
        (:instance lw-cirv-conjugate-norm (point root))
        (:instance lw-complex-norm-square-valid (point root))
        (:instance lw-cirv-square-scale (factor (/ radius)) (root (lw-complex-conjugate root)))
        (:instance lw-complex-norm-square-valid (point (lw-circle-interior-count-ratio root radius)))
        (:instance lw-complex-scale-rational (factor (/ radius)) (point (lw-complex-conjugate root)))
        (:instance lw-reciprocal-positive (value radius))
        (:instance lw-cirv-positive-product (a (/ radius)) (b (/ radius)))
        (:instance lw-cirv-multiply-strict (a (lw-complex-norm-square root)) (b (* radius radius))
                    (factor (* (/ radius) (/ radius)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-ratio lw-cirv-inverse-rational lw-cirv-product-rational lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-circle-interior-count-ratio-data
 (implies (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (lw-complex-norm-square root) (* radius radius)))
  (and (lw-complexp (lw-circle-interior-count-ratio root radius)) (rationalp (lw-circle-interior-count-ratio-cap root radius)) (<= 0 (lw-circle-interior-count-ratio-cap root radius)) (< (lw-circle-interior-count-ratio-cap root radius) 1)
       (lw-complex-diskp (lw-circle-interior-count-ratio root radius) (lw-circle-interior-count-ratio-cap root radius))))
 :hints (("Goal"
  :use (lw-cirv-ratio-norm-data
        (:instance lw-cirv-half-sum-square (s (lw-complex-norm-square (lw-circle-interior-count-ratio root radius))))
        (:instance lw-complex-disk-norm-square (point (lw-circle-interior-count-ratio root radius)) (radius (lw-circle-interior-count-ratio-cap root radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-ratio-cap lw-cirv-sum-rational lw-cirv-product-rational lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cirv-conjugate-reciprocal
 (implies (lw-complexp point)
  (equal (lw-complex-conjugate (lw-complex-reciprocal point))
         (lw-complex-reciprocal (lw-complex-conjugate point))))
 :hints (("Goal" :use (lw-cirv-conjugate-norm lw-complex-norm-square-valid lw-complex-conjugate-rational
        (:instance lw-complex-conjugate-scale (point (lw-complex-conjugate point)) (factor (/ (lw-complex-norm-square point)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-reciprocal lw-complex-conjugate-scale lw-complex-conjugate-involution lw-cirv-inverse-rational lw-complex-norm-square-valid lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cirv-unit-squares
 (implies (and (rationalp a) (rationalp b) (rationalp x) (rationalp radius)
               (< 0 radius) (equal (+ (* a a) (* b b)) 1))
  (equal (+ (- (* radius (/ radius) a a x)) (- (* radius (/ radius) b b x))) (- x)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance distributivity (x (* radius (/ radius) x)) (y (* a a)) (z (* b b)))
        (:instance lw-cirv-inverse-factor (divisor radius) (coefficient x)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cirv-inverse-rational lw-cirv-product-rational lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cirv-denominator-factorization
 (implies (and (lw-complexp root) (rationalp radius) (< 0 radius)
               (lw-complexp point) (equal (lw-complex-norm-square point) 1))
  (equal (lw-complex-mul (lw-complex-scale radius point) (lw-complex-conjugate (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-circle-interior-count-ratio root radius) point))))
         (lw-complex-sub (lw-complex-scale radius point) root)))
 :hints (("Goal"
  :use ((:instance lw-cirv-unit-squares (a (car point)) (b (cdr point)) (x (car root)))
        (:instance lw-cirv-unit-squares (a (car point)) (b (cdr point)) (x (cdr root))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-ratio lw-complex-conjugate lw-complex-norm-square lw-complex-mul lw-complex-scale lw-complex-sub lw-complexp lw-cirv-inverse-rational lw-cirv-product-rational lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))))

(local (defthm lw-cirv-scale-unit-nonzero
 (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (rationalp radius) (< 0 radius))
  (not (equal (lw-complex-scale radius point) (cons 0 0))))
 :hints (("Goal"
  :use ((:instance lw-cirv-square-scale (factor radius) (root point))
        (:instance lw-cirv-positive-product (a radius) (b radius)))
  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complex-norm-square) lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cirv-conjugate-nonzero
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
          (not (equal (lw-complex-conjugate point) (cons 0 0))))
 :hints (("Goal" :use (lw-complex-conjugate-involution)
  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complex-conjugate) lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-circle-interior-count-resolvent-identity
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (lw-complex-norm-square root) (* radius radius))) (lw-complexp point) (equal (lw-complex-norm-square point) 1))
  (equal (lw-complex-mul (lw-complex-scale radius point) (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) root)))
         (lw-complex-conjugate (lw-resolvent-value (lw-circle-interior-count-ratio root radius) point))))
 :hints (("Goal"
  :use (lw-circle-interior-count-ratio-data lw-cirv-denominator-factorization
        (:instance lw-complex-disk-norm-square (radius 1))
        (:instance lw-complex-mul-disk (left (lw-circle-interior-count-ratio root radius)) (right point) (radius (lw-circle-interior-count-ratio-cap root radius)) (other-radius 1))
        (:instance lw-complex-disk-excludes-one (point (lw-complex-mul (lw-circle-interior-count-ratio root radius) point)) (radius (lw-circle-interior-count-ratio-cap root radius)))
        (:instance lw-complex-one-minus-nonzero (point (lw-complex-mul (lw-circle-interior-count-ratio root radius) point)))
        lw-cirv-scale-unit-nonzero
        (:instance lw-cirv-conjugate-nonzero (point (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-circle-interior-count-ratio root radius) point))))
        (:instance lw-complex-reciprocal-product (a (lw-complex-scale radius point)) (b (lw-complex-conjugate (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-circle-interior-count-ratio root radius) point)))))
        (:instance lw-complex-reciprocal-cancel-product (a (lw-complex-scale radius point)) (b (lw-complex-reciprocal (lw-complex-conjugate (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-circle-interior-count-ratio root radius) point))))))
        (:instance lw-cirv-conjugate-reciprocal (point (lw-complex-sub (cons 1 0) (lw-complex-mul (lw-circle-interior-count-ratio root radius) point)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-resolvent-value lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-conjugate-rational lw-complex-scale-rational (:executable-counterpart lw-complexp) lw-cirv-left-commutes lw-cirv-left-distributes lw-cirv-fold-constants lw-cirv-times-negative lw-cirv-negative-times lw-cirv-zero-times lw-cirv-minus-one lw-cirv-double-negative lw-cirv-add-cancel lw-cirv-double lw-cirv-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
