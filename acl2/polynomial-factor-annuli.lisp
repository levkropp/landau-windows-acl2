(in-package "ACL2")

(include-book "polynomial-factor-masses")

; Actual factor values and sampled product paths satisfy the computed annuli.

(local (defthm lw-pva-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pva-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pva-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pva-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pva-times-negative (a b) (b a)))
                 :in-theory (disable lw-pva-times-negative)))))

(local (defthm lw-pva-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pva-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pva-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pva-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pva-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pva-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pva-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pva-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pva-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pva-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pva-left-commutes)))))
(local (defthm lw-pva-product-norm-lower
 (implies (and (lw-complexp a) (lw-complexp b)
               (rationalp lower-left) (< 0 lower-left)
               (rationalp lower-right) (< 0 lower-right)
               (<= (* lower-left lower-left) (lw-complex-norm-square a))
               (<= (* lower-right lower-right) (lw-complex-norm-square b)))
  (<= (* lower-left lower-right lower-left lower-right)
      (lw-complex-norm-square (lw-complex-mul a b))))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-valid (point a))
        (:instance lw-complex-norm-square-valid (point b))
        (:instance lw-pva-multiply-order
          (a (* lower-left lower-left)) (b (lw-complex-norm-square a))
          (factor (lw-complex-norm-square b)))
        (:instance lw-pva-multiply-order
          (a (* lower-right lower-right)) (b (lw-complex-norm-square b))
          (factor (* lower-left lower-left))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-norm-square-product lw-pva-left-commutes lw-pva-left-distributes lw-pva-fold-constants lw-pva-times-negative lw-pva-negative-times lw-pva-zero-times lw-pva-minus-one lw-pva-double-negative lw-pva-add-cancel lw-pva-double lw-pva-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t)) :rule-classes nil))


(local (defthm lw-pva-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pva-left-commutes lw-pva-left-distributes lw-pva-fold-constants lw-pva-times-negative lw-pva-negative-times lw-pva-zero-times lw-pva-minus-one lw-pva-double-negative lw-pva-add-cancel lw-pva-double lw-pva-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-factor-value-upper
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading) (lw-unit-square-pointp point))
  (lw-complex-diskp (lw-polynomial-linear-factor-value roots leading point)
                    (lw-polynomial-factor-upper roots leading)))
 :hints (("Goal" :induct (lw-polynomial-linear-factor-value roots leading point)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-linear-factor-value) lw-polynomial-linear-factor-value lw-polynomial-factor-upper lw-unit-square-roots-awayp endp lw-pva-left-commutes lw-pva-left-distributes lw-pva-fold-constants lw-pva-times-negative lw-pva-negative-times lw-pva-zero-times lw-pva-minus-one lw-pva-double-negative lw-pva-add-cancel lw-pva-double lw-pva-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-l1-bound (point leading))
                  (:instance lw-unit-square-root-cap-bound (root (car roots)))
                  (:instance lw-complex-mul-disk
                    (left (lw-complex-sub point (car roots))) (radius (lw-unit-square-root-cap (car roots)))
                    (right (lw-polynomial-linear-factor-value (cdr roots) leading point))
                    (other-radius (lw-polynomial-factor-upper (cdr roots) leading))))
            :do-not-induct t))))

(defthm lw-polynomial-factor-value-lower
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading)
               (not (equal leading (cons 0 0))) (lw-unit-square-pointp point))
  (<= (* (lw-polynomial-factor-lower roots leading) (lw-polynomial-factor-lower roots leading))
      (lw-complex-norm-square (lw-polynomial-linear-factor-value roots leading point))))
 :hints (("Goal" :induct (lw-polynomial-linear-factor-value roots leading point)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-linear-factor-value) lw-polynomial-linear-factor-value lw-polynomial-factor-lower lw-unit-square-roots-awayp lw-unit-square-roots-away-data lw-polynomial-linear-factor-value-rational lw-complex-ring-rational lw-pva-point-type endp lw-pva-left-commutes lw-pva-left-distributes lw-pva-fold-constants lw-pva-times-negative lw-pva-negative-times lw-pva-zero-times lw-pva-minus-one lw-pva-double-negative lw-pva-add-cancel lw-pva-double lw-pva-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-nonzero-lower-valid (point leading))
                  (:instance lw-unit-square-root-gap-data (root (car roots)))
                  (:instance lw-unit-square-distance-lower (root (car roots)))
                  (:instance lw-polynomial-factor-lower-data (roots (cdr roots)))
                  (:instance lw-pva-product-norm-lower
                    (a (lw-complex-sub point (car roots)))
                    (b (lw-polynomial-linear-factor-value (cdr roots) leading point))
                    (lower-left (lw-unit-square-root-gap (car roots)))
                    (lower-right (lw-polynomial-factor-lower (cdr roots) leading))))
            :do-not-induct t))))

(defthm lw-polynomial-factor-path-annulus
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading)
               (not (equal leading (cons 0 0))) (lw-ray-unit-square-pointsp points))
  (lw-ray-annulus-pointsp (lw-polynomial-factor-path-values roots leading points)
                          (lw-polynomial-factor-lower roots leading)
                          (lw-polynomial-factor-upper roots leading)))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values roots leading points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-ray-annulus-pointsp lw-ray-unit-square-pointsp lw-polynomial-factor-value-upper lw-polynomial-factor-value-lower endp lw-pva-left-commutes lw-pva-left-distributes lw-pva-fold-constants lw-pva-times-negative lw-pva-negative-times lw-pva-zero-times lw-pva-minus-one lw-pva-double-negative lw-pva-add-cancel lw-pva-double lw-pva-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
