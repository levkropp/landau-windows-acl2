(in-package "ACL2")

(include-book "polynomial-capped-coefficients")
(include-book "polynomial-cauchy-caps")
(include-book "polynomial-derivatives")

; The first coefficient of the local difference is the scaled derivative difference.

(local (defthm lw-ldc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ldc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ldc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ldc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ldc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ldc-times-negative)))))

(local (defthm lw-ldc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ldc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ldc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ldc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ldc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ldc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ldc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ldc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ldc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ldc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ldc-left-commutes)))))

(local (defthm lw-ldc-natural-length
 (natp (len coefficients)) :rule-classes (:rewrite :type-prescription)))

(defun lw-polynomial-local-difference (left right center radius)
 (lw-polynomial-disk-difference
  (lw-polynomial-affine left center (cons 1 0)) (lw-polynomial-affine right center (cons 1 0))
  radius (+ (len left) (len right))))

(defthm lw-polynomial-local-difference-valid
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (lw-complexp center) (rationalp radius)) (lw-complex-coefficientsp (lw-polynomial-local-difference left right center radius)))
 :hints (("Goal"
  :use ((:instance lw-polynomial-affine-valid (coefficients left) (slope (cons 1 0)))
        (:instance lw-polynomial-affine-valid (coefficients right) (slope (cons 1 0)))
        (:instance lw-polynomial-disk-difference-valid (left (lw-polynomial-affine left center (cons 1 0))) (right (lw-polynomial-affine right center (cons 1 0))) (count (+ (len left) (len right)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-local-difference lw-ldc-natural-length (:executable-counterpart lw-complexp) lw-ldc-left-commutes lw-ldc-left-distributes lw-ldc-fold-constants lw-ldc-times-negative lw-ldc-negative-times lw-ldc-zero-times lw-ldc-minus-one lw-ldc-double-negative lw-ldc-add-cancel lw-ldc-double lw-ldc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-local-difference-evaluation
 (implies (and (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (lw-complexp center) (rationalp radius)) (lw-complexp point))
  (equal (lw-complex-polynomial (lw-polynomial-local-difference left right center radius) point 0)
         (lw-complex-sub (lw-complex-polynomial left (lw-complex-add center (lw-complex-scale radius point)) 0)
                         (lw-complex-polynomial right (lw-complex-add center (lw-complex-scale radius point)) 0))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-affine-valid (coefficients left) (slope (cons 1 0)))
        (:instance lw-polynomial-affine-valid (coefficients right) (slope (cons 1 0)))
        (:instance lw-polynomial-affine-evaluation (coefficients left) (slope (cons 1 0)) (point (lw-complex-scale radius point)))
        (:instance lw-polynomial-affine-evaluation (coefficients right) (slope (cons 1 0)) (point (lw-complex-scale radius point)))
        (:instance lw-polynomial-disk-difference-evaluation (left (lw-polynomial-affine left center (cons 1 0))) (right (lw-polynomial-affine right center (cons 1 0))) (count (+ (len left) (len right)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-local-difference lw-ldc-natural-length lw-complex-mul-one lw-complex-scale-rational (:executable-counterpart lw-complexp) lw-ldc-left-commutes lw-ldc-left-distributes lw-ldc-fold-constants lw-ldc-times-negative lw-ldc-negative-times lw-ldc-zero-times lw-ldc-minus-one lw-ldc-double-negative lw-ldc-add-cancel lw-ldc-double lw-ldc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ldc-scale-difference
 (implies (and (rationalp radius) (lw-complexp left) (lw-complexp right))
  (equal (lw-complex-sub (lw-complex-scale radius left) (lw-complex-scale radius right))
         (lw-complex-scale radius (lw-complex-sub left right))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-scale lw-complex-sub lw-ldc-left-commutes lw-ldc-left-distributes lw-ldc-fold-constants lw-ldc-times-negative lw-ldc-negative-times lw-ldc-zero-times lw-ldc-minus-one lw-ldc-double-negative lw-ldc-add-cancel lw-ldc-double lw-ldc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-local-difference-derivative
 (implies (and (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (lw-complexp center) (rationalp radius)) (rationalp cap) (<= 0 cap)
               (lw-polynomial-cauchy-cap-check (lw-polynomial-local-difference left right center radius) cap))
  (lw-complex-diskp (lw-complex-scale radius (lw-complex-sub (lw-complex-polynomial-derivative left center) (lw-complex-polynomial-derivative right center))) cap))
 :hints (("Goal"
  :use (lw-polynomial-local-difference-valid
        (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-polynomial-local-difference left right center radius)))
        (:instance lw-polynomial-affine-valid (coefficients left) (slope (cons 1 0)))
        (:instance lw-polynomial-affine-valid (coefficients right) (slope (cons 1 0)))
        (:instance lw-polynomial-disk-difference-capped-coefficient (left (lw-polynomial-affine left center (cons 1 0))) (right (lw-polynomial-affine right center (cons 1 0))) (count (+ (len left) (len right))) (index 1))
        (:instance lw-polynomial-rescale-coefficient (coefficients (lw-polynomial-affine left center (cons 1 0))) (factor radius) (target 1) (offset 0))
        (:instance lw-polynomial-rescale-coefficient (coefficients (lw-polynomial-affine right center (cons 1 0))) (factor radius) (target 1) (offset 0))
        (:instance lw-polynomial-affine-linear-coefficient (coefficients left) (slope (cons 1 0)))
        (:instance lw-polynomial-affine-linear-coefficient (coefficients right) (slope (cons 1 0)))
        (:instance lw-complex-polynomial-derivative-rational (coefficients left) (point center))
        (:instance lw-complex-polynomial-derivative-rational (coefficients right) (point center)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-local-difference lw-ldc-natural-length lw-ldc-scale-difference lw-complex-mul-one lw-rational-power (:executable-counterpart lw-complexp) lw-ldc-left-commutes lw-ldc-left-distributes lw-ldc-fold-constants lw-ldc-times-negative lw-ldc-negative-times lw-ldc-zero-times lw-ldc-minus-one lw-ldc-double-negative lw-ldc-add-cancel lw-ldc-double lw-ldc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
