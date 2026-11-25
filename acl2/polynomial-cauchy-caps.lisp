; A computable finite Cauchy check certifies all coefficients at once.
(in-package "ACL2")
(include-book "polynomial-quadratic-bounds")
(include-book "complex-disk-gap")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner
                 lw-polynomial-add-constant lw-polynomial-multiply-coefficients)))
(local (in-theory (disable lw-polynomial-coefficient-caps lw-polynomial-cap-index
 lw-complex-coefficient-at lw-complex-norm-square lw-disk-gap-error
 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-orbit-rotation)))
(local (defthm lw-pcc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcc-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcc-times-negative)))))

(local (defthm lw-pcc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcc-left-commutes)))))

(local (defthm lw-pcc-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-polynomial-cap-test-error (coefficients cap)
 (if (lw-polynomial-coefficient-caps coefficients cap) 1
  (lw-disk-gap-error
   (lw-complex-norm-square (nth (lw-polynomial-cap-index coefficients cap) coefficients)) cap)))

(local (in-theory (disable lw-polynomial-cap-test-error)))

(local (defthm lw-pcc-failed-test-data
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp cap) (<= 0 cap)
  (not (lw-polynomial-coefficient-caps coefficients cap)))
 (and (natp (lw-polynomial-cap-index coefficients cap)) (< (lw-polynomial-cap-index coefficients cap) (len coefficients)) (lw-complexp (nth (lw-polynomial-cap-index coefficients cap) coefficients))
      (rationalp (lw-polynomial-cap-test-error coefficients cap)) (< 0 (lw-polynomial-cap-test-error coefficients cap))
      (not (lw-complex-diskp (nth (lw-polynomial-cap-index coefficients cap) coefficients) (+ cap (lw-polynomial-cap-test-error coefficients cap))))))
 :hints (("Goal"
 :use (lw-polynomial-cap-index-data
       (:instance lw-complex-coefficient-at-rational (target (lw-polynomial-cap-index coefficients cap)) (offset 0))
       (:instance lw-complex-coefficient-at-nth (target (lw-polynomial-cap-index coefficients cap)) (offset 0))
       (:instance lw-complex-disk-gap-excludes (point (nth (lw-polynomial-cap-index coefficients cap) coefficients)) (radius cap)))
 :in-theory (union-theories
 '(lw-polynomial-cap-test-error lw-pcc-left-commutes lw-pcc-left-distributes lw-pcc-fold-constants lw-pcc-times-negative lw-pcc-negative-times lw-pcc-zero-times lw-pcc-minus-one lw-pcc-double-negative lw-pcc-add-cancel lw-pcc-double lw-pcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-polynomial-cauchy-cap-data
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp cap) (<= 0 cap))
 (and (natp (len coefficients)) (rationalp (lw-polynomial-cap-test-error coefficients cap)) (< 0 (lw-polynomial-cap-test-error coefficients cap))
      (natp (lw-cauchy-coefficient-count coefficients (len coefficients) (lw-polynomial-cap-test-error coefficients cap))) (posp (lw-cauchy-coefficient-count coefficients (len coefficients) (lw-polynomial-cap-test-error coefficients cap)))))
 :hints (("Goal"
 :cases ((lw-polynomial-coefficient-caps coefficients cap))
 :use (lw-pcc-length-natural lw-pcc-failed-test-data
       (:instance lw-cauchy-coefficient-count-natural (degree (len coefficients)) (error (lw-polynomial-cap-test-error coefficients cap))))
 :in-theory (union-theories
 '(lw-polynomial-cap-test-error lw-pcc-left-commutes lw-pcc-left-distributes lw-pcc-fold-constants lw-pcc-times-negative lw-pcc-negative-times lw-pcc-zero-times lw-pcc-minus-one lw-pcc-double-negative lw-pcc-add-cancel lw-pcc-double lw-pcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

(defun lw-polynomial-cauchy-cap-check (coefficients cap)
 (or (lw-polynomial-coefficient-caps coefficients cap)
  (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation (len coefficients)) 0
   (lw-cauchy-coefficient-count coefficients (len coefficients)
    (lw-polynomial-cap-test-error coefficients cap)) cap)))

(local (in-theory (disable lw-polynomial-cauchy-cap-check)))

(defthm lw-polynomial-cauchy-cap-check-sound
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp cap) (<= 0 cap)
  (lw-polynomial-cauchy-cap-check coefficients cap))
 (lw-polynomial-coefficient-caps coefficients cap))
 :hints (("Goal"
 :cases ((lw-polynomial-coefficient-caps coefficients cap))
 :use (lw-pcc-length-natural lw-pcc-failed-test-data
       (:instance lw-cauchy-finite-coefficient-bound (degree (len coefficients)) (target (lw-polynomial-cap-index coefficients cap)) (error (lw-polynomial-cap-test-error coefficients cap))))
 :in-theory (union-theories
 '(lw-polynomial-cauchy-cap-check lw-pcc-left-commutes lw-pcc-left-distributes lw-pcc-fold-constants lw-pcc-times-negative lw-pcc-negative-times lw-pcc-zero-times lw-pcc-minus-one lw-pcc-double-negative lw-pcc-add-cancel lw-pcc-double lw-pcc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp nil :do-not-induct t)))

