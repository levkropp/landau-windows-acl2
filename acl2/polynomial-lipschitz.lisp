; A computed two-point variation bound for every finite rational polynomial.
(in-package "ACL2")
(include-book "euler-uniform-derivative-bounds")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
 lw-complex-diskp lw-diskp lw-complex-polynomial lw-complex-coefficientsp lw-polynomial-disk-cap)))
(local (defthm lw-plc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-plc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-plc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-plc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-plc-times-negative (a b) (b a)))
                 :in-theory (disable lw-plc-times-negative)))))

(local (defthm lw-plc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-plc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-plc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-plc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-plc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-plc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-plc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-plc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-plc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-plc-left-commutes)))))
(defun lw-polynomial-lipschitz-cap (coefficients bound)
 (declare (xargs :measure (acl2-count coefficients) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp coefficients) 0
 (+ (lw-polynomial-disk-cap (cdr coefficients) bound)
    (* bound (lw-polynomial-lipschitz-cap (cdr coefficients) bound)))))
(local (in-theory (disable lw-polynomial-lipschitz-cap)))

(defthm lw-polynomial-lipschitz-cap-data
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp bound) (<= 0 bound))
 (and (rationalp (lw-polynomial-lipschitz-cap coefficients bound)) (<= 0 (lw-polynomial-lipschitz-cap coefficients bound))))
 :hints (("Goal" :induct (lw-polynomial-lipschitz-cap coefficients bound)
 :in-theory (union-theories
 '(lw-polynomial-lipschitz-cap lw-complex-coefficientsp endp lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-disk-cap-valid (coefficients (cdr coefficients)) (radius bound))
         (:instance lw-plc-multiply-order (a 0) (b (lw-polynomial-lipschitz-cap (cdr coefficients) bound)) (factor bound)))
 :do-not-induct t)))
 :rule-classes nil)

(local (defthm lw-plc-polynomial-empty
 (implies (endp coefficients) (equal (lw-complex-polynomial coefficients point 0) (cons 0 0)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial endp lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-plc-horner-difference
 (implies (and (lw-complexp constant) (lw-complexp left) (lw-complexp right) (lw-complexp x) (lw-complexp y))
 (equal (lw-complex-sub (lw-complex-add constant (lw-complex-mul left x)) (lw-complex-add constant (lw-complex-mul right y)))
 (lw-complex-add (lw-complex-mul (lw-complex-sub left right) x) (lw-complex-mul right (lw-complex-sub x y)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-polynomial-lipschitz
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp bound) (<= 0 bound)
 (lw-complex-diskp left bound) (lw-complex-diskp right bound)
 (rationalp step) (<= 0 step) (lw-complex-diskp (lw-complex-sub left right) step))
 (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial coefficients left 0) (lw-complex-polynomial coefficients right 0))
 (* step (lw-polynomial-lipschitz-cap coefficients bound))))
 :hints (("Goal" :induct (lw-polynomial-lipschitz-cap coefficients bound)
 :in-theory (union-theories
 '(lw-polynomial-lipschitz-cap lw-complex-coefficientsp lw-plc-polynomial-empty (:executable-counterpart lw-complex-sub) (:executable-counterpart lw-complex-diskp) endp lw-plc-left-commutes lw-plc-left-distributes lw-plc-fold-constants lw-plc-times-negative lw-plc-negative-times lw-plc-zero-times lw-plc-minus-one lw-plc-double-negative lw-plc-add-cancel lw-plc-double lw-plc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-complex-disk-data (point left) (radius bound))
         (:instance lw-complex-disk-data (point right) (radius bound))
         (:instance lw-polynomial-lipschitz-cap-data (coefficients (cdr coefficients)))
         (:instance lw-polynomial-disk-cap-valid (coefficients (cdr coefficients)) (radius bound))
         (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (point left) (offset 0))
         (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (point right) (offset 0))
         (:instance lw-complex-polynomial-horner (point left))
         (:instance lw-complex-polynomial-horner (point right))
         (:instance lw-plc-horner-difference (constant (car coefficients)) (x (lw-complex-polynomial (cdr coefficients) left 0)) (y (lw-complex-polynomial (cdr coefficients) right 0)))
         (:instance lw-complex-polynomial-disk-cap-bound (coefficients (cdr coefficients)) (point left) (radius bound))
         (:instance lw-complex-mul-disk (left (lw-complex-sub left right)) (radius step) (right (lw-complex-polynomial (cdr coefficients) left 0)) (other-radius (lw-polynomial-disk-cap (cdr coefficients) bound)))
         (:instance lw-complex-mul-disk (left right) (radius bound) (right (lw-complex-sub (lw-complex-polynomial (cdr coefficients) left 0) (lw-complex-polynomial (cdr coefficients) right 0))) (other-radius (* step (lw-polynomial-lipschitz-cap (cdr coefficients) bound))))
         (:instance lw-complex-add-disk (left (lw-complex-mul (lw-complex-sub left right) (lw-complex-polynomial (cdr coefficients) left 0))) (radius (* step (lw-polynomial-disk-cap (cdr coefficients) bound))) (right (lw-complex-mul right (lw-complex-sub (lw-complex-polynomial (cdr coefficients) left 0) (lw-complex-polynomial (cdr coefficients) right 0)))) (other-radius (* bound step (lw-polynomial-lipschitz-cap (cdr coefficients) bound)))))
 :do-not-induct t))))

