(in-package "ACL2")

(include-book "polynomial-normalized-clearance")
(include-book "polynomial-root-search")

; Refine by a computed coefficient-based count, using the inherited clearance.

(local (defthm lw-pnt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pnt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pnt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pnt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pnt-times-negative (a b) (b a)))
                 :in-theory (disable lw-pnt-times-negative)))))

(local (defthm lw-pnt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pnt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pnt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pnt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pnt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pnt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pnt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pnt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pnt-left-commutes)))))
(local (defthm lw-pnt-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pnt-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pnt-unit-radius
 (equal (lw-polynomial-grid-radius (cons -1 -1) 2) 7)
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-grid-radius lw-complex-l1 abs lw-pnt-left-commutes lw-pnt-left-distributes lw-pnt-fold-constants lw-pnt-times-negative lw-pnt-negative-times lw-pnt-zero-times lw-pnt-minus-one lw-pnt-double-negative lw-pnt-add-cancel lw-pnt-double lw-pnt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-polynomial-normalization-factor (coefficients anchor side coarse)
 (let ((clearance (lw-polynomial-square-clearance coefficients anchor side coarse)))
  (if (<= clearance 0) 1
   (lw-polynomial-root-count (lw-polynomial-square-normalize coefficients anchor side) (cons -1 -1) 2 clearance))))
(defun lw-polynomial-normalization-count (coefficients anchor side coarse) (* coarse (lw-polynomial-normalization-factor coefficients anchor side coarse)))

(defthm lw-polynomial-normalization-factor-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (posp (lw-polynomial-normalization-factor coefficients anchor side coarse)))
 :hints (("Goal"
  :use (lw-polynomial-square-normalize-valid
        (:instance lw-polynomial-square-clearance-data (count coarse))
        (:instance lw-polynomial-root-count-data (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (anchor (cons -1 -1)) (side 2) (epsilon (lw-polynomial-square-clearance coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-normalization-factor (:executable-counterpart lw-complexp) lw-pnt-left-commutes lw-pnt-left-distributes lw-pnt-fold-constants lw-pnt-times-negative lw-pnt-negative-times lw-pnt-zero-times lw-pnt-minus-one lw-pnt-double-negative lw-pnt-add-cancel lw-pnt-double lw-pnt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-pnt-division-enlarge
 (implies (and (rationalp numerator) (<= 0 numerator)
               (rationalp divisor) (< 0 divisor) (rationalp larger) (<= divisor larger)
               (rationalp bound) (<= 0 bound)
               (<= (* numerator (/ divisor)) bound))
  (<= (* numerator (/ larger)) bound))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pnt-multiply-order (a (* numerator (/ divisor))) (b bound) (factor divisor))
        (:instance lw-pnt-inverse-factor (coefficient numerator))
        (:instance lw-pnt-multiply-order (a divisor) (b larger) (factor bound))
        (:instance lw-positive-division-bound (divisor larger)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pnt-product-rational lw-pnt-inverse-rational lw-pnt-left-commutes lw-pnt-left-distributes lw-pnt-fold-constants lw-pnt-times-negative lw-pnt-negative-times lw-pnt-zero-times lw-pnt-minus-one lw-pnt-double-negative lw-pnt-add-cancel lw-pnt-double lw-pnt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))



(local (defthm lw-pnt-refine-budget
 (implies (and (posp coarse) (posp factor) (rationalp mass) (<= 0 mass)
               (rationalp clearance) (< 0 clearance) (<= (* 4 mass (/ factor)) clearance))
  (and (posp (* coarse factor)) (<= (* 4 mass (/ (* coarse factor))) clearance)))
 :rule-classes nil
 :hints (("Goal"
  :use ((:instance lw-pnt-multiply-order (a 1) (b coarse))
        (:instance lw-pnt-positive-product (a coarse) (b factor))
        (:instance lw-pnt-division-enlarge (numerator (* 4 mass)) (divisor factor) (larger (* coarse factor)) (bound clearance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pnt-product-rational lw-pnt-left-commutes lw-pnt-left-distributes lw-pnt-fold-constants lw-pnt-times-negative lw-pnt-negative-times lw-pnt-zero-times lw-pnt-minus-one lw-pnt-double-negative lw-pnt-add-cancel lw-pnt-double lw-pnt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-polynomial-normalization-count-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (and (posp (lw-polynomial-normalization-count coefficients anchor side coarse)) (<= (* 4 (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize coefficients anchor side) 7) (/ (lw-polynomial-normalization-count coefficients anchor side coarse))) (lw-polynomial-square-clearance coefficients anchor side coarse))))
 :hints (("Goal"
  :use (lw-polynomial-normalization-factor-data lw-polynomial-square-normalize-valid
        (:instance lw-polynomial-square-clearance-data (count coarse))
        (:instance lw-polynomial-root-count-data (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (anchor (cons -1 -1)) (side 2) (epsilon (lw-polynomial-square-clearance coefficients anchor side coarse)))
        (:instance lw-polynomial-lipschitz-cap-data (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (bound 7))
        (:instance lw-pnt-refine-budget (factor (lw-polynomial-normalization-factor coefficients anchor side coarse)) (mass (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize coefficients anchor side) 7)) (clearance (lw-polynomial-square-clearance coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-normalization-factor lw-polynomial-normalization-count lw-polynomial-grid-step lw-pnt-unit-radius (:executable-counterpart lw-complexp) lw-pnt-left-commutes lw-pnt-left-distributes lw-pnt-fold-constants lw-pnt-times-negative lw-pnt-negative-times lw-pnt-zero-times lw-pnt-minus-one lw-pnt-double-negative lw-pnt-add-cancel lw-pnt-double lw-pnt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-normalization-edge-cap-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
               (posp coarse) (lw-polynomial-square-boundary-check coefficients anchor side coarse))
  (and (rationalp (lw-polynomial-edge-cap (lw-polynomial-square-normalize coefficients anchor side) 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse))))) (<= 0 (lw-polynomial-edge-cap (lw-polynomial-square-normalize coefficients anchor side) 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse))))) (< (lw-polynomial-edge-cap (lw-polynomial-square-normalize coefficients anchor side) 7 (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse)))) (lw-polynomial-square-clearance coefficients anchor side coarse))))
 :hints (("Goal"
  :use (lw-polynomial-normalization-count-data lw-polynomial-square-normalize-valid
        (:instance lw-polynomial-square-clearance-data (count coarse))
        (:instance lw-polynomial-lipschitz-cap-data (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (bound 7))
        (:instance lw-reciprocal-positive (value (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-pnt-multiply-order (a 0) (b (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize coefficients anchor side) 7)) (factor (* 2 (/ (lw-polynomial-normalization-count coefficients anchor side coarse))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-edge-cap lw-pnt-product-rational lw-pnt-inverse-rational lw-pnt-left-commutes lw-pnt-left-distributes lw-pnt-fold-constants lw-pnt-times-negative lw-pnt-negative-times lw-pnt-zero-times lw-pnt-minus-one lw-pnt-double-negative lw-pnt-add-cancel lw-pnt-double lw-pnt-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
