(in-package "ACL2")

(include-book "polynomial-accurate-counts")
(include-book "polynomial-square-counts")

; Requested factor accuracy and the same exact count on any checked rational square.

(local (defthm lw-pac-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pac-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pac-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pac-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pac-times-negative (a b) (b a)))
                 :in-theory (disable lw-pac-times-negative)))))

(local (defthm lw-pac-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pac-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pac-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pac-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pac-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pac-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pac-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pac-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pac-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pac-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pac-left-commutes)))))

(defun lw-polynomial-square-normalized-request (coefficients anchor side coarse tolerance)
 (lw-polynomial-square-factor-request (lw-polynomial-square-normalize coefficients anchor side)
  (lw-polynomial-normalization-count coefficients anchor side coarse) tolerance))
(defun lw-polynomial-square-accurate-normalized-roots (coefficients anchor side coarse tolerance)
 (lw-polynomial-square-accurate-roots (lw-polynomial-square-normalize coefficients anchor side)
  (lw-polynomial-normalization-count coefficients anchor side coarse) tolerance))

(defthm lw-polynomial-square-normalized-request-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients anchor side coarse) (rationalp tolerance) (< 0 tolerance)) (and (rationalp (lw-polynomial-square-normalized-request coefficients anchor side coarse tolerance)) (< 0 (lw-polynomial-square-normalized-request coefficients anchor side coarse tolerance)) (<= (lw-polynomial-square-normalized-request coefficients anchor side coarse tolerance) tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-normalization-boundary-check
        (:instance lw-polynomial-square-factor-request-data (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (count (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-normalized-request lw-pac-left-commutes lw-pac-left-distributes lw-pac-fold-constants lw-pac-times-negative lw-pac-negative-times lw-pac-zero-times lw-pac-minus-one lw-pac-double-negative lw-pac-add-cancel lw-pac-double lw-pac-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-normalized-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients anchor side coarse) (rationalp tolerance) (< 0 tolerance)) (and (lw-ray-pointsp (lw-polynomial-square-accurate-normalized-roots coefficients anchor side coarse tolerance)) (lw-unit-square-roots-awayp (lw-polynomial-square-accurate-normalized-roots coefficients anchor side coarse tolerance))))
 :hints (("Goal"
  :use (lw-polynomial-square-normalize-valid lw-polynomial-normalization-count-data lw-polynomial-normalization-boundary-check
        (:instance lw-polynomial-square-accurate-data (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (count (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-square-accurate-away (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (count (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-normalized-roots lw-pac-left-commutes lw-pac-left-distributes lw-pac-fold-constants lw-pac-times-negative lw-pac-negative-times lw-pac-zero-times lw-pac-minus-one lw-pac-double-negative lw-pac-add-cancel lw-pac-double lw-pac-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-normalized-count
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients anchor side coarse) (rationalp tolerance) (< 0 tolerance))
  (equal (lw-unit-square-factor-count (lw-polynomial-square-accurate-normalized-roots coefficients anchor side coarse tolerance))
   (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse))))
 :hints (("Goal"
  :use (lw-polynomial-square-index-normalize lw-polynomial-square-normalize-valid
        lw-polynomial-normalization-count-data lw-polynomial-normalization-boundary-check
        (:instance lw-polynomial-checked-square-accurate-count (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (coarse (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-normalized-roots lw-pac-left-commutes lw-pac-left-distributes lw-pac-fold-constants lw-pac-times-negative lw-pac-negative-times lw-pac-zero-times lw-pac-minus-one lw-pac-double-negative lw-pac-add-cancel lw-pac-double lw-pac-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-normalized-approximation
 (implies (and (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients anchor side coarse) (rationalp tolerance) (< 0 tolerance)) (lw-complexp point) (lw-complex-diskp point 2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial (lw-polynomial-square-normalize coefficients anchor side) point 0)
    (lw-polynomial-linear-factor-value (lw-polynomial-square-accurate-normalized-roots coefficients anchor side coarse tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize coefficients anchor side))) point))
   (lw-polynomial-square-normalized-request coefficients anchor side coarse tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-normalize-valid lw-polynomial-normalization-count-data lw-polynomial-normalization-boundary-check
        (:instance lw-polynomial-square-accurate-disk-approximation (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (count (lw-polynomial-normalization-count coefficients anchor side coarse))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-normalized-roots lw-polynomial-square-normalized-request lw-pac-left-commutes lw-pac-left-distributes lw-pac-fold-constants lw-pac-times-negative lw-pac-negative-times lw-pac-zero-times lw-pac-minus-one lw-pac-double-negative lw-pac-add-cancel lw-pac-double lw-pac-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-physical-root-residual
 (implies (and (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side) (posp coarse)
               (lw-polynomial-square-boundary-check coefficients anchor side coarse) (rationalp tolerance) (< 0 tolerance)) (lw-complexp root) (lw-complex-diskp root 2) (member-equal root (lw-polynomial-square-accurate-normalized-roots coefficients anchor side coarse tolerance)))
  (lw-complex-diskp (lw-complex-polynomial coefficients (lw-polynomial-square-forward anchor side root) 0) (lw-polynomial-square-normalized-request coefficients anchor side coarse tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-normalize-valid lw-polynomial-normalization-count-data lw-polynomial-normalization-boundary-check
        (:instance lw-polynomial-square-accurate-root-residual (coefficients (lw-polynomial-square-normalize coefficients anchor side)) (count (lw-polynomial-normalization-count coefficients anchor side coarse)))
        (:instance lw-polynomial-square-normalize-evaluation (point root)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-normalized-roots lw-polynomial-square-normalized-request lw-pac-left-commutes lw-pac-left-distributes lw-pac-fold-constants lw-pac-times-negative lw-pac-negative-times lw-pac-zero-times lw-pac-minus-one lw-pac-double-negative lw-pac-add-cancel lw-pac-double lw-pac-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
