(in-package "ACL2")

(include-book "euler-base-boundary-margin")

; A fixed collar separates every selected factor from the square boundary.

(local (defthm lw-irc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-irc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-irc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-irc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-irc-times-negative (a b) (b a)))
                 :in-theory (disable lw-irc-times-negative)))))

(local (defthm lw-irc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-irc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-irc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-irc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-irc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-irc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-irc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-irc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-irc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-irc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-irc-left-commutes)))))

(local (defthm lw-irc-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-irc-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(defun lw-euler-interior-root-clearance (anchor side base-target base-error eta)
 (* 1/8 eta (/ (+ 1 (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) 2)))))

(local (defthm lw-irc-scalar-budget
 (implies (and (rationalp mass) (<= 0 mass) (rationalp eta) (< 0 eta))
  (let ((clearance (* 1/8 eta (/ (+ 1 mass)))))
   (and (rationalp clearance) (< 0 clearance) (<= (* clearance mass) (* 1/8 eta)))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value (+ 1 mass)))
        (:instance lw-irc-positive-product (a (* 1/8 eta)) (b (/ (+ 1 mass))))
        (:instance lw-irc-inverse-factor (divisor (+ 1 mass)) (coefficient (* 1/8 eta)))
        (:instance lw-irc-multiply-order (a mass) (b (+ 1 mass)) (factor (* 1/8 eta (/ (+ 1 mass))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-irc-product-rational lw-irc-inverse-rational lw-irc-left-commutes lw-irc-left-distributes lw-irc-fold-constants lw-irc-times-negative lw-irc-negative-times lw-irc-zero-times lw-irc-minus-one lw-irc-double-negative lw-irc-add-cancel lw-irc-double lw-irc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))))

(defthm lw-euler-interior-root-clearance-data
 (implies (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta)
  (and (rationalp (lw-euler-interior-root-clearance anchor side base-target base-error eta)) (< 0 (lw-euler-interior-root-clearance anchor side base-target base-error eta)) (<= (* (lw-euler-interior-root-clearance anchor side base-target base-error eta) (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) 2)) (* 1/8 eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side base-target base-error)))
        (:instance lw-polynomial-lipschitz-cap-data (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side)) (bound 2))
        (:instance lw-irc-scalar-budget (mass (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) 2))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-interior-root-clearance lw-irc-left-commutes lw-irc-left-distributes lw-irc-fold-constants lw-irc-times-negative lw-irc-negative-times lw-irc-zero-times lw-irc-minus-one lw-irc-double-negative lw-irc-add-cancel lw-irc-double lw-irc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-base-model-at-selected-root
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (<= tolerance (* 1/8 eta)) (member-equal root (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
  (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) root 0) (* 5/8 eta)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-accurate-root-data lw-euler-model-factor-request-data
        lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-accurate-physical-root-residual (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-polynomial-square-normalize-evaluation (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point root))
        (:instance lw-euler-positive-square-model-cauchy (point (lw-polynomial-square-forward anchor side root))
         (left-target base-target) (left-error base-error) (right-target target) (right-error error))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-polynomial-square-forward anchor side root)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side target error)) (point (lw-polynomial-square-forward anchor side root)) (offset 0))
        (:instance lw-polynomial-square-map-data (point root))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side root) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-forward anchor side root) 0)) (radius (* 1/4 (+ base-error error))))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-forward anchor side root) 0)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side root) 0)) (right (cons 0 0)) (radius (* 1/4 (+ base-error error))) (other-radius (lw-euler-model-factor-request anchor side coarse target error eta tolerance)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-forward anchor side root) 0)) (radius (+ (* 1/4 (+ base-error error)) (lw-euler-model-factor-request anchor side coarse target error eta tolerance))) (cap (* 5/8 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-roots lw-euler-model-factor-request lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-irc-left-commutes lw-irc-left-distributes lw-irc-fold-constants lw-irc-times-negative lw-irc-negative-times lw-irc-zero-times lw-irc-minus-one lw-irc-double-negative lw-irc-add-cancel lw-irc-double lw-irc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-selected-root-boundary-distance
 (implies (and (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (<= tolerance (* 1/8 eta)) (member-equal root (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance))) (lw-unit-square-pointp point))
  (not (lw-complex-diskp (lw-complex-sub point root) (lw-euler-interior-root-clearance anchor side base-target base-error eta))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-interior-root-clearance-data
        lw-euler-base-normalized-boundary-margin lw-euler-base-model-at-selected-root
        lw-unit-square-point-annulus lw-unit-square-point-coordinates lw-euler-model-accurate-root-data
        (:instance lw-polynomial-square-normalize-valid (coefficients (lw-euler-positive-square-model anchor side base-target base-error)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side)) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side)) (point root) (offset 0))
        (:instance lw-complex-polynomial-lipschitz
         (coefficients (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side)) (left point) (right root) (bound 2) (step (lw-euler-interior-root-clearance anchor side base-target base-error eta)))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) point 0)) (middle (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) root 0)) (right (cons 0 0))
         (radius (* (lw-euler-interior-root-clearance anchor side base-target base-error eta) (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) 2))) (other-radius (* 5/8 eta)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) point 0)) (radius (+ (* (lw-euler-interior-root-clearance anchor side base-target base-error eta) (lw-polynomial-lipschitz-cap (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side base-target base-error) anchor side) 2)) (* 5/8 eta))) (cap (* 3/4 eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-irc-left-commutes lw-irc-left-distributes lw-irc-fold-constants lw-irc-times-negative lw-irc-negative-times lw-irc-zero-times lw-irc-minus-one lw-irc-double-negative lw-irc-add-cancel lw-irc-double lw-irc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
