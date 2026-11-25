(in-package "ACL2")

(include-book "polynomial-square-accurate-counts")
(include-book "euler-model-pole-candidates")

; Fine Euler and factorization requests vary independently at one fixed native count.

(local (defthm lw-eaf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eaf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eaf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eaf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eaf-times-negative (a b) (b a)))
                 :in-theory (disable lw-eaf-times-negative)))))

(local (defthm lw-eaf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eaf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eaf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eaf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eaf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eaf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eaf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-eaf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eaf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-eaf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-eaf-left-commutes)))))

(defun lw-euler-model-factor-request (anchor side coarse target error eta tolerance)
 (lw-polynomial-square-normalized-request
  (lw-euler-positive-square-model anchor side target error) anchor side
  (lw-euler-model-square-count anchor side coarse target error eta) tolerance))
(defun lw-euler-model-accurate-roots (anchor side coarse target error eta tolerance)
 (lw-polynomial-square-accurate-normalized-roots
  (lw-euler-positive-square-model anchor side target error) anchor side
  (lw-euler-model-square-count anchor side coarse target error eta) tolerance))
(defun lw-euler-model-accurate-inside-roots (anchor side coarse target error eta tolerance)
 (lw-unit-square-inside-roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)))

(defthm lw-euler-model-factor-request-data
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (and (rationalp (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (< 0 (lw-euler-model-factor-request anchor side coarse target error eta tolerance)) (<= (lw-euler-model-factor-request anchor side coarse target error eta tolerance) tolerance)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-normalized-request-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-factor-request lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-accurate-factor-count
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (equal (lw-unit-square-factor-count (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data
        lw-euler-model-square-boundary-check lw-euler-model-square-grid-index
        (:instance lw-polynomial-square-accurate-normalized-count (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-roots lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-accurate-roots-data
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance))
  (and (lw-ray-pointsp (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)) (lw-unit-square-roots-awayp (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))
       (lw-ray-pointsp (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (lw-unit-square-open-rootsp (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance))))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-accurate-normalized-data (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-unit-square-inside-roots-valid (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)))
        (:instance lw-unit-square-inside-roots-interior (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-roots lw-euler-model-accurate-inside-roots lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-accurate-inside-count
 (implies (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance))
  (and (equal (len (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error))
       (<= (len (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (len (lw-polynomial-without-leading (lw-polynomial-trim (lw-euler-positive-square-model anchor side base-target base-error)))))))
 :hints (("Goal"
  :use (lw-euler-model-accurate-factor-count lw-euler-square-polynomial-budget-data
        (:instance lw-euler-native-square-index-nonnegative (value-error base-error))
        (:instance lw-unit-square-inside-roots-length (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-inside-roots lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-model-accurate-disk-approximation
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (lw-complexp point) (lw-complex-diskp point 2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side) point 0)
    (lw-polynomial-linear-factor-value (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance) (lw-polynomial-leading (lw-polynomial-trim (lw-polynomial-square-normalize (lw-euler-positive-square-model anchor side target error) anchor side))) point))
   (lw-euler-model-factor-request anchor side coarse target error eta tolerance)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-accurate-normalized-approximation (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-roots lw-euler-model-factor-request lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-eaf-selected-member
 (implies (member-equal root (lw-unit-square-inside-roots roots)) (member-equal root roots))
 :hints (("Goal" :induct (lw-unit-square-inside-roots roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-inside-roots) lw-unit-square-inside-roots member-equal endp lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-eaf-open-member
 (implies (and (lw-unit-square-open-rootsp roots) (member-equal root roots))
  (and (lw-complexp root) (< -1 (car root)) (< (car root) 1) (< -1 (cdr root)) (< (cdr root) 1)))
 :hints (("Goal" :induct (lw-unit-square-open-rootsp roots)
  :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-open-rootsp) lw-unit-square-open-rootsp member-equal endp lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-eaf-open-disk
 (implies (and (lw-complexp root) (< -1 (car root)) (< (car root) 1) (< -1 (cdr root)) (< (cdr root) 1))
  (lw-complex-diskp root 2))
 :hints (("Goal" :nonlinearp t
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-diskp lw-diskp lw-complexp lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-euler-model-accurate-root-data
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (member-equal root (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
  (and (lw-complexp root) (lw-complex-diskp root 2) (member-equal root (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance))
       (lw-square-containsp anchor side (lw-polynomial-square-forward anchor side root))))
 :hints (("Goal"
  :use (lw-euler-model-accurate-roots-data lw-euler-square-polynomial-budget-data
        (:instance lw-eaf-selected-member (roots (lw-euler-model-accurate-roots anchor side coarse target error eta tolerance)))
        (:instance lw-eaf-open-member (roots (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)))
        lw-eaf-open-disk lw-square-forward-root-interior)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-model-accurate-inside-roots lw-square-containsp lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-eaf-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-eaf-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b))) :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-model-accurate-root-value
 (implies (and (and (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp error) (< 0 error) (<= error eta)) (rationalp tolerance) (< 0 tolerance)) (member-equal root (lw-euler-model-accurate-inside-roots anchor side coarse target error eta tolerance)) (rationalp value-error) (< 0 value-error))
  (lw-complex-diskp (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side root)) (cdr (lw-polynomial-square-forward anchor side root)) value-error) (+ tolerance (+ (* 1/4 error) (* 1/4 value-error)))))
 :hints (("Goal"
  :use (lw-euler-model-accurate-root-data lw-euler-model-factor-request-data
        lw-euler-square-polynomial-budget-data lw-euler-model-square-count-data lw-euler-model-square-boundary-check
        (:instance lw-polynomial-square-accurate-physical-root-residual (coefficients (lw-euler-positive-square-model anchor side target error)) (coarse (lw-euler-model-square-count anchor side coarse target error eta)))
        (:instance lw-euler-positive-square-model-comparison (point (lw-polynomial-square-forward anchor side root)))
        (:instance lw-positive-square-point-data (point (lw-polynomial-square-forward anchor side root)))
        (:instance lw-complex-euler-continuation-value-rational (rate (car (lw-polynomial-square-forward anchor side root))) (height (cdr (lw-polynomial-square-forward anchor side root))) (error value-error))
        (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side root) 0)) (right (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side root)) (cdr (lw-polynomial-square-forward anchor side root)) value-error)) (radius (+ (* 1/4 error) (* 1/4 value-error))))
        (:instance lw-complex-difference-triangle (left (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side root)) (cdr (lw-polynomial-square-forward anchor side root)) value-error)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-forward anchor side root) 0)) (right (cons 0 0)) (radius (+ (* 1/4 error) (* 1/4 value-error))) (other-radius (lw-euler-model-factor-request anchor side coarse target error eta tolerance)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (car (lw-polynomial-square-forward anchor side root)) (cdr (lw-polynomial-square-forward anchor side root)) value-error)) (radius (+ (lw-euler-model-factor-request anchor side coarse target error eta tolerance) (+ (* 1/4 error) (* 1/4 value-error)))) (cap (+ tolerance (+ (* 1/4 error) (* 1/4 value-error))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-euler-model-accurate-roots lw-euler-model-factor-request lw-complex-sub-zero lw-complex-polynomial-rational lw-eaf-product-rational lw-eaf-sum-rational (:executable-counterpart lw-complexp) lw-eaf-left-commutes lw-eaf-left-distributes lw-eaf-fold-constants lw-eaf-times-negative lw-eaf-negative-times lw-eaf-zero-times lw-eaf-minus-one lw-eaf-double-negative lw-eaf-add-cancel lw-eaf-double lw-eaf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
