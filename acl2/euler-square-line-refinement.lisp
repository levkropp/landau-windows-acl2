; Fixed Euler coarse clearance preserves every square-side crossing sum.
(in-package "ACL2")
(include-book "square-line-clearance")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp lw-complex-polynomial
 lw-complex-positive-halfplanep lw-complex-norm-square lw-polynomial-line-point lw-polynomial-line-value
 lw-polynomial-line-values lw-polynomial-line-crossings lw-polynomial-edge-values lw-unit-mesh lw-unit-parametersp
 lw-euler-square-index-check lw-euler-polygon-index-check lw-euler-positive-square-model
 lw-polynomial-grid-step lw-polynomial-lipschitz-cap lw-square-containsp lw-ray-halfplane-points)))
(local (defthm lw-esl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esl-times-negative (a b) (b a)))
                 :in-theory (disable lw-esl-times-negative)))))

(local (defthm lw-esl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esl-left-commutes)))))
(defun lw-euler-square-line-clearancep (anchor side coarse edge base-target base-error eta index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) t
 (and (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index) eta))
      (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta (+ 1 index) (- remaining 1)))))
(local (in-theory (disable lw-euler-square-line-clearancep)))

(local (defthm lw-esl-line-heads
 (and (equal (consp (lw-polynomial-line-values coefficients left right count index remaining)) (not (zp remaining)))
      (implies (not (zp remaining))
       (and (equal (car (lw-polynomial-line-values coefficients left right count index remaining))
                   (lw-polynomial-line-value coefficients left right count index))
            (equal (cdr (lw-polynomial-line-values coefficients left right count index remaining))
                   (lw-polynomial-line-values coefficients left right count (+ 1 index) (- remaining 1))))))
 :hints (("Goal" :expand ((lw-polynomial-line-values coefficients left right count index remaining))
 :in-theory (union-theories
 '(lw-polynomial-line-values lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-euler-square-line-clearance-as-values
 (iff (lw-ray-row-avoids (lw-polynomial-line-values (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index remaining) eta)
      (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta index remaining))
 :hints (("Goal"
 :induct (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta index remaining)
 :in-theory (union-theories
 '(lw-esl-line-heads lw-euler-square-line-clearancep lw-polynomial-line-values lw-ray-row-avoids lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-square-line-clearance-generated
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4))
 (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta 0 (+ 1 coarse)))
 :hints (("Goal"
 :use ((:instance lw-polynomial-square-boundary-avoids-lines (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (count coarse))
       (:instance lw-euler-square-line-clearance-as-values (index 0) (remaining (+ 1 coarse))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-model-line-halfplane
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp cell) (< cell coarse)
               (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) eta))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (lw-complex-positive-halfplanep (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0)))
 :hints (("Goal"
 :use ((:instance lw-euler-polygon-index-check-data (points (lw-polynomial-square-boundary anchor side coarse)) (step (lw-polynomial-grid-step side coarse)))
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-polynomial-grid-step-data (count coarse))
       (:instance lw-polynomial-square-line-point-contained (count coarse) (index cell))
       (:instance lw-polynomial-square-line-point-contained (count coarse) (index (+ 1 cell)))
       (:instance lw-polynomial-square-line-step-bound (count coarse) (index cell))
       (:instance lw-square-segment-contained (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))))
       (:instance lw-polynomial-square-segment-variation
        (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))) (step (* 2 (lw-polynomial-grid-step side coarse))))
       (:instance lw-euler-positive-square-model-cauchy
        (left-target base-target) (left-error base-error) (right-target target) (right-error error) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)) (offset 0))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side target error)) (point (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter)) (offset 0))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) 0))
        (radius (* 1/4 (+ base-error error))) (other-radius (* 2 (lw-polynomial-grid-step side coarse) (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) 0)))
        (radius (+ (* 1/4 (+ base-error error)) (* 2 (lw-polynomial-grid-step side coarse) (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side))))) (cap eta))
       (:instance lw-complex-disk-norm-square (point (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (radius eta))
       (:instance lw-complex-disk-positive-halfplane (anchor (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (point (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-complex-segment (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameter) 0)) (radius eta)))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-square-containsp lw-polynomial-line-value lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-square-model-edge-values-halfplane
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp cell) (< cell coarse)
               (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) eta))
               (lw-unit-parametersp parameters)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (lw-ray-halfplane-points (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-edge-values (lw-euler-positive-square-model anchor side target error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameters)))
 :hints (("Goal" :induct (lw-polynomial-edge-values (lw-euler-positive-square-model anchor side target error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) parameters)
 :in-theory (union-theories
 '(lw-polynomial-edge-values lw-unit-parametersp lw-ray-halfplane-points endp lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-square-model-line-halfplane (parameter (car parameters))))
   :do-not-induct t))))

(local (defthm lw-esl-line-values-consp
 (equal (consp (lw-polynomial-line-values coefficients left right count index remaining))
        (not (zp remaining)))
 :hints (("Goal" :expand ((lw-polynomial-line-values coefficients left right count index remaining))
 :in-theory (union-theories
 '(lw-polynomial-line-values lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-esl-natural-product
 (implies (and (natp a) (natp b)) (natp (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-square-model-refined-block-index
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (natp cell) (< cell coarse)
               (not (lw-complex-diskp (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) eta)) (posp factor)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (equal
 (lw-polynomial-line-crossings (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (* coarse factor) (* cell factor) factor)
 (lw-ray-crossing
  (lw-polynomial-line-value (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)
  (lw-polynomial-line-value (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)))))
 :hints (("Goal"
 :use ((:instance lw-euler-square-model-edge-values-halfplane
        (parameters (lw-unit-mesh factor 0 (+ 1 factor))))
       (:instance lw-unit-mesh-data (count factor) (index 0) (remaining (+ 1 factor)))
       (:instance lw-polynomial-square-line-point-contained (count coarse) (index cell))
       (:instance lw-polynomial-square-line-point-contained (count coarse) (index (+ 1 cell)))
       (:instance lw-polynomial-line-refinement-values
        (coefficients (lw-euler-positive-square-model anchor side target error)) (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge)) (index 0) (remaining (+ 1 factor)))
       (:instance lw-polynomial-line-values-index
        (coefficients (lw-euler-positive-square-model anchor side target error)) (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge)) (count (* coarse factor)) (index (* cell factor)) (remaining factor))
       (:instance lw-polynomial-line-values-as-mesh
        (coefficients (lw-euler-positive-square-model anchor side target error)) (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))) (count factor) (index 0) (remaining (+ 1 factor)))
       (:instance lw-polynomial-line-values-endpoints
        (coefficients (lw-euler-positive-square-model anchor side target error)) (left (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (right (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell))) (count factor))
       (:instance lw-ray-halfplane-row-index
        (h (lw-polynomial-line-value (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell)) (points (lw-polynomial-line-values (lw-euler-positive-square-model anchor side target error) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse cell) (lw-polynomial-line-point (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse (+ 1 cell)) factor 0 (+ 1 factor)))))
 :in-theory (union-theories
 '(lw-esl-line-values-consp lw-polynomial-square-edge-left lw-polynomial-square-edge-right lw-complexp lw-polynomial-line-value lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-square-containsp lw-esl-natural-product lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-esl-zero-crossings
 (equal (lw-polynomial-line-crossings coefficients left right count index 0) 0)
 :hints (("Goal" :in-theory (union-theories
 '(lw-polynomial-line-crossings lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-esl-crossings-step
 (implies (not (zp remaining))
 (equal (lw-polynomial-line-crossings coefficients left right count index remaining)
 (+ (lw-ray-crossing (lw-polynomial-line-value coefficients left right count index)
                    (lw-polynomial-line-value coefficients left right count (+ 1 index)))
    (lw-polynomial-line-crossings coefficients left right count (+ 1 index) (- remaining 1)))))
 :hints (("Goal" :expand ((lw-polynomial-line-crossings coefficients left right count index remaining))
 :in-theory (union-theories
 '(lw-polynomial-line-crossings lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(defthm lw-euler-square-model-line-refinement-index
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp edge) (< edge 4) (posp factor)
               (natp index) (natp remaining) (<= (+ index remaining) coarse)
               (lw-euler-square-line-clearancep anchor side coarse edge base-target base-error eta index (+ 1 remaining))
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (equal
 (lw-polynomial-line-crossings (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) (* coarse factor) (* index factor) (* remaining factor))
 (lw-polynomial-line-crossings (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index remaining)))
 :hints (("Goal"
 :induct (lw-polynomial-line-crossings (lw-euler-positive-square-model anchor side target error) (lw-polynomial-square-edge-left anchor side edge) (lw-polynomial-square-edge-right anchor side edge) coarse index remaining)
 :in-theory (union-theories
 '((:induction lw-polynomial-line-crossings) lw-euler-square-line-clearancep lw-esl-natural-product lw-esl-zero-crossings lw-polynomial-line-crossings-integer fold-consts-in-+ lw-esl-left-commutes lw-esl-left-distributes lw-esl-fold-constants lw-esl-times-negative lw-esl-negative-times lw-esl-zero-times lw-esl-minus-one lw-esl-double-negative lw-esl-add-cancel lw-esl-double lw-esl-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-esl-natural-product (a (- remaining 1)) (b factor))
         (:instance lw-polynomial-line-crossings-split
          (coefficients (lw-euler-positive-square-model anchor side target error)) (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge)) (count (* coarse factor))
          (index (* index factor)) (prefix factor) (suffix (* (- remaining 1) factor)))
         (:instance lw-euler-square-model-refined-block-index (cell index))
         (:instance lw-esl-crossings-step (coefficients (lw-euler-positive-square-model anchor side target error)) (left (lw-polynomial-square-edge-left anchor side edge)) (right (lw-polynomial-square-edge-right anchor side edge)) (count coarse)))
   :do-not-induct t))))

