; Every checked polynomial edge retains its index under arbitrary finite sampling.
(in-package "ACL2")
(include-book "complex-segments")
(include-book "polynomial-lipschitz")
(include-book "polygon-refinement")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp lw-diskp
 lw-complex-segment lw-complex-polynomial lw-complex-coefficientsp lw-polynomial-lipschitz-cap
 lw-complex-positive-halfplanep lw-ray-path-index lw-ray-path-last lw-ray-crossing lw-ray-halfplane-points)))
(local (defthm lw-per-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-per-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-per-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-per-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-per-times-negative (a b) (b a)))
                 :in-theory (disable lw-per-times-negative)))))

(local (defthm lw-per-zero-times (equal (* 0 a) 0)))

(local (defthm lw-per-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-per-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-per-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-per-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-per-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-per-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-per-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-per-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-per-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-per-left-commutes)))))
(defun lw-unit-parametersp (parameters)
 (if (endp parameters) (equal parameters nil)
 (and (rationalp (car parameters)) (<= 0 (car parameters)) (<= (car parameters) 1)
      (lw-unit-parametersp (cdr parameters)))))
(defun lw-unit-mesh (count index remaining)
 (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp remaining) nil
 (cons (* index (/ count)) (lw-unit-mesh count (+ 1 index) (- remaining 1)))))
(defun lw-polynomial-edge-values (coefficients left right parameters)
 (declare (xargs :measure (acl2-count parameters) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp parameters) nil
 (cons (lw-complex-polynomial coefficients (lw-complex-segment left right (car parameters)) 0)
       (lw-polynomial-edge-values coefficients left right (cdr parameters)))))
(defun lw-polynomial-edge-cap (coefficients bound radius)
 (* radius (lw-polynomial-lipschitz-cap coefficients bound)))
(defun lw-polynomial-edge-check (coefficients left right bound radius)
 (and (lw-complex-coefficientsp coefficients) (lw-complexp left) (lw-complexp right)
      (rationalp bound) (<= 0 bound) (rationalp radius) (<= 0 radius)
      (lw-complex-diskp left bound) (lw-complex-diskp right bound)
      (lw-complex-diskp (lw-complex-sub right left) radius)
      (< (* (lw-polynomial-edge-cap coefficients bound radius)
            (lw-polynomial-edge-cap coefficients bound radius))
         (lw-complex-norm-square (lw-complex-polynomial coefficients left 0)))))
(defun lw-polynomial-edge-samples (coefficients left right count)
 (lw-polynomial-edge-values coefficients left right (lw-unit-mesh count 1 (nfix (- count 1)))))
(local (in-theory (disable lw-unit-parametersp lw-unit-mesh lw-polynomial-edge-values lw-polynomial-edge-cap lw-polynomial-edge-check lw-polynomial-edge-samples)))

(local (defthm lw-per-zero-difference
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius))
 (lw-complex-diskp (lw-complex-sub point point) radius))
 :hints (("Goal" :nonlinearp t :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-unit-mesh-data
 (implies (and (posp count) (natp index) (natp remaining) (<= (+ index remaining) (+ 1 count)))
 (and (lw-unit-parametersp (lw-unit-mesh count index remaining))
      (equal (len (lw-unit-mesh count index remaining)) remaining)))
 :hints (("Goal" :induct (lw-unit-mesh count index remaining)
 :in-theory (union-theories
 '(lw-unit-mesh lw-unit-parametersp len endp nfix lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-reciprocal-positive (value count))
         (:instance lw-per-multiply-order (a 0) (b index) (factor (/ count)))
         (:instance lw-per-multiply-order (a index) (b count) (factor (/ count)))
         (:instance inverse-of-* (x count))) :do-not-induct t))))

(defthm lw-polynomial-edge-sample-variation
 (implies (and (lw-polynomial-edge-check coefficients left right bound radius)
 (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0)
                  (lw-complex-polynomial coefficients left 0))
  (lw-polynomial-edge-cap coefficients bound radius)))
 :hints (("Goal"
 :use ((:instance lw-per-zero-difference (point left))
       (:instance lw-complex-segment-centered-disk (center left))
       (:instance lw-complex-segment-disk (radius bound))
       (:instance lw-complex-polynomial-lipschitz (left (lw-complex-segment left right parameter)) (right left) (step radius)))
 :in-theory (union-theories
 '(lw-polynomial-edge-check lw-polynomial-edge-cap lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-edge-sample-halfplane
 (implies (and (lw-polynomial-edge-check coefficients left right bound radius)
 (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-complex-positive-halfplanep
  (lw-complex-polynomial coefficients left 0)
  (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0)))
 :hints (("Goal"
 :use (lw-polynomial-edge-sample-variation
       lw-complex-segment-rational
       (:instance lw-complex-polynomial-rational (point left) (offset 0))
       (:instance lw-complex-polynomial-rational (point (lw-complex-segment left right parameter)) (offset 0))
       lw-polynomial-lipschitz-cap-data
       (:instance lw-complex-disk-positive-halfplane
        (anchor (lw-complex-polynomial coefficients left 0))
        (point (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0))
        (radius (lw-polynomial-edge-cap coefficients bound radius))))
 :in-theory (union-theories
 '(lw-polynomial-edge-check lw-polynomial-edge-cap lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-edge-values-halfplane
 (implies (and (lw-polynomial-edge-check coefficients left right bound radius) (lw-unit-parametersp parameters))
 (lw-ray-halfplane-points (lw-complex-polynomial coefficients left 0)
 (lw-polynomial-edge-values coefficients left right parameters)))
 :hints (("Goal" :induct (lw-polynomial-edge-values coefficients left right parameters)
 :in-theory (union-theories
 '(lw-polynomial-edge-values lw-unit-parametersp lw-ray-halfplane-points endp lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-edge-sample-halfplane (parameter (car parameters)))) :do-not-induct t))))

(defthm lw-polynomial-edge-samples-halfplane
 (implies (and (posp count) (lw-polynomial-edge-check coefficients left right bound radius))
 (lw-ray-halfplane-points (lw-complex-polynomial coefficients left 0)
 (lw-polynomial-edge-samples coefficients left right count)))
 :hints (("Goal"
 :use ((:instance lw-unit-mesh-data (index 1) (remaining (- count 1)))
       (:instance lw-polynomial-edge-values-halfplane (parameters (lw-unit-mesh count 1 (- count 1)))))
 :in-theory (union-theories
 '(lw-polynomial-edge-samples nfix lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-edge-refinement-index
 (implies (and (posp count) (lw-polynomial-edge-check coefficients left right bound radius))
 (equal
 (+ (lw-ray-path-index (lw-complex-polynomial coefficients left 0)
                       (lw-polynomial-edge-samples coefficients left right count))
    (lw-ray-crossing (lw-ray-path-last (lw-complex-polynomial coefficients left 0)
                                      (lw-polynomial-edge-samples coefficients left right count))
                     (lw-complex-polynomial coefficients right 0)))
 (lw-ray-crossing (lw-complex-polynomial coefficients left 0) (lw-complex-polynomial coefficients right 0))))
 :hints (("Goal"
 :use (lw-polynomial-edge-samples-halfplane
       (:instance lw-polynomial-edge-sample-halfplane (parameter 0))
       (:instance lw-polynomial-edge-sample-halfplane (parameter 1))
       lw-complex-segment-endpoints
       (:instance lw-ray-halfplane-chain-replacement
        (h (lw-complex-polynomial coefficients left 0))
        (current (lw-complex-polynomial coefficients left 0))
        (next (lw-complex-polynomial coefficients right 0))
        (points (lw-polynomial-edge-samples coefficients left right count))))
 :in-theory (union-theories
 '(lw-polynomial-edge-check lw-per-left-commutes lw-per-left-distributes lw-per-fold-constants lw-per-times-negative lw-per-negative-times lw-per-zero-times lw-per-minus-one lw-per-double-negative lw-per-add-cancel lw-per-double lw-per-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
