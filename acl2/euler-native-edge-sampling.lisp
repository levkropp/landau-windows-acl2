; Native Euler edge samples share the fixed coarse positive half-plane.
(in-package "ACL2")
(include-book "euler-native-polygon-index")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp
 lw-complex-polynomial lw-complex-norm-square lw-complex-positive-halfplanep
 lw-euler-polygon-index-check lw-euler-positive-square-model lw-euler-polygon-edge-point
 lw-complex-euler-continuation-value lw-unit-parametersp lw-unit-mesh lw-ray-halfplane-points)))
(local (defthm lw-nes-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nes-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nes-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nes-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nes-times-negative (a b) (b a)))
                 :in-theory (disable lw-nes-times-negative)))))

(local (defthm lw-nes-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nes-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nes-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nes-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nes-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nes-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nes-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nes-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nes-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nes-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nes-left-commutes)))))
(defun lw-euler-polygon-base-anchor (anchor side points base-target base-error index)
 (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0))
(defun lw-euler-native-edge-value (points index parameter value-error)
 (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error))
(defun lw-euler-native-edge-values (points index parameters value-error)
 (if (endp parameters) nil
 (cons (lw-euler-native-edge-value points index (car parameters) value-error)
       (lw-euler-native-edge-values points index (cdr parameters) value-error))))
(defun lw-euler-native-edge-samples (points index count value-error)
 (lw-euler-native-edge-values points index (lw-unit-mesh count 1 (nfix (- count 1))) value-error))
(local (in-theory (disable lw-euler-polygon-base-anchor lw-euler-native-edge-value
 lw-euler-native-edge-values lw-euler-native-edge-samples)))

(defthm lw-euler-native-edge-near-anchor
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (and (lw-complexp (lw-euler-polygon-base-anchor anchor side points base-target base-error index)) (lw-complexp (lw-euler-native-edge-value points index parameter value-error))
      (lw-complex-diskp (lw-complex-sub (lw-euler-native-edge-value points index parameter value-error) (lw-euler-polygon-base-anchor anchor side points base-target base-error index)) (* 3/4 eta))))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-euler-polygon-edge-data lw-euler-polygon-segment-variation
       (:instance lw-euler-positive-square-model-comparison (target base-target) (error base-error) (point (lw-euler-polygon-edge-point points index parameter)))
       (:instance lw-complex-euler-continuation-value-rational (rate (car (lw-euler-polygon-edge-point points index parameter))) (height (cdr (lw-euler-polygon-edge-point points index parameter))) (error value-error))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0)) (right (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error)) (radius (+ (/ base-error 4) (/ value-error 4))))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0))
        (radius (+ (/ base-error 4) (/ value-error 4))) (other-radius (/ eta 4)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)))
        (radius (+ (/ base-error 4) (/ value-error 4) (/ eta 4))) (cap (* 3/4 eta))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-euler-polygon-base-anchor lw-euler-native-edge-value lw-complexp lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-nes-radius-square
 (implies (and (rationalp eta) (<= 0 eta))
 (<= (* (* 3/4 eta) (* 3/4 eta)) (* eta eta)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-native-edge-halfplane
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (rationalp parameter) (<= 0 parameter) (<= parameter 1) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (lw-complex-positive-halfplanep (lw-euler-polygon-base-anchor anchor side points base-target base-error index) (lw-euler-native-edge-value points index parameter value-error)))
 :hints (("Goal"
 :use (lw-euler-native-edge-near-anchor lw-euler-polygon-edge-data
       (:instance lw-complex-disk-norm-square (point (lw-euler-polygon-base-anchor anchor side points base-target base-error index)) (radius eta))
       lw-nes-radius-square
       (:instance lw-complex-disk-positive-halfplane (anchor (lw-euler-polygon-base-anchor anchor side points base-target base-error index)) (point (lw-euler-native-edge-value points index parameter value-error)) (radius (* 3/4 eta))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-euler-polygon-base-anchor lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-polygon-edge-endpoints
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)))
 (and (equal (lw-euler-polygon-edge-point points index 0) (nth index (lw-ray-close-polygon points)))
      (equal (lw-euler-polygon-edge-point points index 1) (nth (+ 1 index) (lw-ray-close-polygon points)))))
 :hints (("Goal" :use (lw-euler-polygon-edge-data
       (:instance lw-complex-segment-endpoints (left (nth index (lw-ray-close-polygon points))) (right (nth (+ 1 index) (lw-ray-close-polygon points)))))
 :in-theory (union-theories
 '(lw-euler-polygon-edge-point lw-square-containsp lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-edge-values-halfplane
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (lw-unit-parametersp parameters) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (lw-ray-halfplane-points (lw-euler-polygon-base-anchor anchor side points base-target base-error index) (lw-euler-native-edge-values points index parameters value-error)))
 :hints (("Goal" :induct (lw-euler-native-edge-values points index parameters value-error)
 :in-theory (union-theories
 '(lw-euler-native-edge-values lw-unit-parametersp lw-ray-halfplane-points endp lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-native-edge-halfplane (parameter (car parameters))))
   :do-not-induct t))))

(defthm lw-euler-native-edge-values-length
 (equal (len (lw-euler-native-edge-values points index parameters value-error)) (len parameters))
 :hints (("Goal" :induct (lw-euler-native-edge-values points index parameters value-error)
 :in-theory (union-theories
 '(lw-euler-native-edge-values len endp lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-native-edge-samples-halfplane
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (posp count) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (and (lw-ray-halfplane-points (lw-euler-polygon-base-anchor anchor side points base-target base-error index) (lw-euler-native-edge-samples points index count value-error))
      (equal (len (lw-euler-native-edge-samples points index count value-error)) (- count 1))))
 :hints (("Goal"
 :use ((:instance lw-unit-mesh-data (index 1) (remaining (nfix (- count 1))))
       (:instance lw-euler-native-edge-values-halfplane
        (parameters (lw-unit-mesh count 1 (nfix (- count 1))))))
 :in-theory (union-theories
 '(lw-euler-native-edge-samples lw-euler-native-edge-values-length nfix lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-edge-refinement-index
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)) (posp count) (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (equal
 (+ (lw-ray-path-index
     (lw-complex-euler-continuation-value (car (nth index (lw-ray-close-polygon points))) (cdr (nth index (lw-ray-close-polygon points))) value-error)
     (lw-euler-native-edge-samples points index count value-error))
    (lw-ray-crossing
     (lw-ray-path-last
      (lw-complex-euler-continuation-value (car (nth index (lw-ray-close-polygon points))) (cdr (nth index (lw-ray-close-polygon points))) value-error)
      (lw-euler-native-edge-samples points index count value-error))
     (lw-complex-euler-continuation-value (car (nth (+ 1 index) (lw-ray-close-polygon points))) (cdr (nth (+ 1 index) (lw-ray-close-polygon points))) value-error)))
 (lw-ray-crossing
  (lw-complex-euler-continuation-value (car (nth index (lw-ray-close-polygon points))) (cdr (nth index (lw-ray-close-polygon points))) value-error)
  (lw-complex-euler-continuation-value (car (nth (+ 1 index) (lw-ray-close-polygon points))) (cdr (nth (+ 1 index) (lw-ray-close-polygon points))) value-error))))
 :hints (("Goal"
 :use (lw-euler-polygon-edge-endpoints lw-euler-native-edge-samples-halfplane
       (:instance lw-euler-native-edge-halfplane (parameter 0))
       (:instance lw-euler-native-edge-halfplane (parameter 1))
       (:instance lw-ray-halfplane-chain-replacement
        (h (lw-euler-polygon-base-anchor anchor side points base-target base-error index))
        (current (lw-complex-euler-continuation-value (car (nth index (lw-ray-close-polygon points))) (cdr (nth index (lw-ray-close-polygon points))) value-error))
        (next (lw-complex-euler-continuation-value (car (nth (+ 1 index) (lw-ray-close-polygon points))) (cdr (nth (+ 1 index) (lw-ray-close-polygon points))) value-error))
        (points (lw-euler-native-edge-samples points index count value-error))))
 :in-theory (union-theories
 '(lw-euler-native-edge-value lw-nes-left-commutes lw-nes-left-distributes lw-nes-fold-constants lw-nes-times-negative lw-nes-negative-times lw-nes-zero-times lw-nes-minus-one lw-nes-double-negative lw-nes-add-cancel lw-nes-double lw-nes-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

