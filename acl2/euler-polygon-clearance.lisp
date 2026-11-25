; Native Euler clearance on every segment of a fixed index certificate.
(in-package "ACL2")
(include-book "euler-polygon-index")
(include-book "polygon-edge-access")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp
 lw-complex-polynomial lw-complex-norm-square lw-complex-reciprocal lw-complex-l1
 lw-complex-positive-halfplanep lw-square-containsp lw-square-point-listp
 lw-euler-polygon-index-check lw-euler-positive-square-model lw-ray-close-polygon
 lw-polynomial-path-values lw-ray-row-avoids lw-ray-row-near-check
 lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower
 lw-complex-euler-continuation-value)))
(local (defthm lw-epc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epc-times-negative (a b) (b a)))
                 :in-theory (disable lw-epc-times-negative)))))

(local (defthm lw-epc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epc-left-commutes)))))
(defun lw-euler-polygon-edge-point (points index parameter)
 (lw-complex-segment (nth index (lw-ray-close-polygon points)) (nth (+ 1 index) (lw-ray-close-polygon points)) parameter))
(local (in-theory (disable lw-euler-polygon-edge-point)))

(defthm lw-euler-polygon-edge-data
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points)))
 (and (lw-square-containsp anchor side (nth index (lw-ray-close-polygon points))) (lw-square-containsp anchor side (nth (+ 1 index) (lw-ray-close-polygon points)))
      (lw-complex-diskp (lw-complex-sub (nth (+ 1 index) (lw-ray-close-polygon points)) (nth index (lw-ray-close-polygon points))) step)
      (lw-complexp (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)) (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0) eta))))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-square-point-list-close lw-square-point-list-data
       (:instance lw-ray-close-polygon-data)
       (:instance lw-square-point-list-nth (points (lw-ray-close-polygon points)))
       (:instance lw-square-point-list-nth (points (lw-ray-close-polygon points)) (index (+ 1 index)))
       (:instance lw-ray-row-near-nth (points (lw-ray-close-polygon points)))
       (:instance lw-ray-close-polygon-avoids (points (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) points)) (epsilon eta))
       (:instance lw-polynomial-path-values-shape (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (points (lw-ray-close-polygon points)))
       (:instance lw-ray-row-avoids-nth (points (lw-polynomial-path-values (lw-euler-positive-square-model anchor side base-target base-error) (lw-ray-close-polygon points))) (radius eta))
       (:instance lw-polynomial-path-values-nth (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (points (lw-ray-close-polygon points)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (nth index (lw-ray-close-polygon points))) (offset 0)))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-square-containsp lw-polynomial-path-values-close lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-polygon-segment-variation
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (and (lw-square-containsp anchor side (lw-euler-polygon-edge-point points index parameter))
      (lw-complexp (lw-euler-polygon-edge-point points index parameter)) (< 0 (car (lw-euler-polygon-edge-point points index parameter)))
      (lw-complexp (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0))
      (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)) (/ eta 4))))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-euler-polygon-edge-data
       (:instance lw-square-segment-contained (left (nth index (lw-ray-close-polygon points))) (right (nth (+ 1 index) (lw-ray-close-polygon points))))
       (:instance lw-positive-square-point-data (point (lw-euler-polygon-edge-point points index parameter)))
       (:instance lw-polynomial-square-segment-variation
        (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (left (nth index (lw-ray-close-polygon points))) (right (nth (+ 1 index) (lw-ray-close-polygon points))))
       (:instance lw-polynomial-lipschitz-cap-data (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (bound (lw-polynomial-grid-radius anchor side)))
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side base-target base-error)) (point (lw-euler-polygon-edge-point points index parameter)) (offset 0))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)))
        (radius (* step (lw-polynomial-lipschitz-cap (lw-euler-positive-square-model anchor side base-target base-error) (lw-polynomial-grid-radius anchor side)))) (cap (/ eta 4))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-euler-polygon-edge-point lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-epc-radius-square
 (implies (and (rationalp eta) (<= 0 eta)) (<= (* (* 3/4 eta) (* 3/4 eta)) (* eta eta)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-polygon-model-edge-halfplane
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (lw-complex-positive-halfplanep (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-euler-polygon-edge-point points index parameter) 0)))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-euler-polygon-edge-data lw-euler-polygon-segment-variation
       (:instance lw-euler-positive-square-model-valid)
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side target error)) (point (lw-euler-polygon-edge-point points index parameter)) (offset 0))
       (:instance lw-euler-positive-square-model-cauchy
        (left-target base-target) (left-error base-error) (right-target target) (right-error error) (point (lw-euler-polygon-edge-point points index parameter)))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-euler-polygon-edge-point points index parameter) 0)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0))
        (radius (* 1/4 (+ base-error error))) (other-radius (/ eta 4)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-euler-polygon-edge-point points index parameter) 0) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)))
        (radius (+ (* 1/4 (+ base-error error)) (/ eta 4))) (cap (* 3/4 eta)))
       (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)) (radius eta))
       (:instance lw-epc-radius-square)
       (:instance lw-complex-disk-positive-halfplane
        (anchor (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)) (point (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) (lw-euler-polygon-edge-point points index parameter) 0)) (radius (* 3/4 eta))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-epc-quarter-sum
 (implies (rationalp eta) (equal (+ (* 1/4 eta) (* 3/4 eta)) eta))
 :hints (("Goal" :nonlinearp t))))

(defthm lw-euler-polygon-native-edge-excludes-small
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1)
               (rationalp value-error) (< 0 value-error) (<= value-error eta))
 (not (lw-complex-diskp (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error) (/ eta 4))))
 :hints (("Goal"
 :use (lw-euler-polygon-index-check-data lw-euler-polygon-edge-data lw-euler-polygon-segment-variation
       (:instance lw-euler-positive-square-model-comparison (target base-target) (error base-error) (point (lw-euler-polygon-edge-point points index parameter)))
       (:instance lw-complex-euler-continuation-value-rational (rate (car (lw-euler-polygon-edge-point points index parameter))) (height (cdr (lw-euler-polygon-edge-point points index parameter))) (error value-error))
       (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0)) (right (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error)) (radius (+ (/ base-error 4) (/ value-error 4))))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error)) (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (lw-euler-polygon-edge-point points index parameter) 0)) (right (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0))
        (radius (+ (/ base-error 4) (/ value-error 4))) (other-radius (/ eta 4)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-sub (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error) (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)))
        (radius (+ (/ base-error 4) (/ value-error 4) (/ eta 4))) (cap (* 3/4 eta)))
       (:instance lw-complex-perturbation-excludes-small
        (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side base-target base-error) (nth index (lw-ray-close-polygon points)) 0)) (right (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) value-error)) (epsilon (/ eta 4)) (delta (* 3/4 eta))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-epc-quarter-sum lw-complexp lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-epc-not-small-l1
 (implies (and (lw-complexp value) (rationalp eta) (< 0 eta)
               (not (lw-complex-diskp value (/ eta 4))))
 (< (/ eta 4) (lw-complex-l1 value)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-bound (point value))
       (:instance lw-complex-disk-enlarge (point value) (radius (lw-complex-l1 value)) (cap (/ eta 4))))
 :in-theory (union-theories
 '( lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-polygon-native-edge-check
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (and (lw-euler-value-clearance-check (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) (/ eta 64))
      (<= (/ eta 16) (lw-euler-value-clearance-lower (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) (/ eta 64)))))
 :hints (("Goal"
 :use (lw-euler-polygon-segment-variation
       (:instance lw-euler-polygon-native-edge-excludes-small (value-error (/ eta 64)))
       (:instance lw-complex-euler-continuation-value-rational
        (rate (car (lw-euler-polygon-edge-point points index parameter))) (height (cdr (lw-euler-polygon-edge-point points index parameter))) (error (/ eta 64)))
       (:instance lw-epc-not-small-l1
        (value (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) (/ eta 64)))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-complexp lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-epc-square-order
 (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b)) (<= (* a a) (* b b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-polygon-native-edge-denominator
 (implies (and (lw-euler-polygon-index-check anchor side points base-target base-error step eta) (natp index) (< index (len points))
               (rationalp parameter) (<= 0 parameter) (<= parameter 1)
               (rationalp request) (< 0 request) (<= request (/ eta 64)))
 (let ((value (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) request)))
 (and (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ eta 16) (/ eta 16)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ eta 16))))))
 :hints (("Goal"
 :use (lw-euler-polygon-native-edge-check
       (:instance lw-euler-value-clearance-data (rate (car (lw-euler-polygon-edge-point points index parameter))) (height (cdr (lw-euler-polygon-edge-point points index parameter))) (anchor-error (/ eta 64)))
       (:instance lw-complex-euler-value-clearance (rate (car (lw-euler-polygon-edge-point points index parameter))) (height (cdr (lw-euler-polygon-edge-point points index parameter))) (anchor-error (/ eta 64)))
       (:instance lw-epc-square-order (a (/ eta 16))
        (b (lw-euler-value-clearance-lower (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) (/ eta 64))))
       (:instance lw-complex-reciprocal-disk-bound
        (point (lw-complex-euler-continuation-value (car (lw-euler-polygon-edge-point points index parameter)) (cdr (lw-euler-polygon-edge-point points index parameter)) request)) (lower (/ eta 16))))
 :in-theory (union-theories
 '(lw-euler-polygon-index-check lw-epc-quarter-sum lw-complexp lw-epc-left-commutes lw-epc-left-distributes lw-epc-fold-constants lw-epc-times-negative lw-epc-negative-times lw-epc-zero-times lw-epc-minus-one lw-epc-double-negative lw-epc-add-cancel lw-epc-double lw-epc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

