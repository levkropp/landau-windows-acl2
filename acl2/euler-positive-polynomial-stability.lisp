; Actual translated Euler models with arbitrary target degree and uniform perturbation.
(in-package "ACL2")
(include-book "euler-positive-square-cover")
(include-book "polygon-perturbation")
(include-book "polynomial-path-refinement")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp
 lw-complex-polynomial lw-euler-uniform-polynomial lw-polynomial-affine
 lw-euler-positive-square-polynomial lw-positive-squarep lw-square-containsp
 lw-positive-square-center-rate lw-positive-square-center-height
 lw-positive-square-disk-radius lw-positive-square-translation lw-positive-square-offset
 lw-complex-euler-continuation-value lw-ray-pointwise-nearp lw-polynomial-path-values)))
(local (defthm lw-epm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-epm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-epm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-epm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-epm-times-negative (a b) (b a)))
                 :in-theory (disable lw-epm-times-negative)))))

(local (defthm lw-epm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-epm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-epm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-epm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-epm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-epm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-epm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-epm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-epm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-epm-left-commutes)))))
(defun lw-euler-positive-square-model (anchor side target error)
 (lw-polynomial-affine
 (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) target (/ error 4))
 (lw-positive-square-translation anchor side) (cons 1 0)))
(defun lw-square-point-listp (anchor side points)
 (if (endp points) (equal points nil)
 (and (lw-square-containsp anchor side (car points))
      (lw-square-point-listp anchor side (cdr points)))))
(local (in-theory (disable lw-euler-positive-square-model lw-square-point-listp)))

(defthm lw-euler-positive-square-model-zero-target
 (equal (lw-euler-positive-square-model anchor side 0 error)
        (lw-euler-positive-square-polynomial anchor side error))
 :hints (("Goal" :in-theory (union-theories
 '(lw-euler-positive-square-model lw-euler-positive-square-polynomial lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-positive-square-model-valid
 (implies (and (lw-positive-squarep anchor side) (natp target) (rationalp error) (< 0 error))
 (lw-complex-coefficientsp (lw-euler-positive-square-model anchor side target error)))
 :hints (("Goal"
 :use (lw-positive-square-disk-data
       (:instance lw-positive-square-coordinate-recovery (point (cons 0 0)))
       (:instance lw-euler-uniform-polynomial-valid (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (radius (lw-positive-square-disk-radius anchor side)) (error (/ error 4)))
       (:instance lw-polynomial-affine-valid
        (coefficients (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) target (/ error 4)))
        (center (lw-positive-square-translation anchor side)) (slope (cons 1 0))))
 :in-theory (union-theories
 '(lw-euler-positive-square-model lw-complexp cons lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-positive-square-model-evaluation
 (implies (and (lw-positive-squarep anchor side) (lw-complexp point)
               (natp target) (rationalp error) (< 0 error))
 (equal (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) point 0)
        (lw-complex-polynomial
         (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) target (/ error 4)) (lw-positive-square-offset anchor side point) 0)))
 :hints (("Goal"
 :use (lw-positive-square-disk-data lw-positive-square-coordinate-recovery lw-positive-square-affine-point
       (:instance lw-euler-uniform-polynomial-valid (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (radius (lw-positive-square-disk-radius anchor side)) (error (/ error 4)))
       (:instance lw-polynomial-affine-evaluation
        (coefficients (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) target (/ error 4)))
        (center (lw-positive-square-translation anchor side)) (slope (cons 1 0))))
 :in-theory (union-theories
 '(lw-euler-positive-square-model lw-complexp cons lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-positive-square-model-comparison
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
               (natp target) (rationalp error) (< 0 error) (rationalp value-error) (< 0 value-error))
 (lw-complex-diskp
 (lw-complex-sub (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) point 0)
                 (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
 (+ (/ error 4) (/ value-error 4))))
 :hints (("Goal"
 :use (lw-positive-square-disk-data lw-positive-square-point-data
       lw-positive-square-coordinate-recovery lw-positive-square-offset-in-disk
       lw-euler-positive-square-model-evaluation
       (:instance lw-complex-euler-uniform-polynomial-comparison
        (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (radius (lw-positive-square-disk-radius anchor side)) (error (/ error 4)) (point (lw-positive-square-offset anchor side point))))
 :in-theory (union-theories
 '( lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-positive-square-model-cauchy
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-complex-diskp
 (lw-complex-sub
  (lw-complex-polynomial (lw-euler-positive-square-model anchor side right-target right-error) point 0)
  (lw-complex-polynomial (lw-euler-positive-square-model anchor side left-target left-error) point 0))
 (* 1/4 (+ left-error right-error))))
 :hints (("Goal"
 :use (lw-positive-square-disk-data lw-positive-square-point-data lw-positive-square-offset-in-disk
       (:instance lw-euler-positive-square-model-evaluation (target left-target) (error left-error))
       (:instance lw-euler-positive-square-model-evaluation (target right-target) (error right-error))
       (:instance lw-complex-euler-uniform-polynomial-cauchy
        (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (radius (lw-positive-square-disk-radius anchor side)) (point (lw-positive-square-offset anchor side point))
        (left-target right-target) (right-target left-target)
        (left-error (/ right-error 4)) (right-error (/ left-error 4))))
 :in-theory (union-theories
 '( lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-square-point-list-data
 (implies (lw-square-point-listp anchor side points)
 (and (lw-ray-pointsp points) (true-listp points)))
 :hints (("Goal" :induct (lw-square-point-listp anchor side points)
 :in-theory (union-theories
 '(lw-square-point-listp lw-square-containsp lw-ray-pointsp true-listp endp lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-square-point-list-append
 (implies (and (lw-square-point-listp anchor side left) (lw-square-point-listp anchor side right))
 (lw-square-point-listp anchor side (append left right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-square-point-listp append endp lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-positive-square-model-path-near
 (implies (and (lw-positive-squarep anchor side) (lw-square-point-listp anchor side points)
               (natp left-target) (natp right-target)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
 (lw-ray-pointwise-nearp
 (lw-polynomial-path-values (lw-euler-positive-square-model anchor side left-target left-error) points)
 (lw-polynomial-path-values (lw-euler-positive-square-model anchor side right-target right-error) points)
 (* 1/4 (+ left-error right-error))))
 :hints (("Goal" :induct (lw-square-point-listp anchor side points)
 :in-theory (union-theories
 '(lw-square-point-listp lw-polynomial-path-values lw-ray-pointwise-nearp endp lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-euler-positive-square-model-cauchy (point (car points)))
         (:instance lw-euler-positive-square-model-valid (target left-target) (error left-error))
         (:instance lw-euler-positive-square-model-valid (target right-target) (error right-error))
         (:instance lw-complex-polynomial-rational
          (coefficients (lw-euler-positive-square-model anchor side left-target left-error)) (point (car points)) (offset 0))
         (:instance lw-complex-polynomial-rational
          (coefficients (lw-euler-positive-square-model anchor side right-target right-error)) (point (car points)) (offset 0)))
   :in-theory (union-theories
 '(lw-square-containsp lw-epm-left-commutes lw-epm-left-distributes lw-epm-fold-constants lw-epm-times-negative lw-epm-negative-times lw-epm-zero-times lw-epm-minus-one lw-epm-double-negative lw-epm-add-cancel lw-epm-double lw-epm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
   :do-not-induct t))))

