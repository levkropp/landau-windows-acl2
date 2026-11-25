; Coefficient-controlled polygon paths inside a rational square.
(in-package "ACL2")
(include-book "euler-positive-polynomial-stability")
(local (in-theory (disable lw-complexp lw-complex-sub lw-complex-diskp lw-complex-polynomial
 lw-square-containsp lw-square-point-listp lw-polynomial-path-values lw-ray-row-near-check
 lw-ray-close-polygon lw-polynomial-lipschitz-cap lw-polynomial-grid-radius lw-complex-segment)))
(local (defthm lw-psp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psp-times-negative (a b) (b a)))
                 :in-theory (disable lw-psp-times-negative)))))

(local (defthm lw-psp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psp-left-commutes)))))
(local (defthm lw-psp-map-heads
 (and (equal (consp (lw-polynomial-path-values coefficients points)) (consp points))
      (implies (consp points)
       (and (equal (car (lw-polynomial-path-values coefficients points))
                   (lw-complex-polynomial coefficients (car points) 0))
            (equal (cdr (lw-polynomial-path-values coefficients points))
                   (lw-polynomial-path-values coefficients (cdr points))))))
 :hints (("Goal" :expand ((lw-polynomial-path-values coefficients points))
 :in-theory (union-theories
 '(lw-polynomial-path-values endp lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-path-values-shape
 (and (equal (consp (lw-polynomial-path-values coefficients points)) (consp points))
      (equal (len (lw-polynomial-path-values coefficients points)) (len points)))
 :hints (("Goal" :induct (lw-polynomial-path-values coefficients points)
 :in-theory (union-theories
 '(lw-polynomial-path-values endp len lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-square-point-list-close
 (implies (lw-square-point-listp anchor side points)
 (lw-square-point-listp anchor side (lw-ray-close-polygon points)))
 :hints (("Goal"
 :use ((:instance lw-square-point-list-append
        (left (cdr points)) (right (list (car points)))))
 :in-theory (union-theories
 '(lw-square-point-listp lw-ray-close-polygon append endp cons lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-square-segment-contained
 (implies (and (lw-square-containsp anchor side left) (lw-square-containsp anchor side right)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-square-containsp anchor side (lw-complex-segment left right parameter)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-square-containsp lw-complex-segment lw-complexp lw-complex-add lw-complex-scale lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)))

(defthm lw-polynomial-path-values-close
 (equal (lw-polynomial-path-values coefficients (lw-ray-close-polygon points))
        (lw-ray-close-polygon (lw-polynomial-path-values coefficients points)))
 :hints (("Goal"
 :use ((:instance lw-polynomial-path-values-append
        (left (cdr points)) (right (list (car points)))))
 :expand ((lw-polynomial-path-values coefficients points))
 :in-theory (union-theories
 '(lw-ray-close-polygon lw-polynomial-path-values append endp cons lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-path-step-bound
 (implies (and (lw-complex-coefficientsp coefficients)
               (lw-complexp anchor) (rationalp side) (< 0 side)
               (lw-square-point-listp anchor side points)
               (rationalp step) (<= 0 step)
               (lw-ray-row-near-check points points step))
 (lw-ray-row-near-check (lw-polynomial-path-values coefficients points)
                       (lw-polynomial-path-values coefficients points)
 (* step (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side)))))
 :hints (("Goal" :induct (lw-square-point-listp anchor side points)
 :in-theory (union-theories
 '(lw-psp-map-heads lw-square-point-listp lw-polynomial-path-values lw-ray-row-near-check endp lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-grid-radius-data)
         (:instance lw-polynomial-lipschitz-cap-data (bound (lw-polynomial-grid-radius anchor side)))
         (:instance lw-square-contained-in-disk (point (car points)))
         (:instance lw-square-contained-in-disk (point (cadr points)))
         (:instance lw-complex-polynomial-lipschitz (left (cadr points)) (right (car points)) (bound (lw-polynomial-grid-radius anchor side)))
         (:instance lw-complex-polynomial-lipschitz (left (car points)) (right (car points)) (bound (lw-polynomial-grid-radius anchor side))))
   :in-theory (union-theories
 '(lw-psp-map-heads lw-square-point-listp lw-square-containsp lw-polynomial-path-values lw-ray-row-near-check endp lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
   :do-not-induct t))))

(defthm lw-polynomial-square-polygon-step-bound
 (implies (and (lw-complex-coefficientsp coefficients)
               (lw-complexp anchor) (rationalp side) (< 0 side)
               (lw-square-point-listp anchor side points)
               (rationalp step) (<= 0 step)
               (lw-ray-row-near-check (lw-ray-close-polygon points) (lw-ray-close-polygon points) step))
 (lw-ray-row-near-check
  (lw-ray-close-polygon (lw-polynomial-path-values coefficients points))
  (lw-ray-close-polygon (lw-polynomial-path-values coefficients points))
 (* step (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side)))))
 :hints (("Goal" :use (lw-square-point-list-close
       (:instance lw-polynomial-square-path-step-bound (points (lw-ray-close-polygon points))))
 :in-theory (union-theories
 '(lw-polynomial-path-values-close lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-complex-perturbation-excludes-small
 (implies (and (lw-complexp left) (lw-complexp right)
               (rationalp epsilon) (<= 0 epsilon) (rationalp delta) (<= 0 delta)
               (lw-complex-diskp (lw-complex-sub right left) delta)
               (not (lw-complex-diskp left (+ epsilon delta))))
 (not (lw-complex-diskp right epsilon)))
 :hints (("Goal"
 :use ((:instance lw-complex-difference-symmetric (left right) (right left) (radius delta))
       (:instance lw-complex-difference-triangle
        (left left) (middle right) (right (cons 0 0)) (radius delta) (other-radius epsilon)))
 :in-theory (union-theories
 '(lw-complex-sub-zero cons (:executable-counterpart lw-complexp) lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-segment-variation
 (implies (and (lw-complex-coefficientsp coefficients)
               (lw-square-containsp anchor side left) (lw-square-containsp anchor side right)
               (rationalp step) (<= 0 step)
               (lw-complex-diskp (lw-complex-sub right left) step)
               (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-complex-diskp
 (lw-complex-sub (lw-complex-polynomial coefficients (lw-complex-segment left right parameter) 0)
                 (lw-complex-polynomial coefficients left 0))
 (* step (lw-polynomial-lipschitz-cap coefficients (lw-polynomial-grid-radius anchor side)))))
 :hints (("Goal"
 :use (lw-square-segment-contained lw-polynomial-grid-radius-data
       (:instance lw-square-contained-in-disk (point left))
       (:instance lw-square-contained-in-disk (point (lw-complex-segment left right parameter)))
       (:instance lw-complex-segment-centered-disk (center left) (radius step))
       (:instance lw-complex-polynomial-lipschitz (left (lw-complex-segment left right parameter)) (right left) (bound (lw-polynomial-grid-radius anchor side))))
 :in-theory (union-theories
 '(lw-square-containsp lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-psp-left-commutes lw-psp-left-distributes lw-psp-fold-constants lw-psp-times-negative lw-psp-negative-times lw-psp-zero-times lw-psp-minus-one lw-psp-double-negative lw-psp-add-cancel lw-psp-double lw-psp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

