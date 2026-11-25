; Two requested resolutions compute a complete polynomial sublevel cover.
(in-package "ACL2")
(include-book "polynomial-sublevel-cover")
(include-book "polynomial-certified-root-search")
(local (in-theory (disable lw-polynomial-sublevel-cover lw-square-cover-containsp lw-square-containsp
 lw-polynomial-cell-variation lw-polynomial-grid-step lw-polynomial-grid-radius lw-polynomial-lipschitz-cap
 lw-polynomial-root-count lw-polynomial-certified-root-count lw-complexp lw-complex-diskp lw-complex-polynomial
 lw-polynomial-square-boundary-check lw-ray-grid-boundary-index lw-polynomial-grid lw-square-cell-address)))
(local (defthm lw-prc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-prc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-prc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-prc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-prc-times-negative (a b) (b a)))
                 :in-theory (disable lw-prc-times-negative)))))

(local (defthm lw-prc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-prc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-prc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-prc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-prc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-prc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-prc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-prc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-prc-left-commutes)))))
(defun lw-square-spatial-count (side width)
 (+ 1 (lw-ceiling-rational (* side (/ width)))))
(defun lw-polynomial-resolved-cover-count (coefficients anchor side width epsilon)
 (lw-polynomial-certified-root-count coefficients anchor side (lw-square-spatial-count side width) epsilon))
(defun lw-polynomial-resolved-cover (coefficients anchor side width epsilon)
 (lw-polynomial-sublevel-cover coefficients anchor side
 (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon) epsilon))
(local (in-theory (disable lw-square-spatial-count lw-polynomial-resolved-cover-count lw-polynomial-resolved-cover)))

(defthm lw-square-spatial-count-data
 (implies (and (rationalp side) (< 0 side) (rationalp width) (< 0 width))
 (and (posp (lw-square-spatial-count side width))
      (<= (lw-polynomial-grid-step side (lw-square-spatial-count side width)) width)))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-positive (value width))
       (:instance lw-prc-positive-product (a side) (b (/ width)))
       (:instance lw-ceiling-rational-natural (value (* side (/ width))))
       (:instance lw-ceiling-rational-bracket (value (* side (/ width))))
       (:instance lw-prc-multiply-order (a (* side (/ width))) (b (+ 1 (lw-ceiling-rational (* side (/ width))))) (factor width))
       (:instance lw-prc-inverse-factor (divisor width) (coefficient side))
       (:instance lw-positive-division-bound (numerator side) (divisor (+ 1 (lw-ceiling-rational (* side (/ width))))) (bound width)))
 :in-theory (union-theories
 '(lw-square-spatial-count lw-polynomial-grid-step lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-prc-count-multiple
 (implies (and (posp coarse) (posp base))
 (and (posp (* coarse base)) (<= base (* coarse base))))
 :hints (("Goal"
 :use ((:instance lw-prc-positive-product (a coarse) (b base))
       (:instance lw-prc-multiply-order (a 1) (b coarse) (factor base)))
 :in-theory (union-theories
 '( lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(local (defthm lw-prc-step-decrease
 (implies (and (rationalp side) (<= 0 side) (posp small) (posp large) (<= small large))
 (<= (lw-polynomial-grid-step side large) (lw-polynomial-grid-step side small)))
 :hints (("Goal"
 :use ((:instance lw-reciprocal-antitone (left small) (right large))
       (:instance lw-prc-multiply-order (a (/ large)) (b (/ small)) (factor side)))
 :in-theory (union-theories
 '(lw-polynomial-grid-step lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-polynomial-resolved-cover-count-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (let ((count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
 (and (posp count) (rationalp (lw-polynomial-grid-step side count))
      (< 0 (lw-polynomial-grid-step side count)) (<= (lw-polynomial-grid-step side count) width)
      (rationalp (lw-polynomial-cell-variation coefficients anchor side count))
      (<= 0 (lw-polynomial-cell-variation coefficients anchor side count))
      (<= (lw-polynomial-cell-variation coefficients anchor side count) epsilon))))
 :hints (("Goal"
 :use (lw-square-spatial-count-data
       lw-polynomial-root-count-data
       (:instance lw-polynomial-certified-root-count-data (coarse (lw-square-spatial-count side width)))
       (:instance lw-prc-count-multiple (coarse (lw-polynomial-root-count coefficients anchor side epsilon)) (base (lw-square-spatial-count side width)))
       (:instance lw-prc-step-decrease (small (lw-square-spatial-count side width))
        (large (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
       (:instance lw-polynomial-grid-step-data (count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
       (:instance lw-polynomial-cell-variation-data (count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-resolved-cover-count lw-polynomial-certified-root-count lw-polynomial-cell-variation lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-resolved-cover-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (let ((count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
 (and (lw-square-address-listp (lw-polynomial-resolved-cover coefficients anchor side width epsilon) count)
      (lw-polynomial-active-coverp coefficients anchor side count epsilon
       (lw-polynomial-resolved-cover coefficients anchor side width epsilon))
      (<= (len (lw-polynomial-resolved-cover coefficients anchor side width epsilon)) (* count count)))))
 :hints (("Goal" :use (lw-polynomial-resolved-cover-count-data
       (:instance lw-polynomial-sublevel-cover-data (count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-resolved-cover lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-resolved-cover-complete
 (implies (and (lw-complex-coefficientsp coefficients) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-complex-diskp (lw-complex-polynomial coefficients point 0) epsilon))
 (let ((count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
 (and (member-equal (lw-square-cell-address anchor side count point)
                    (lw-polynomial-resolved-cover coefficients anchor side width epsilon))
      (lw-square-cover-containsp anchor side count point
                    (lw-polynomial-resolved-cover coefficients anchor side width epsilon)))))
 :hints (("Goal" :use (lw-polynomial-resolved-cover-count-data
       (:instance lw-polynomial-sublevel-cover-complete (count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-resolved-cover lw-square-containsp lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-resolved-cover-value-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (lw-square-cover-containsp anchor side
  (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon) point
  (lw-polynomial-resolved-cover coefficients anchor side width epsilon)))
 (and (lw-square-containsp anchor side point)
      (lw-complex-diskp (lw-complex-polynomial coefficients point 0) (* 3 epsilon))))
 :hints (("Goal"
 :use (lw-polynomial-resolved-cover-count-data
       (:instance lw-polynomial-sublevel-cover-value-bound (count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))
       (:instance lw-square-cover-in-square (count (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon))
        (addresses (lw-polynomial-resolved-cover coefficients anchor side width epsilon)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial coefficients point 0))
        (radius (+ epsilon (* 2 (lw-polynomial-cell-variation coefficients anchor side
                  (lw-polynomial-resolved-cover-count coefficients anchor side width epsilon)))))
        (cap (* 3 epsilon))))
 :in-theory (union-theories
 '(lw-polynomial-resolved-cover lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-empty-resolved-cover-excludes-small
 (implies (and (lw-complex-coefficientsp coefficients) (lw-square-containsp anchor side point)
 (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
 (not (consp (lw-polynomial-resolved-cover coefficients anchor side width epsilon))))
 (not (lw-complex-diskp (lw-complex-polynomial coefficients point 0) epsilon)))
 :hints (("Goal" :use lw-polynomial-resolved-cover-complete
 :in-theory (union-theories
 '(lw-square-cover-containsp endp lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-resolved-cover-nonempty
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (< 0 side)
 (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon) (posp coarse)
 (lw-polynomial-square-boundary-check coefficients anchor side coarse)
 (not (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side coarse)) 0)))
 (consp (lw-polynomial-resolved-cover coefficients anchor side width epsilon)))
 :hints (("Goal"
 :use (lw-polynomial-certified-root-search-witness
       (:instance lw-polynomial-empty-resolved-cover-excludes-small
        (point (lw-polynomial-certified-root-point coefficients anchor side coarse epsilon))))
 :in-theory (union-theories
 '(lw-square-containsp lw-prc-left-commutes lw-prc-left-distributes lw-prc-fold-constants lw-prc-times-negative lw-prc-negative-times lw-prc-zero-times lw-prc-minus-one lw-prc-double-negative lw-prc-add-cancel lw-prc-double lw-prc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
