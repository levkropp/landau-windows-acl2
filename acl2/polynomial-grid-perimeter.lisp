; Identify the actual square-grid perimeter as mapped domain vertices.
(in-package "ACL2")
(include-book "grid-perimeter")
(include-book "polynomial-path-refinement")
(include-book "polynomial-grid")
(local (in-theory (disable lw-complexp lw-complex-polynomial lw-complex-coefficientsp lw-complex-power
 lw-complex-add lw-complex-mul lw-ray-path-last lw-ray-row-last lw-ray-pointsp lw-ray-reverse-points
 lw-ray-gridp lw-ray-grid-left lw-ray-grid-right lw-ray-grid-last-row lw-ray-grid-perimeter lw-ray-four-path-perimeter
 lw-polynomial-path-values lw-polynomial-grid lw-polynomial-grid-row lw-polynomial-grid-rows lw-polynomial-grid-value lw-polynomial-grid-point)))
(local (defthm lw-pgm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pgm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pgm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pgm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pgm-times-negative (a b) (b a)))
                 :in-theory (disable lw-pgm-times-negative)))))

(local (defthm lw-pgm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pgm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pgm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pgm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pgm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pgm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pgm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pgm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pgm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pgm-left-commutes)))))
(defun lw-polynomial-grid-map (coefficients rows)
 (declare (xargs :measure (acl2-count rows) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp rows) nil
 (cons (lw-polynomial-path-values coefficients (car rows)) (lw-polynomial-grid-map coefficients (cdr rows)))))
(defun lw-polynomial-domain-grid (anchor side count)
 (lw-polynomial-grid '((0 . 0) (1 . 0)) anchor side count))
(defun lw-polynomial-square-boundary (anchor side count)
 (lw-ray-grid-perimeter (lw-polynomial-domain-grid anchor side count)))
(local (in-theory (disable lw-polynomial-grid-map lw-polynomial-domain-grid lw-polynomial-square-boundary)))

(local (defthm lw-pgm-map-heads
 (and (equal (consp (lw-polynomial-path-values coefficients points)) (consp points))
      (equal (consp (lw-polynomial-grid-map coefficients rows)) (consp rows))
      (implies (consp points)
       (and (equal (car (lw-polynomial-path-values coefficients points)) (lw-complex-polynomial coefficients (car points) 0))
            (equal (cdr (lw-polynomial-path-values coefficients points)) (lw-polynomial-path-values coefficients (cdr points)))))
      (and (equal (car (lw-polynomial-grid-map coefficients rows)) (lw-polynomial-path-values coefficients (car rows)))
            (equal (cdr (lw-polynomial-grid-map coefficients rows)) (lw-polynomial-grid-map coefficients (cdr rows)))))
 :hints (("Goal" :expand ((lw-polynomial-path-values coefficients points) (lw-polynomial-grid-map coefficients rows))
 :in-theory (union-theories
 '(lw-polynomial-path-values lw-polynomial-grid-map endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-path-values-append
 (equal (lw-polynomial-path-values coefficients (append left right))
 (append (lw-polynomial-path-values coefficients left) (lw-polynomial-path-values coefficients right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-polynomial-path-values append endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-path-values-reverse
 (equal (lw-polynomial-path-values coefficients (lw-ray-reverse-points points))
 (lw-ray-reverse-points (lw-polynomial-path-values coefficients points)))
 :hints (("Goal" :induct (lw-ray-reverse-points points)
 :in-theory (union-theories
 '(lw-ray-reverse-points lw-polynomial-path-values lw-polynomial-path-values-append endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pgm-map-last
 (equal (lw-ray-path-last (lw-complex-polynomial coefficients current 0) (lw-polynomial-path-values coefficients points))
        (lw-complex-polynomial coefficients (lw-ray-path-last current points) 0))
 :hints (("Goal" :induct (lw-ray-path-last current points)
 :in-theory (union-theories
 '(lw-ray-path-last lw-polynomial-path-values endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pgm-map-row-last
 (implies (consp points)
 (equal (lw-ray-row-last (lw-polynomial-path-values coefficients points))
        (lw-complex-polynomial coefficients (lw-ray-row-last points) 0)))
 :hints (("Goal" :use ((:instance lw-pgm-map-last (current (car points)) (points (cdr points))))
 :in-theory (union-theories
 '(lw-pgm-map-heads lw-ray-row-last endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-pgm-last-row-step
 (implies (consp (cdr rows)) (equal (lw-ray-grid-last-row rows) (lw-ray-grid-last-row (cdr rows))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pgm-last-row-base
 (implies (endp (cdr rows)) (equal (lw-ray-grid-last-row rows) (car rows)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pgm-map-grid-last
 (equal (lw-ray-grid-last-row (lw-polynomial-grid-map coefficients rows))
        (lw-polynomial-path-values coefficients (lw-ray-grid-last-row rows)))
 :hints (("Goal" :induct (lw-polynomial-grid-map coefficients rows)
 :in-theory (union-theories
 '(lw-polynomial-grid-map lw-pgm-map-heads lw-pgm-last-row-step lw-pgm-last-row-base lw-polynomial-path-values endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp '(:cases ((consp (cdr rows))) :do-not-induct t)))))

(local (defthm lw-pgm-positive-length
 (implies (< 0 (len points)) (consp points))
 :hints (("Goal" :in-theory (union-theories
 '(len endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))) :rule-classes nil))

(defthm lw-polynomial-grid-map-left
 (implies (and (posp width) (lw-ray-gridp rows width))
 (equal (lw-ray-grid-left (lw-polynomial-grid-map coefficients rows))
        (lw-polynomial-path-values coefficients (lw-ray-grid-left rows))))
 :hints (("Goal" :induct (lw-ray-gridp rows width)
 :in-theory (union-theories
 '(lw-ray-gridp lw-ray-grid-left lw-polynomial-grid-map lw-polynomial-path-values lw-pgm-map-heads endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-pgm-positive-length (points (car rows)))) :do-not-induct t))))

(defthm lw-polynomial-grid-map-right
 (implies (and (posp width) (lw-ray-gridp rows width))
 (equal (lw-ray-grid-right (lw-polynomial-grid-map coefficients rows))
        (lw-polynomial-path-values coefficients (lw-ray-grid-right rows))))
 :hints (("Goal" :induct (lw-ray-gridp rows width)
 :in-theory (union-theories
 '(lw-ray-gridp lw-ray-grid-right lw-polynomial-grid-map lw-polynomial-path-values lw-pgm-map-row-last lw-pgm-map-heads endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-pgm-positive-length (points (car rows)))) :do-not-induct t))))

(defthm lw-polynomial-grid-map-perimeter
 (implies (and (posp width) (lw-ray-gridp rows width))
 (equal (lw-ray-grid-perimeter (lw-polynomial-grid-map coefficients rows))
        (lw-polynomial-path-values coefficients (lw-ray-grid-perimeter rows))))
 :hints (("Goal"
 :use (lw-polynomial-grid-map-left lw-polynomial-grid-map-right lw-pgm-map-grid-last)
 :in-theory (union-theories
 '(lw-ray-grid-perimeter lw-ray-four-path-perimeter lw-pgm-map-heads lw-polynomial-path-values-append lw-polynomial-path-values-reverse endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-pgm-identity
 (implies (lw-complexp point)
 (equal (lw-complex-polynomial '((0 . 0) (1 . 0)) point 0) point))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial lw-complex-power lw-complex-add lw-complex-mul lw-complexp endp nfix lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pgm-map-grid-row
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp row) (natp column) (natp remaining))
 (equal (lw-polynomial-path-values coefficients (lw-polynomial-grid-row '((0 . 0) (1 . 0)) anchor side count row column remaining))
        (lw-polynomial-grid-row coefficients anchor side count row column remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-row '((0 . 0) (1 . 0)) anchor side count row column remaining)
 :in-theory (union-theories
 '(lw-polynomial-grid-row lw-polynomial-path-values lw-polynomial-grid-value lw-pgm-identity lw-polynomial-grid-point-rational endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pgm-map-grid-rows
 (implies (and (lw-complexp anchor) (rationalp side) (posp count) (natp row) (natp remaining))
 (equal (lw-polynomial-grid-map coefficients (lw-polynomial-grid-rows '((0 . 0) (1 . 0)) anchor side count row remaining))
        (lw-polynomial-grid-rows coefficients anchor side count row remaining)))
 :hints (("Goal" :induct (lw-polynomial-grid-rows '((0 . 0) (1 . 0)) anchor side count row remaining)
 :in-theory (union-theories
 '(lw-polynomial-grid-rows lw-polynomial-grid-map lw-pgm-map-grid-row endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-grid-as-domain-map
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
 (equal (lw-polynomial-grid-map coefficients (lw-polynomial-domain-grid anchor side count))
        (lw-polynomial-grid coefficients anchor side count)))
 :hints (("Goal" :use ((:instance lw-pgm-map-grid-rows (row 0) (remaining (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-domain-grid lw-polynomial-grid lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-domain-grid-data
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
 (and (lw-ray-gridp (lw-polynomial-domain-grid anchor side count) (+ 1 count))
      (consp (lw-polynomial-domain-grid anchor side count))
      (equal (len (lw-polynomial-domain-grid anchor side count)) (+ 1 count))))
 :hints (("Goal"
 :use ((:instance lw-polynomial-grid-data (coefficients '((0 . 0) (1 . 0))))
       (:instance lw-pgm-positive-length (points (lw-polynomial-domain-grid anchor side count))))
 :in-theory (union-theories
 '(lw-polynomial-domain-grid lw-complex-coefficientsp lw-complexp endp lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-square-boundary-data
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
 (and (lw-ray-pointsp (lw-polynomial-square-boundary anchor side count))
      (consp (lw-polynomial-square-boundary anchor side count))
      (equal (lw-ray-row-last (lw-polynomial-square-boundary anchor side count))
             (car (lw-polynomial-square-boundary anchor side count)))
      (equal (len (lw-polynomial-square-boundary anchor side count)) (* 4 (+ 1 count)))))
 :hints (("Goal"
 :use (lw-polynomial-domain-grid-data
       (:instance lw-ray-grid-perimeter-data (rows (lw-polynomial-domain-grid anchor side count)) (width (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-square-boundary lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-boundary-values
 (implies (and (lw-complexp anchor) (rationalp side) (posp count))
 (equal (lw-polynomial-path-values coefficients (lw-polynomial-square-boundary anchor side count))
        (lw-ray-grid-perimeter (lw-polynomial-grid coefficients anchor side count))))
 :hints (("Goal"
 :use (lw-polynomial-domain-grid-data lw-polynomial-grid-as-domain-map
       (:instance lw-polynomial-grid-map-perimeter (rows (lw-polynomial-domain-grid anchor side count)) (width (+ 1 count))))
 :in-theory (union-theories
 '(lw-polynomial-square-boundary lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-grid-boundary-as-polygon
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor) (rationalp side) (posp count))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid coefficients anchor side count))
        (lw-ray-polygon-index (lw-polynomial-path-values coefficients (lw-polynomial-square-boundary anchor side count)))))
 :hints (("Goal"
 :use (lw-polynomial-grid-data lw-polynomial-square-boundary-values
       (:instance lw-pgm-positive-length (points (lw-polynomial-grid coefficients anchor side count)))
       (:instance lw-ray-grid-perimeter-index (rows (lw-polynomial-grid coefficients anchor side count)) (width (+ 1 count))))
 :in-theory (union-theories
 '( lw-pgm-left-commutes lw-pgm-left-distributes lw-pgm-fold-constants lw-pgm-times-negative lw-pgm-negative-times lw-pgm-zero-times lw-pgm-minus-one lw-pgm-double-negative lw-pgm-add-cancel lw-pgm-double lw-pgm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
