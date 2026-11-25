; The rectangular grid boundary is an explicit oriented closed polygon.
(in-package "ACL2")
(include-book "polygon-paths")
(local (in-theory (disable lw-complexp lw-ray-crossing lw-ray-path-index lw-ray-path-last
 lw-ray-row-index lw-ray-row-last lw-ray-polygon-index lw-ray-pointsp lw-ray-reverse-points
 lw-ray-gridp lw-ray-grid-left lw-ray-grid-right lw-ray-grid-last-row lw-ray-grid-boundary-index)))
(local (defthm lw-gpm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-gpm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-gpm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-gpm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-gpm-times-negative (a b) (b a)))
                 :in-theory (disable lw-gpm-times-negative)))))

(local (defthm lw-gpm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-gpm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-gpm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-gpm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-gpm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-gpm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-gpm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-gpm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-gpm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-gpm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-gpm-left-commutes)))))
(defun lw-ray-four-path-perimeter (bottom right top left)
 (append bottom (append right (append top left))))
(defun lw-ray-grid-perimeter (rows)
 (lw-ray-four-path-perimeter (car rows) (lw-ray-grid-right rows)
 (lw-ray-reverse-points (lw-ray-grid-last-row rows))
 (lw-ray-reverse-points (lw-ray-grid-left rows))))
(local (in-theory (disable lw-ray-four-path-perimeter lw-ray-grid-perimeter)))

(local (defthm lw-gpm-append-head
 (and (equal (consp (append left right)) (or (consp left) (consp right)))
      (equal (car (append left right)) (if (consp left) (car left) (car right))))
 :hints (("Goal" :expand ((append left right)) :in-theory (union-theories
 '(append endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-gpm-length-natural (natp (len points))
 :hints (("Goal" :induct (len points) :in-theory (union-theories
 '(len endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-gpm-length-append
 (equal (len (append left right)) (+ (len left) (len right)))
 :hints (("Goal" :induct (append left right) :in-theory (union-theories
 '(append len endp lw-gpm-length-natural lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-gpm-polygon-as-row
 (equal (lw-ray-polygon-index points)
 (if (endp points) 0
 (+ (lw-ray-row-index points) (lw-ray-crossing (lw-ray-row-last points) (car points)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-polygon-index lw-ray-row-index lw-ray-row-last endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-four-path-perimeter-index
 (implies (and (lw-ray-pointsp bottom) (lw-ray-pointsp right) (lw-ray-pointsp top) (lw-ray-pointsp left)
 (consp bottom) (consp right) (consp top) (consp left)
 (equal (lw-ray-row-last bottom) (car right))
 (equal (lw-ray-row-last right) (car top))
 (equal (lw-ray-row-last top) (car left))
 (equal (lw-ray-row-last left) (car bottom)))
 (equal (lw-ray-polygon-index (lw-ray-four-path-perimeter bottom right top left))
 (+ (lw-ray-row-index bottom) (lw-ray-row-index right) (lw-ray-row-index top) (lw-ray-row-index left))))
 :hints (("Goal"
 :use ((:instance lw-ray-crossing-self (point (car bottom)))
       (:instance lw-ray-crossing-self (point (car right)))
       (:instance lw-ray-crossing-self (point (car top)))
       (:instance lw-ray-crossing-self (point (car left))))
 :in-theory (union-theories
 '(lw-ray-four-path-perimeter lw-gpm-polygon-as-row lw-ray-row-index-append lw-ray-row-last-append lw-gpm-append-head lw-ray-pointsp lw-ray-row-index-integer endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-gpm-row-nonempty
 (implies (< 0 (len points)) (consp points))
 :hints (("Goal" :in-theory (union-theories
 '(len endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(local (defthm lw-gpm-row-last-step
 (equal (lw-ray-row-last (cons current points))
 (if (endp points) current (lw-ray-row-last points)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-row-last lw-ray-path-last endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-gpm-last-row-step
 (implies (consp (cdr rows)) (equal (lw-ray-grid-last-row rows) (lw-ray-grid-last-row (cdr rows))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-gpm-last-row-base
 (implies (endp (cdr rows)) (equal (lw-ray-grid-last-row rows) (car rows)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-last-row lw-ray-path-last endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-gpm-column-heads
 (and (equal (consp (lw-ray-grid-left rows)) (consp rows))
      (equal (consp (lw-ray-grid-right rows)) (consp rows))
      (implies (consp rows)
       (and (equal (car (lw-ray-grid-left rows)) (caar rows))
            (equal (car (lw-ray-grid-right rows)) (lw-ray-row-last (car rows))))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-grid-left lw-ray-grid-right endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-gpm-grid-sides
 (implies (and (posp width) (lw-ray-gridp rows width) (consp rows))
 (and (lw-ray-pointsp (car rows)) (consp (car rows)) (equal (len (car rows)) width)
      (lw-ray-pointsp (lw-ray-grid-last-row rows)) (consp (lw-ray-grid-last-row rows)) (equal (len (lw-ray-grid-last-row rows)) width)
      (lw-ray-pointsp (lw-ray-grid-left rows)) (consp (lw-ray-grid-left rows)) (equal (len (lw-ray-grid-left rows)) (len rows))
      (lw-ray-pointsp (lw-ray-grid-right rows)) (consp (lw-ray-grid-right rows)) (equal (len (lw-ray-grid-right rows)) (len rows))
      (equal (car (lw-ray-grid-left rows)) (caar rows))
      (equal (car (lw-ray-grid-right rows)) (lw-ray-row-last (car rows)))
      (equal (lw-ray-row-last (lw-ray-grid-left rows)) (car (lw-ray-grid-last-row rows)))
      (equal (lw-ray-row-last (lw-ray-grid-right rows)) (lw-ray-row-last (lw-ray-grid-last-row rows)))))
 :hints (("Goal" :induct (lw-ray-gridp rows width)
 :in-theory (union-theories
 '(lw-ray-gridp lw-ray-grid-left lw-ray-grid-right lw-gpm-column-heads lw-gpm-row-last-step lw-gpm-last-row-step lw-gpm-last-row-base lw-ray-pointsp len lw-gpm-length-natural endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:cases ((consp (cdr rows))) :use ((:instance lw-gpm-row-nonempty (points (car rows)))
         (:instance lw-ray-row-last-complex (points (car rows)))) :do-not-induct t)))
 :rule-classes nil))

(defthm lw-ray-grid-perimeter-data
 (implies (and (posp width) (lw-ray-gridp rows width) (consp rows))
 (and (lw-ray-pointsp (lw-ray-grid-perimeter rows)) (consp (lw-ray-grid-perimeter rows))
      (equal (car (lw-ray-grid-perimeter rows)) (caar rows))
      (equal (lw-ray-row-last (lw-ray-grid-perimeter rows)) (caar rows))
      (equal (len (lw-ray-grid-perimeter rows)) (* 2 (+ width (len rows))))))
 :hints (("Goal" :use lw-gpm-grid-sides
 :in-theory (union-theories
 '(lw-ray-grid-perimeter lw-ray-four-path-perimeter lw-ray-pointsp-append lw-ray-reverse-points-data lw-ray-reverse-points-endpoints lw-ray-row-last-append lw-gpm-append-head lw-gpm-length-append lw-gpm-length-natural endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-ray-grid-perimeter-index
 (implies (and (posp width) (lw-ray-gridp rows width) (consp rows))
 (equal (lw-ray-polygon-index (lw-ray-grid-perimeter rows)) (lw-ray-grid-boundary-index rows)))
 :hints (("Goal"
 :use (lw-gpm-grid-sides
       (:instance lw-ray-four-path-perimeter-index
        (bottom (car rows)) (right (lw-ray-grid-right rows))
        (top (lw-ray-reverse-points (lw-ray-grid-last-row rows)))
        (left (lw-ray-reverse-points (lw-ray-grid-left rows)))))
 :in-theory (union-theories
 '(lw-ray-grid-perimeter lw-ray-grid-boundary-index lw-ray-reverse-points-data lw-ray-reverse-points-endpoints lw-ray-row-index-reverse lw-ray-row-index-integer endp lw-gpm-left-commutes lw-gpm-left-distributes lw-gpm-fold-constants lw-gpm-times-negative lw-gpm-negative-times lw-gpm-zero-times lw-gpm-minus-one lw-gpm-double-negative lw-gpm-add-cancel lw-gpm-double lw-gpm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))
