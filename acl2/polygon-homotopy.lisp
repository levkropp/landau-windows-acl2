; Finite rational polygon homotopy with checked nonzero collars.
(in-package "ACL2")
(include-book "grid-root-search")
(local (in-theory (disable lw-complexp lw-complex-det lw-complex-dot lw-complex-positive-halfplanep
 lw-ray-crossing lw-ray-triangle-index lw-ray-path-index lw-ray-path-last lw-ray-polygon-index
 lw-ray-row-index lw-ray-row-last lw-ray-pointsp lw-ray-row-avoids lw-ray-row-near-check lw-ray-row-strip-index)))
(local (defthm lw-phm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-phm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-phm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-phm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-phm-times-negative (a b) (b a)))
                 :in-theory (disable lw-phm-times-negative)))))

(local (defthm lw-phm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-phm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-phm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-phm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-phm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-phm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-phm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-phm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-phm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-phm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-phm-left-commutes)))))
(defun lw-ray-close-polygon (points)
 (if (endp points) nil (cons (car points) (append (cdr points) (list (car points))))))
(defun lw-ray-polygon-homotopy-check (bottom top epsilon)
 (and (lw-ray-pointsp bottom) (lw-ray-pointsp top)
      (consp bottom) (consp top) (equal (len bottom) (len top))
      (rationalp epsilon) (< 0 epsilon)
      (lw-ray-row-avoids bottom epsilon)
      (lw-ray-row-near-check (lw-ray-close-polygon bottom) (lw-ray-close-polygon top) epsilon)))
(local (in-theory (disable lw-ray-close-polygon lw-ray-polygon-homotopy-check)))

(local (defthm lw-phm-pointsp-append
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right))
 (lw-ray-pointsp (append left right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-ray-pointsp append endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-phm-length-append
 (implies (true-listp left) (equal (len (append left right)) (+ (len left) (len right))))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append len true-listp endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-phm-pointsp-true-list
 (implies (lw-ray-pointsp points) (true-listp points))
 :hints (("Goal" :induct (lw-ray-pointsp points)
 :in-theory (union-theories
 '(lw-ray-pointsp true-listp endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-phm-avoids-append
 (equal (lw-ray-row-avoids (append left right) epsilon)
 (and (lw-ray-row-avoids left epsilon) (lw-ray-row-avoids right epsilon)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(append lw-ray-row-avoids endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-close-polygon-data
 (implies (and (lw-ray-pointsp points) (consp points))
 (and (consp (lw-ray-close-polygon points))
      (lw-ray-pointsp (lw-ray-close-polygon points))
      (equal (car (lw-ray-close-polygon points)) (car points))
      (equal (len (lw-ray-close-polygon points)) (+ 1 (len points)))))
 :hints (("Goal" :use ((:instance lw-phm-pointsp-append (left (cdr points)) (right (list (car points)))))
 :in-theory (union-theories
 '(lw-ray-close-polygon lw-ray-pointsp lw-phm-pointsp-true-list lw-phm-length-append append len endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-close-polygon-last
 (implies (consp points)
 (equal (lw-ray-row-last (lw-ray-close-polygon points)) (car points)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-ray-close-polygon lw-ray-row-last lw-ray-path-last-append lw-ray-path-last append endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-close-polygon-index
 (equal (lw-ray-row-index (lw-ray-close-polygon points)) (lw-ray-polygon-index points))
 :hints (("Goal"
 :use ((:instance lw-ray-crossing-data (a (lw-ray-path-last (car points) (cdr points))) (b (car points))))
 :in-theory (union-theories
 '(lw-ray-close-polygon lw-ray-row-index lw-ray-polygon-index lw-ray-path-index-append lw-ray-path-index lw-ray-path-index-integer append endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-close-polygon-avoids
 (implies (lw-ray-row-avoids points epsilon)
 (lw-ray-row-avoids (lw-ray-close-polygon points) epsilon))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-ray-close-polygon lw-phm-avoids-append lw-ray-row-avoids endp lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-ray-polygon-homotopy-invariant
 (implies (lw-ray-polygon-homotopy-check bottom top epsilon)
 (equal (lw-ray-polygon-index bottom) (lw-ray-polygon-index top)))
 :hints (("Goal"
 :use ((:instance lw-ray-close-polygon-data (points bottom))
       (:instance lw-ray-close-polygon-data (points top))
       (:instance lw-ray-close-polygon-last (points bottom))
       (:instance lw-ray-close-polygon-last (points top))
       (:instance lw-ray-close-polygon-index (points bottom))
       (:instance lw-ray-close-polygon-index (points top))
       (:instance lw-ray-close-polygon-avoids (points bottom))
       (:instance lw-ray-row-near-avoids-index-zero
          (bottom (lw-ray-close-polygon bottom)) (top (lw-ray-close-polygon top)))
       (:instance lw-ray-row-strip-boundary
          (bottom (lw-ray-close-polygon bottom)) (top (lw-ray-close-polygon top)))
       (:instance lw-ray-polygon-index-integer (points bottom))
       (:instance lw-ray-polygon-index-integer (points top))
       (:instance lw-ray-crossing-data (a (car bottom)) (b (car top))))
 :in-theory (union-theories
 '(lw-ray-polygon-homotopy-check lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-ray-polygon-homotopy-nonzero
 (implies (and (lw-ray-polygon-homotopy-check bottom top epsilon)
               (not (equal (lw-ray-polygon-index bottom) 0)))
 (not (equal (lw-ray-polygon-index top) 0)))
 :hints (("Goal" :use lw-ray-polygon-homotopy-invariant
 :in-theory (union-theories
 '( lw-phm-left-commutes lw-phm-left-distributes lw-phm-fold-constants lw-phm-times-negative lw-phm-negative-times lw-phm-zero-times lw-phm-minus-one lw-phm-double-negative lw-phm-add-cancel lw-phm-double lw-phm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
