(in-package "ACL2")

(include-book "polynomial-factor-winding")
(include-book "polynomial-normalized-factorization")
(include-book "polynomial-square-clearance")

; The coarse polynomial certificate generates a complete factor family away
; from the square boundary, without assuming clearance for the factors.

(local (defthm lw-pbf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pbf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pbf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pbf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pbf-times-negative (a b) (b a)))
                 :in-theory (disable lw-pbf-times-negative)))))

(local (defthm lw-pbf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pbf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pbf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pbf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pbf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pbf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pbf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pbf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pbf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pbf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pbf-left-commutes)))))
(defun lw-polynomial-square-factor-error (coefficients count) (* 1/4 (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count)))
(defun lw-polynomial-square-factor-roots (coefficients count)
 (lw-polynomial-normalized-factor-roots coefficients 2 (lw-polynomial-square-factor-error coefficients count)))

(local (defthm lw-pbf-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-pbf-empty-coefficients
 (implies (and (lw-complex-coefficientsp coefficients) (not (consp coefficients))) (equal coefficients nil))
 :rule-classes nil
 :hints (("Goal" :expand ((lw-complex-coefficientsp coefficients)) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pbf-empty-polynomial
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-polynomial nil point offset)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-checked-square-normalized-nonzero
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count))
  (and (consp (lw-polynomial-trim coefficients)) (not (equal (lw-polynomial-leading (lw-polynomial-trim coefficients)) (cons 0 0)))))
 :hints (("Goal"
  :use ((:instance lw-polynomial-square-clearance-data (anchor (cons -1 -1)) (side 2))
        (:instance lw-polynomial-unit-square-excludes-clearance (point (cons -1 -1)))
        lw-polynomial-trim-valid lw-polynomial-trim-nonzero-leading
        (:instance lw-pbf-empty-coefficients (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-trim-evaluation (point (cons -1 -1)) (offset 0))
        (:instance lw-complex-zero-disk (radius (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pbf-empty-polynomial (:executable-counterpart lw-unit-square-pointp) (:executable-counterpart lw-complexp) lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-square-factor-error-data
 (implies (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
  (and (rationalp (lw-polynomial-square-factor-error coefficients count)) (< 0 (lw-polynomial-square-factor-error coefficients count))
       (<= (lw-polynomial-square-factor-error coefficients count) (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))
       (<= (* 3 (lw-polynomial-square-factor-error coefficients count)) (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))))
 :hints (("Goal" :use ((:instance lw-polynomial-square-clearance-data (anchor (cons -1 -1)) (side 2)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-factor-error lw-pbf-product-rational lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-factor-data
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count))
  (and (lw-ray-pointsp (lw-polynomial-square-factor-roots coefficients count))
       (equal (len (lw-polynomial-square-factor-roots coefficients count)) (len (lw-polynomial-without-leading (lw-polynomial-trim coefficients))))
       (lw-complexp (lw-polynomial-leading (lw-polynomial-trim coefficients))) (not (equal (lw-polynomial-leading (lw-polynomial-trim coefficients)) (cons 0 0)))))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-error-data lw-polynomial-checked-square-normalized-nonzero lw-polynomial-trim-valid
        (:instance lw-polynomial-leading-valid (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-normalized-factor-roots-data (bound 2) (epsilon (lw-polynomial-square-factor-error coefficients count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-factor-roots lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-factor-approximation
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-unit-square-pointp point))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                   (lw-polynomial-linear-factor-value (lw-polynomial-square-factor-roots coefficients count) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)) (lw-polynomial-square-factor-error coefficients count)))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-error-data lw-unit-square-point-annulus
        (:instance lw-polynomial-normalized-approximate-factorization (bound 2) (epsilon (lw-polynomial-square-factor-error coefficients count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-factor-roots lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-pbf-zero-products
 (and (equal (lw-complex-mul (cons 0 0) point) (cons 0 0))
      (equal (lw-complex-mul point (cons 0 0)) (cons 0 0)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-mul lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-factor-member-zero
 (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp root) (member-equal root roots))
  (equal (lw-polynomial-linear-factor-value roots leading root) (cons 0 0)))
 :hints (("Goal" :induct (lw-polynomial-linear-factor-value roots leading root)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-linear-factor-value) lw-polynomial-linear-factor-value member-equal lw-ray-pointsp lw-complex-sub-zero lw-pbf-zero-products endp lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defun lw-pbf-boundary-root (roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) nil
  (if (lw-unit-square-pointp (car roots)) (car roots) (lw-pbf-boundary-root (cdr roots))))))

(local (defthm lw-pbf-boundary-root-data
 (implies (consp (lw-pbf-boundary-root roots))
  (and (member-equal (lw-pbf-boundary-root roots) roots) (lw-unit-square-pointp (lw-pbf-boundary-root roots))))
 :hints (("Goal" :induct (lw-pbf-boundary-root roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-pbf-boundary-root) lw-pbf-boundary-root member-equal endp lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pbf-boundary-root-complete
 (implies (and (lw-ray-pointsp roots) (not (lw-unit-square-roots-awayp roots)))
  (consp (lw-pbf-boundary-root roots)))
 :hints (("Goal" :induct (lw-pbf-boundary-root roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-pbf-boundary-root) lw-pbf-boundary-root lw-ray-pointsp lw-unit-square-roots-awayp lw-complexp endp lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pbf-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-square-factors-away
 (implies (and (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count))
  (lw-unit-square-roots-awayp (lw-polynomial-square-factor-roots coefficients count)))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-data lw-polynomial-square-factor-error-data
        (:instance lw-polynomial-square-clearance-data (anchor (cons -1 -1)) (side 2))
        (:instance lw-pbf-boundary-root-data (roots (lw-polynomial-square-factor-roots coefficients count)))
        (:instance lw-pbf-boundary-root-complete (roots (lw-polynomial-square-factor-roots coefficients count)))
        (:instance lw-polynomial-factor-member-zero (roots (lw-polynomial-square-factor-roots coefficients count)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (root (lw-pbf-boundary-root (lw-polynomial-square-factor-roots coefficients count))))
        (:instance lw-polynomial-square-factor-approximation (point (lw-pbf-boundary-root (lw-polynomial-square-factor-roots coefficients count))))
        (:instance lw-polynomial-unit-square-excludes-clearance (point (lw-pbf-boundary-root (lw-polynomial-square-factor-roots coefficients count))))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-polynomial coefficients (lw-pbf-boundary-root (lw-polynomial-square-factor-roots coefficients count)) 0)) (radius (lw-polynomial-square-factor-error coefficients count)) (cap (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pbf-point-type lw-complex-sub-zero lw-complex-polynomial-rational lw-pbf-left-commutes lw-pbf-left-distributes lw-pbf-fold-constants lw-pbf-times-negative lw-pbf-negative-times lw-pbf-zero-times lw-pbf-minus-one lw-pbf-double-negative lw-pbf-add-cancel lw-pbf-double lw-pbf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
