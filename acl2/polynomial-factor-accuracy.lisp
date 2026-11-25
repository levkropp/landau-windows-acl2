(in-package "ACL2")

(include-book "polynomial-boundary-factors")

; Independently requested factorization accuracy under the same coarse certificate.

(local (defthm lw-pfa-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfa-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfa-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfa-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfa-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfa-times-negative)))))

(local (defthm lw-pfa-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfa-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfa-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfa-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfa-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfa-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfa-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfa-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfa-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfa-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfa-left-commutes)))))

(defun lw-polynomial-square-factor-request (coefficients count tolerance)
 (let ((clearance-request (lw-polynomial-square-factor-error coefficients count)))
  (if (< tolerance clearance-request) tolerance clearance-request)))
(defun lw-polynomial-square-accurate-roots (coefficients count tolerance)
 (lw-polynomial-normalized-factor-roots coefficients 2 (lw-polynomial-square-factor-request coefficients count tolerance)))

(local (defthm lw-pfa-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defun lw-pfa-boundary-root (roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) nil
  (if (lw-unit-square-pointp (car roots)) (car roots) (lw-pfa-boundary-root (cdr roots))))))

(local (defthm lw-pfa-boundary-root-data
 (implies (consp (lw-pfa-boundary-root roots))
  (and (member-equal (lw-pfa-boundary-root roots) roots) (lw-unit-square-pointp (lw-pfa-boundary-root roots))))
 :hints (("Goal" :induct (lw-pfa-boundary-root roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-pfa-boundary-root) lw-pfa-boundary-root member-equal endp lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pfa-boundary-root-complete
 (implies (and (lw-ray-pointsp roots) (not (lw-unit-square-roots-awayp roots)))
  (consp (lw-pfa-boundary-root roots)))
 :hints (("Goal" :induct (lw-pfa-boundary-root roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-pfa-boundary-root) lw-pfa-boundary-root lw-ray-pointsp lw-unit-square-roots-awayp lw-complexp endp lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pfa-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-square-factor-request-data
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count))
  (and (rationalp (lw-polynomial-square-factor-request coefficients count tolerance)) (< 0 (lw-polynomial-square-factor-request coefficients count tolerance)) (<= (lw-polynomial-square-factor-request coefficients count tolerance) tolerance)
       (<= (lw-polynomial-square-factor-request coefficients count tolerance) (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count)) (<= (* 3 (lw-polynomial-square-factor-request coefficients count tolerance)) (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))))
 :hints (("Goal" :use (lw-polynomial-square-factor-error-data)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-factor-request lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-data
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count))
  (and (lw-ray-pointsp (lw-polynomial-square-accurate-roots coefficients count tolerance))
       (equal (len (lw-polynomial-square-accurate-roots coefficients count tolerance)) (len (lw-polynomial-without-leading (lw-polynomial-trim coefficients))))
       (lw-complexp (lw-polynomial-leading (lw-polynomial-trim coefficients))) (not (equal (lw-polynomial-leading (lw-polynomial-trim coefficients)) (cons 0 0)))))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-request-data lw-polynomial-checked-square-normalized-nonzero lw-polynomial-trim-valid
        (:instance lw-polynomial-leading-valid (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-normalized-factor-roots-data (bound 2) (epsilon (lw-polynomial-square-factor-request coefficients count tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-roots lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-disk-approximation
 (implies (and (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complexp point) (lw-complex-diskp point 2))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
    (lw-polynomial-linear-factor-value (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point))
   (lw-polynomial-square-factor-request coefficients count tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-request-data
        (:instance lw-polynomial-normalized-approximate-factorization (bound 2) (epsilon (lw-polynomial-square-factor-request coefficients count tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-roots lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-approximation
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)
               (lw-unit-square-pointp point))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                   (lw-polynomial-linear-factor-value (lw-polynomial-square-accurate-roots coefficients count tolerance) (lw-polynomial-leading (lw-polynomial-trim coefficients)) point)) (lw-polynomial-square-factor-request coefficients count tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-factor-request-data lw-unit-square-point-annulus
        (:instance lw-polynomial-normalized-approximate-factorization (bound 2) (epsilon (lw-polynomial-square-factor-request coefficients count tolerance))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-square-accurate-roots lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-away
 (implies (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count)
               (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count))
  (lw-unit-square-roots-awayp (lw-polynomial-square-accurate-roots coefficients count tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-data lw-polynomial-square-factor-request-data
        (:instance lw-polynomial-square-clearance-data (anchor (cons -1 -1)) (side 2))
        (:instance lw-pfa-boundary-root-data (roots (lw-polynomial-square-accurate-roots coefficients count tolerance)))
        (:instance lw-pfa-boundary-root-complete (roots (lw-polynomial-square-accurate-roots coefficients count tolerance)))
        (:instance lw-polynomial-factor-member-zero (roots (lw-polynomial-square-accurate-roots coefficients count tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))) (root (lw-pfa-boundary-root (lw-polynomial-square-accurate-roots coefficients count tolerance))))
        (:instance lw-polynomial-square-accurate-approximation (point (lw-pfa-boundary-root (lw-polynomial-square-accurate-roots coefficients count tolerance))))
        (:instance lw-polynomial-unit-square-excludes-clearance (point (lw-pfa-boundary-root (lw-polynomial-square-accurate-roots coefficients count tolerance))))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-polynomial coefficients (lw-pfa-boundary-root (lw-polynomial-square-accurate-roots coefficients count tolerance)) 0)) (radius (lw-polynomial-square-factor-request coefficients count tolerance)) (cap (lw-polynomial-square-clearance coefficients (cons -1 -1) 2 count))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pfa-point-type lw-complex-sub-zero lw-complex-polynomial-rational lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-square-accurate-root-residual
 (implies (and (and (rationalp tolerance) (< 0 tolerance) (lw-complex-coefficientsp coefficients) (posp count) (lw-polynomial-square-boundary-check coefficients (cons -1 -1) 2 count)) (lw-complexp root) (lw-complex-diskp root 2)
               (member-equal root (lw-polynomial-square-accurate-roots coefficients count tolerance)))
  (lw-complex-diskp (lw-complex-polynomial coefficients root 0) (lw-polynomial-square-factor-request coefficients count tolerance)))
 :hints (("Goal"
  :use (lw-polynomial-square-accurate-data
        (:instance lw-polynomial-square-accurate-disk-approximation (point root))
        (:instance lw-polynomial-factor-member-zero (roots (lw-polynomial-square-accurate-roots coefficients count tolerance)) (leading (lw-polynomial-leading (lw-polynomial-trim coefficients)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-sub-zero lw-complex-polynomial-rational lw-pfa-left-commutes lw-pfa-left-distributes lw-pfa-fold-constants lw-pfa-times-negative lw-pfa-negative-times lw-pfa-zero-times lw-pfa-minus-one lw-pfa-double-negative lw-pfa-add-cancel lw-pfa-double lw-pfa-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
