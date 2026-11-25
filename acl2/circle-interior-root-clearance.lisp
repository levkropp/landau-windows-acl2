(in-package "ACL2")

(include-book "circle-pole-split")
(include-book "polynomial-pole-sum-clearance")

; The finite interior list determines one positive margin to the circle.

(local (defthm lw-cir-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cir-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cir-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cir-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cir-times-negative (a b) (b a)))
                 :in-theory (disable lw-cir-times-negative)))))

(local (defthm lw-cir-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cir-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cir-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cir-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cir-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cir-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cir-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cir-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cir-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cir-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cir-left-commutes)))))

(defun lw-circle-root-norm-max (roots)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     0
   (max (lw-complex-norm-square (car roots)) (lw-circle-root-norm-max (cdr roots)))))

(defun lw-circle-interior-root-clearance (roots radius)
 (* 1/8 (- (* radius radius) (lw-circle-root-norm-max roots)) (/ radius)))

(local (defthm lw-cir-positive-square
 (implies (and (rationalp a) (< 0 a)) (< 0 (* a a)))
 :rule-classes (:rewrite :linear)
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(defthm lw-circle-root-norm-max-data
 (implies (lw-ray-pointsp roots)
  (and (rationalp (lw-circle-root-norm-max roots)) (<= 0 (lw-circle-root-norm-max roots))))
 :hints (("Goal" :induct (lw-circle-root-norm-max roots)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-root-norm-max lw-ray-pointsp lw-complex-norm-square-valid max endp lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-circle-interior-max-norm
 (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)) (< (lw-circle-root-norm-max (lw-circle-pole-roots roots radius)) (* radius radius)))
 :hints (("Goal" :induct (lw-circle-pole-roots roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-pole-roots lw-circle-root-norm-max max lw-ray-pointsp lw-complex-norm-square-valid lw-cir-positive-square endp lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cir-rational-inverse
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-cir-rational-product
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cir-gap-data
 (implies (and (rationalp norm) (<= 0 norm) (rationalp radius) (< 0 radius) (< norm (* radius radius)))
  (let ((gap (* 1/8 (- (* radius radius) norm) (/ radius))))
   (and (rationalp gap) (< 0 gap) (< (* 2 gap) radius)
        (<= norm (* (- radius (* 2 gap)) (- radius (* 2 gap)))))))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-positive (value radius))
        (:instance lw-cir-inverse-factor (divisor radius) (coefficient (- (* radius radius) norm)))
        (:instance lw-cir-inverse-factor (divisor radius) (coefficient radius))
        (:instance lw-cir-positive-product (a (- (* radius radius) norm)) (b (/ radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cir-rational-inverse lw-cir-rational-product lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t))))

(defthm lw-circle-interior-root-clearance-data
 (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius))
  (and (rationalp (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius)) (< 0 (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius)) (< (* 2 (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius)) radius)
       (<= (lw-circle-root-norm-max (lw-circle-pole-roots roots radius)) (* (- radius (* 2 (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius))) (- radius (* 2 (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius)))))))
 :hints (("Goal"
  :use (lw-circle-interior-max-norm lw-circle-pole-split-valid
        (:instance lw-circle-root-norm-max-data (roots (lw-circle-pole-roots roots radius)))
        (:instance lw-cir-gap-data (norm (lw-circle-root-norm-max (lw-circle-pole-roots roots radius)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-root-clearance lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-cir-square-scale
 (implies (and (rationalp factor) (lw-complexp root))
  (equal (lw-complex-norm-square (lw-complex-scale factor root))
         (* factor factor (lw-complex-norm-square root))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complexp lw-complex-norm-square lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cir-radius-has-norm
 (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1) (rationalp radius))
  (and (lw-complexp (lw-complex-scale radius point))
       (equal (lw-complex-norm-square (lw-complex-scale radius point)) (* radius radius))))
 :hints (("Goal" :use ((:instance lw-cir-square-scale (factor radius) (root point))
        (:instance lw-complex-scale-rational (factor radius)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cir-shift-back
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-add (lw-complex-sub a b) b) a))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cir-margin-add
 (implies (and (rationalp gap) (rationalp radius))
  (equal (+ gap (- radius (* 2 gap))) (- radius gap)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-cir-distance-from-interior
 (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (lw-complexp root) (rationalp radius) (< 0 radius) (rationalp gap) (< 0 gap) (< (* 2 gap) radius)
               (<= (lw-complex-norm-square root) (* (- radius (* 2 gap)) (- radius (* 2 gap)))))
  (not (lw-complex-diskp (lw-complex-sub (lw-complex-scale radius point) root) gap)))
 :hints (("Goal"
  :use (lw-cir-radius-has-norm
        (:instance lw-complex-disk-norm-square (point root) (radius (- radius (* 2 gap))))
        (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-scale radius point) root)) (radius gap)
         (right root) (other-radius (- radius (* 2 gap))))
        (:instance lw-cir-shift-back (a (lw-complex-scale radius point)) (b root))
        (:instance lw-complex-disk-norm-square (point (lw-complex-scale radius point)) (radius (- radius gap))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cir-margin-add lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-cir-list-clearance
 (implies (and (lw-ray-pointsp roots) (lw-complexp point) (equal (lw-complex-norm-square point) 1)
               (rationalp radius) (< 0 radius) (rationalp gap) (< 0 gap) (< (* 2 gap) radius)
               (<= (lw-circle-root-norm-max roots) (* (- radius (* 2 gap)) (- radius (* 2 gap)))))
  (lw-polynomial-root-clearancesp roots (lw-complex-scale radius point) gap))
 :hints (("Goal" :induct (lw-circle-root-norm-max roots)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-root-norm-max lw-polynomial-root-clearancesp max lw-ray-pointsp lw-complex-norm-square-valid lw-cir-distance-from-interior endp lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-interior-root-clearances-generated
 (implies (and (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)) (lw-complexp point) (equal (lw-complex-norm-square point) 1))
  (lw-polynomial-root-clearancesp (lw-circle-pole-roots roots radius) (lw-complex-scale radius point) (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius)))
 :hints (("Goal"
  :use (lw-circle-interior-root-clearance-data lw-circle-pole-split-valid
        (:instance lw-cir-list-clearance (roots (lw-circle-pole-roots roots radius)) (gap (lw-circle-interior-root-clearance (lw-circle-pole-roots roots radius) radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cir-left-commutes lw-cir-left-distributes lw-cir-fold-constants lw-cir-times-negative lw-cir-negative-times lw-cir-zero-times lw-cir-minus-one lw-cir-double-negative lw-cir-add-cancel lw-cir-double lw-cir-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
