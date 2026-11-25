; Convexity and affine coordinates for rational complex segments.
(in-package "ACL2")
(include-book "cauchy-polynomials")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub
 lw-complex-mul lw-complex-scale lw-complex-diskp lw-diskp)))
(local (defthm lw-csg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-csg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-csg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-csg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-csg-times-negative (a b) (b a)))
                 :in-theory (disable lw-csg-times-negative)))))

(local (defthm lw-csg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-csg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-csg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-csg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-csg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-csg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-csg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-csg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-csg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-csg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-csg-left-commutes)))))
(defun lw-complex-segment (left right parameter)
 (lw-complex-add (lw-complex-scale (- 1 parameter) left) (lw-complex-scale parameter right)))
(local (in-theory (disable lw-complex-segment)))
(defthm lw-complex-segment-rational
 (implies (and (lw-complexp left) (lw-complexp right) (rationalp parameter))
 (lw-complexp (lw-complex-segment left right parameter)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-segment lw-complex-add lw-complex-scale lw-csg-left-commutes lw-csg-left-distributes lw-csg-fold-constants lw-csg-times-negative lw-csg-negative-times lw-csg-zero-times lw-csg-minus-one lw-csg-double-negative lw-csg-add-cancel lw-csg-double lw-csg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-complex-segment-endpoints
 (implies (and (lw-complexp left) (lw-complexp right))
 (and (equal (lw-complex-segment left right 0) left)
      (equal (lw-complex-segment left right 1) right)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-segment lw-complex-add lw-complex-scale lw-csg-left-commutes lw-csg-left-distributes lw-csg-fold-constants lw-csg-times-negative lw-csg-negative-times lw-csg-zero-times lw-csg-minus-one lw-csg-double-negative lw-csg-add-cancel lw-csg-double lw-csg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-complex-segment-affine
 (implies (and (lw-complexp left) (lw-complexp right) (rationalp parameter))
 (equal (lw-complex-segment left right parameter)
        (lw-complex-add left (lw-complex-mul (lw-complex-sub right left) (cons parameter 0)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-segment lw-complex-add lw-complex-scale lw-complex-mul lw-complex-sub lw-csg-left-commutes lw-csg-left-distributes lw-csg-fold-constants lw-csg-times-negative lw-csg-negative-times lw-csg-zero-times lw-csg-minus-one lw-csg-double-negative lw-csg-add-cancel lw-csg-double lw-csg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-complex-segment-centered
 (implies (and (lw-complexp left) (lw-complexp right) (lw-complexp center) (rationalp parameter))
 (equal (lw-complex-sub (lw-complex-segment left right parameter) center)
        (lw-complex-segment (lw-complex-sub left center) (lw-complex-sub right center) parameter)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-segment lw-complex-add lw-complex-scale lw-complex-sub lw-csg-left-commutes lw-csg-left-distributes lw-csg-fold-constants lw-csg-times-negative lw-csg-negative-times lw-csg-zero-times lw-csg-minus-one lw-csg-double-negative lw-csg-add-cancel lw-csg-double lw-csg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-complex-segment-disk
 (implies (and (lw-complex-diskp left radius) (lw-complex-diskp right radius)
 (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-complex-diskp (lw-complex-segment left right parameter) radius))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-data (point left))
       (:instance lw-complex-disk-data (point right))
       (:instance lw-complex-scale-disk (point left) (factor (- 1 parameter)))
       (:instance lw-complex-scale-disk (point right) (factor parameter))
       (:instance lw-complex-add-disk (left (lw-complex-scale (- 1 parameter) left)) (right (lw-complex-scale parameter right))
        (radius (* (- 1 parameter) radius)) (other-radius (* parameter radius))))
 :in-theory (union-theories
 '(lw-complex-segment abs lw-csg-left-commutes lw-csg-left-distributes lw-csg-fold-constants lw-csg-times-negative lw-csg-negative-times lw-csg-zero-times lw-csg-minus-one lw-csg-double-negative lw-csg-add-cancel lw-csg-double lw-csg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
(defthm lw-complex-segment-centered-disk
 (implies (and (lw-complexp left) (lw-complexp right) (lw-complexp center)
 (lw-complex-diskp (lw-complex-sub left center) radius)
 (lw-complex-diskp (lw-complex-sub right center) radius)
 (rationalp parameter) (<= 0 parameter) (<= parameter 1))
 (lw-complex-diskp (lw-complex-sub (lw-complex-segment left right parameter) center) radius))
 :hints (("Goal"
 :use ((:instance lw-complex-segment-disk (left (lw-complex-sub left center)) (right (lw-complex-sub right center))))
 :in-theory (union-theories
 '(lw-complex-segment-centered lw-csg-left-commutes lw-csg-left-distributes lw-csg-fold-constants lw-csg-times-negative lw-csg-negative-times lw-csg-zero-times lw-csg-minus-one lw-csg-double-negative lw-csg-add-cancel lw-csg-double lw-csg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
