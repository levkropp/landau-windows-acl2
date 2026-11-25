; Integer positive-ray crossings, with a fixed convention at vertices on the ray.
(in-package "ACL2")
(include-book "complex-orientation")
(local (in-theory (disable lw-complexp lw-complex-det lw-complex-dot lw-complex-positive-halfplanep)))
(local (defthm lw-rcr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rcr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rcr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rcr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rcr-times-negative (a b) (b a)))
                 :in-theory (disable lw-rcr-times-negative)))))

(local (defthm lw-rcr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rcr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rcr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rcr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rcr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rcr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rcr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rcr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rcr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rcr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rcr-left-commutes)))))
(defun lw-ray-crossing (a b)
 (if (and (<= (cdr a) 0) (< 0 (cdr b)) (< 0 (lw-complex-det a b))) 1
  (if (and (<= (cdr b) 0) (< 0 (cdr a)) (< (lw-complex-det a b) 0)) -1 0)))
(defun lw-ray-triangle-index (a b c)
 (+ (lw-ray-crossing a b) (lw-ray-crossing b c) (lw-ray-crossing c a)))
(local (in-theory (disable lw-ray-crossing lw-ray-triangle-index)))

(defthm lw-ray-crossing-data
 (and (integerp (lw-ray-crossing a b)) (<= -1 (lw-ray-crossing a b)) (<= (lw-ray-crossing a b) 1))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-crossing lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-ray-crossing-self
 (implies (lw-complexp point) (equal (lw-ray-crossing point point) 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-crossing lw-complex-det-self lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-ray-crossing-reverse
 (implies (and (lw-complexp a) (lw-complexp b))
 (equal (lw-ray-crossing b a) (- (lw-ray-crossing a b))))
 :hints (("Goal" :use (lw-complex-det-reverse lw-complex-orientation-rational)
 :in-theory (union-theories
 '(lw-ray-crossing lw-complexp lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)
(defthm lw-ray-triangle-index-integer
 (integerp (lw-ray-triangle-index a b c))
 :hints (("Goal"
 :use (lw-ray-crossing-data
       (:instance lw-ray-crossing-data (a b) (b c))
       (:instance lw-ray-crossing-data (a c) (b a)))
 :in-theory (union-theories
 '(lw-ray-triangle-index lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(defthm lw-ray-triangle-index-cyclic
 (equal (lw-ray-triangle-index b c a) (lw-ray-triangle-index a b c))
 :hints (("Goal"
 :use (lw-ray-crossing-data
       (:instance lw-ray-crossing-data (a b) (b c))
       (:instance lw-ray-crossing-data (a c) (b a)))
 :in-theory (union-theories
 '(lw-ray-triangle-index lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rcr-positive-weights
 (implies (and (rationalp u) (< 0 u) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
 (rationalp x) (<= 0 x) (rationalp y) (<= 0 y) (rationalp z) (<= 0 z)
 (equal (+ (* u x) (* v y) (* w z)) 0))
 (and (equal x 0) (equal y 0) (equal z 0)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-rcr-negative-weights
 (implies (and (rationalp u) (< 0 u) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
 (rationalp x) (<= x 0) (rationalp y) (<= y 0) (rationalp z) (<= z 0)
 (equal (+ (* u x) (* v y) (* w z)) 0))
 (and (equal x 0) (equal y 0) (equal z 0)))
 :hints (("Goal"
 :use ((:instance lw-rcr-positive-weights (x (- x)) (y (- y)) (z (- z))))
 :in-theory (union-theories
 '( lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(local (defthm lw-rcr-third-nonnegative
 (implies (and (rationalp u) (< 0 u) (rationalp v) (<= v 0) (rationalp w) (<= w 0)
 (rationalp x) (rationalp y) (<= 0 y) (rationalp z) (<= 0 z)
 (equal (+ (* u x) (* v y) (* w z)) 0))
 (<= 0 x))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-rcr-third-nonpositive
 (implies (and (rationalp u) (< 0 u) (rationalp v) (<= v 0) (rationalp w) (<= w 0)
 (rationalp x) (rationalp y) (<= y 0) (rationalp z) (<= z 0)
 (equal (+ (* u x) (* v y) (* w z)) 0))
 (<= x 0))
 :hints (("Goal"
 :use ((:instance lw-rcr-third-nonnegative (x (- x)) (y (- y)) (z (- z))))
 :in-theory (union-theories
 '( lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))
(local (defthm lw-rcr-negative-first-strict
 (implies (and (rationalp u) (<= u 0) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
 (rationalp x) (rationalp y) (<= 0 y) (rationalp z) (<= 0 z)
 (or (< 0 y) (< 0 z)) (equal (+ (* u x) (* v y) (* w z)) 0))
 (< 0 x))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-rcr-negative-first-negative
 (implies (and (rationalp u) (<= u 0) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
 (rationalp x) (rationalp y) (<= y 0) (rationalp z) (<= z 0)
 (or (< y 0) (< z 0)) (equal (+ (* u x) (* v y) (* w z)) 0))
 (< x 0))
 :hints (("Goal"
 :use ((:instance lw-rcr-negative-first-strict (x (- x)) (y (- y)) (z (- z))))
 :in-theory (union-theories
 '( lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))


(local (defthm lw-rcr-halfplane-data
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b) (lw-complex-positive-halfplanep h c))
 (and (lw-complexp h) (lw-complexp a) (lw-complexp b) (lw-complexp c)
      (rationalp (cdr a)) (rationalp (cdr b)) (rationalp (cdr c))
      (rationalp (lw-complex-dot h a)) (< 0 (lw-complex-dot h a)) (rationalp (lw-complex-dot h b)) (< 0 (lw-complex-dot h b)) (rationalp (lw-complex-dot h c)) (< 0 (lw-complex-dot h c))
      (rationalp (lw-complex-det b c)) (rationalp (lw-complex-det c a)) (rationalp (lw-complex-det a b))))
 :hints (("Goal"
 :use ((:instance lw-complex-orientation-rational (a h) (b a))
       (:instance lw-complex-orientation-rational (a h) (b b))
       (:instance lw-complex-orientation-rational (a h) (b c))
       (:instance lw-complex-orientation-rational (a b) (b c))
       (:instance lw-complex-orientation-rational (a c) (b a))
       lw-complex-orientation-rational)
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-complexp lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-rcr-halfplane-positive-dets
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b) (lw-complex-positive-halfplanep h c) (<= 0 (lw-complex-det b c)) (<= 0 (lw-complex-det c a)) (<= 0 (lw-complex-det a b)))
 (and (equal (lw-complex-det b c) 0) (equal (lw-complex-det c a) 0) (equal (lw-complex-det a b) 0)))
 :hints (("Goal"
 :use (lw-rcr-halfplane-data lw-complex-det-dot-relation
       (:instance lw-rcr-positive-weights (u (lw-complex-dot h a)) (v (lw-complex-dot h b)) (w (lw-complex-dot h c)) (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b))))
 :in-theory (union-theories
 '( lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-rcr-halfplane-negative-dets
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b) (lw-complex-positive-halfplanep h c) (<= (lw-complex-det b c) 0) (<= (lw-complex-det c a) 0) (<= (lw-complex-det a b) 0))
 (and (equal (lw-complex-det b c) 0) (equal (lw-complex-det c a) 0) (equal (lw-complex-det a b) 0)))
 :hints (("Goal"
 :use (lw-rcr-halfplane-data lw-complex-det-dot-relation
       (:instance lw-rcr-negative-weights (u (lw-complex-dot h a)) (v (lw-complex-dot h b)) (w (lw-complex-dot h c)) (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b))))
 :in-theory (union-theories
 '( lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-rcr-one-positive-y
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b) (lw-complex-positive-halfplanep h c) (< 0 (cdr a)) (<= (cdr b) 0) (<= (cdr c) 0))
 (equal (lw-ray-triangle-index a b c) 0))
 :hints (("Goal"
 :use (lw-rcr-halfplane-data lw-complex-det-y-relation lw-rcr-halfplane-positive-dets lw-rcr-halfplane-negative-dets
       (:instance lw-rcr-third-nonnegative (u (cdr a)) (v (cdr b)) (w (cdr c)) (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b)))
       (:instance lw-rcr-third-nonpositive (u (cdr a)) (v (cdr b)) (w (cdr c)) (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b))))
 :in-theory (union-theories
 '(lw-ray-triangle-index lw-ray-crossing lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-rcr-one-nonpositive-y
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b) (lw-complex-positive-halfplanep h c) (<= (cdr a) 0) (< 0 (cdr b)) (< 0 (cdr c)))
 (equal (lw-ray-triangle-index a b c) 0))
 :hints (("Goal"
 :use (lw-rcr-halfplane-data lw-complex-det-y-relation lw-rcr-halfplane-positive-dets lw-rcr-halfplane-negative-dets
       (:instance lw-rcr-negative-first-strict (u (cdr a)) (v (cdr b)) (w (cdr c)) (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b)))
       (:instance lw-rcr-negative-first-negative (u (cdr a)) (v (cdr b)) (w (cdr c)) (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b))))
 :in-theory (union-theories
 '(lw-ray-triangle-index lw-ray-crossing lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-rcr-same-y-side
 (implies (or (and (< 0 (cdr a)) (< 0 (cdr b)) (< 0 (cdr c)))
              (and (<= (cdr a) 0) (<= (cdr b) 0) (<= (cdr c) 0)))
 (equal (lw-ray-triangle-index a b c) 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-ray-triangle-index lw-ray-crossing lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-ray-triangle-halfplane-zero
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b) (lw-complex-positive-halfplanep h c)) (equal (lw-ray-triangle-index a b c) 0))
 :hints (("Goal"
 :use (lw-rcr-one-positive-y lw-rcr-one-nonpositive-y lw-rcr-same-y-side
       (:instance lw-rcr-one-positive-y (a b) (b c) (c a))
       (:instance lw-rcr-one-positive-y (a c) (b a) (c b))
       (:instance lw-rcr-one-nonpositive-y (a b) (b c) (c a))
       (:instance lw-rcr-one-nonpositive-y (a c) (b a) (c b))
       lw-ray-triangle-index-cyclic
       (:instance lw-ray-triangle-index-cyclic (a b) (b c) (c a)))
 :in-theory (union-theories
 '( lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-rcr-anchor-positive
 (implies (lw-complex-positive-halfplanep h point) (lw-complex-positive-halfplanep h h))
 :hints (("Goal"
 :cases ((equal h (cons 0 0)))
 :use ((:instance lw-complex-norm-square-positive (point h))
       (:instance lw-complex-dot-self (point h)))
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-complexp lw-complex-dot lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-ray-halfplane-potential
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b))
 (equal (lw-ray-crossing a b) (- (lw-ray-crossing h b) (lw-ray-crossing h a))))
 :hints (("Goal"
 :use ((:instance lw-rcr-anchor-positive (point a))
       (:instance lw-ray-triangle-halfplane-zero (a h) (b a) (c b))
       (:instance lw-ray-crossing-reverse (a h) (b b))
       (:instance lw-ray-crossing-data (a h) (b a))
       (:instance lw-ray-crossing-data (a h) (b b))
       lw-ray-crossing-data)
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-ray-triangle-index lw-rcr-left-commutes lw-rcr-left-distributes lw-rcr-fold-constants lw-rcr-times-negative lw-rcr-negative-times lw-rcr-zero-times lw-rcr-minus-one lw-rcr-double-negative lw-rcr-add-cancel lw-rcr-double lw-rcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


