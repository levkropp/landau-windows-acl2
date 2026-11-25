(in-package "ACL2")

(include-book "ray-positive-scales")

; The triangle index is determined by the three cyclic determinant signs
; when every edge avoids the origin. Positive collinear edges are allowed.

(local (defthm lw-rts-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rts-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rts-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rts-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rts-times-negative (a b) (b a)))
                 :in-theory (disable lw-rts-times-negative)))))

(local (defthm lw-rts-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rts-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rts-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rts-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rts-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rts-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rts-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rts-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rts-left-commutes)))))

(defun lw-ray-determinant-index (a b c)
 (if (and (< 0 (lw-complex-det a b)) (< 0 (lw-complex-det b c))
          (< 0 (lw-complex-det c a))) 1
  (if (and (< (lw-complex-det a b) 0) (< (lw-complex-det b c) 0)
           (< (lw-complex-det c a) 0)) -1 0)))

(defun lw-ray-safe-edgep (a b)
 (and (lw-complexp a) (lw-complexp b)
      (or (not (equal (lw-complex-det a b) 0)) (< 0 (lw-complex-dot a b)))))

(local (defthm lw-rts-third-nonnegative
 (implies (and (rationalp u) (< 0 u) (rationalp v) (<= v 0) (rationalp w) (<= w 0)
               (rationalp x) (rationalp y) (<= 0 y) (rationalp z) (<= 0 z)
               (equal (+ (* u x) (* v y) (* w z)) 0))
          (<= 0 x))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-third-nonpositive
 (implies (and (rationalp u) (< 0 u) (rationalp v) (<= v 0) (rationalp w) (<= w 0)
               (rationalp x) (rationalp y) (<= y 0) (rationalp z) (<= z 0)
               (equal (+ (* u x) (* v y) (* w z)) 0))
          (<= x 0))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-first-strict
 (implies (and (rationalp u) (<= u 0) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
               (rationalp x) (rationalp y) (<= 0 y) (rationalp z) (<= 0 z)
               (or (< 0 y) (< 0 z)) (equal (+ (* u x) (* v y) (* w z)) 0))
          (< 0 x))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-first-negative
 (implies (and (rationalp u) (<= u 0) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
               (rationalp x) (rationalp y) (<= y 0) (rationalp z) (<= z 0)
               (or (< y 0) (< z 0)) (equal (+ (* u x) (* v y) (* w z)) 0))
          (< x 0))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-positive-weights
 (implies (and (rationalp u) (< 0 u) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
               (rationalp x) (<= 0 x) (rationalp y) (<= 0 y) (rationalp z) (<= 0 z)
               (equal (+ (* u x) (* v y) (* w z)) 0))
          (and (equal x 0) (equal y 0) (equal z 0)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-negative-weights
 (implies (and (rationalp u) (< 0 u) (rationalp v) (< 0 v) (rationalp w) (< 0 w)
               (rationalp x) (<= x 0) (rationalp y) (<= y 0) (rationalp z) (<= z 0)
               (equal (+ (* u x) (* v y) (* w z)) 0))
          (and (equal x 0) (equal y 0) (equal z 0)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rts-one-positive-y
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (< 0 (cdr a)) (<= (cdr b) 0) (<= (cdr c) 0)
               (not (equal (lw-complex-det a b) 0))
               (not (equal (lw-complex-det b c) 0))
               (not (equal (lw-complex-det c a) 0)))
  (equal (lw-ray-triangle-index a b c) (lw-ray-determinant-index a b c)))
 :hints (("Goal"
  :use (lw-complex-det-y-relation lw-complex-orientation-rational
        (:instance lw-complex-orientation-rational (a b) (b c))
        (:instance lw-complex-orientation-rational (a c) (b a))
        (:instance lw-rts-third-nonnegative
          (u (cdr a)) (v (cdr b)) (w (cdr c))
          (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b)))
        (:instance lw-rts-third-nonpositive
          (u (cdr a)) (v (cdr b)) (w (cdr c))
          (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-triangle-index lw-ray-crossing lw-ray-determinant-index lw-complexp lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)) :rule-classes nil))

(local (defthm lw-rts-one-nonpositive-y
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (<= (cdr a) 0) (< 0 (cdr b)) (< 0 (cdr c))
               (not (equal (lw-complex-det a b) 0))
               (not (equal (lw-complex-det b c) 0))
               (not (equal (lw-complex-det c a) 0)))
  (equal (lw-ray-triangle-index a b c) (lw-ray-determinant-index a b c)))
 :hints (("Goal"
  :use (lw-complex-det-y-relation lw-complex-orientation-rational
        (:instance lw-complex-orientation-rational (a b) (b c))
        (:instance lw-complex-orientation-rational (a c) (b a))
        (:instance lw-rts-first-strict
          (u (cdr a)) (v (cdr b)) (w (cdr c))
          (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b)))
        (:instance lw-rts-first-negative
          (u (cdr a)) (v (cdr b)) (w (cdr c))
          (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-triangle-index lw-ray-crossing lw-ray-determinant-index lw-complexp lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)) :rule-classes nil))

(local (defthm lw-rts-axis-det
 (implies (and (equal (cdr a) 0) (equal (cdr b) 0))
          (equal (lw-complex-det a b) 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-det lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-rts-same-y-side
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (not (equal (lw-complex-det a b) 0))
               (not (equal (lw-complex-det b c) 0))
               (not (equal (lw-complex-det c a) 0))
               (or (and (< 0 (cdr a)) (< 0 (cdr b)) (< 0 (cdr c)))
                   (and (<= (cdr a) 0) (<= (cdr b) 0) (<= (cdr c) 0))))
  (equal (lw-ray-triangle-index a b c) (lw-ray-determinant-index a b c)))
 :hints (("Goal"
  :use (lw-complex-det-y-relation lw-complex-orientation-rational
        (:instance lw-complex-orientation-rational (a b) (b c))
        (:instance lw-complex-orientation-rational (a c) (b a))
        (:instance lw-rts-positive-weights
          (u (cdr a)) (v (cdr b)) (w (cdr c))
          (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b)))
        (:instance lw-rts-negative-weights
          (u (cdr a)) (v (cdr b)) (w (cdr c))
          (x (lw-complex-det b c)) (y (lw-complex-det c a)) (z (lw-complex-det a b)))
        (:instance lw-rts-negative-weights
          (u (lw-complex-det b c)) (v (lw-complex-det c a)) (w (lw-complex-det a b))
          (x (cdr a)) (y (cdr b)) (z (cdr c)))
        (:instance lw-rts-negative-weights
          (u (- (lw-complex-det b c))) (v (- (lw-complex-det c a))) (w (- (lw-complex-det a b)))
          (x (cdr a)) (y (cdr b)) (z (cdr c))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-triangle-index lw-ray-crossing lw-ray-determinant-index lw-complexp lw-rts-axis-det lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)) :rule-classes nil))

(local (defthm lw-rts-determinant-cyclic
 (equal (lw-ray-determinant-index b c a) (lw-ray-determinant-index a b c))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-determinant-index lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-triangle-strict-determinants
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (not (equal (lw-complex-det a b) 0))
               (not (equal (lw-complex-det b c) 0))
               (not (equal (lw-complex-det c a) 0)))
  (equal (lw-ray-triangle-index a b c) (lw-ray-determinant-index a b c)))
 :hints (("Goal"
  :use (lw-rts-one-positive-y lw-rts-one-nonpositive-y lw-rts-same-y-side
        (:instance lw-rts-one-positive-y (a b) (b c) (c a))
        (:instance lw-rts-one-positive-y (a c) (b a) (c b))
        (:instance lw-rts-one-nonpositive-y (a b) (b c) (c a))
        (:instance lw-rts-one-nonpositive-y (a c) (b a) (c b))
        lw-ray-triangle-index-cyclic
        (:instance lw-ray-triangle-index-cyclic (a b) (b c) (c a)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-rts-determinant-cyclic lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-rts-zero-det-crossing
 (implies (equal (lw-complex-det a b) 0) (equal (lw-ray-crossing a b) 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-crossing lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-triangle-same-ray-zero
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (equal (lw-complex-det a b) 0) (< 0 (lw-complex-dot a b)))
  (equal (lw-ray-triangle-index a b c) 0))
 :hints (("Goal"
  :use (lw-ray-crossing-same-ray-endpoint
        (:instance lw-ray-crossing-reverse (a a) (b c))
        (:instance lw-ray-crossing-data (a b) (b c)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-triangle-index lw-rts-zero-det-crossing lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-triangle-determinants
 (implies (and (lw-ray-safe-edgep a b) (lw-ray-safe-edgep b c) (lw-ray-safe-edgep c a))
  (equal (lw-ray-triangle-index a b c) (lw-ray-determinant-index a b c)))
 :hints (("Goal"
  :use (lw-ray-triangle-strict-determinants lw-ray-triangle-same-ray-zero
        (:instance lw-ray-triangle-same-ray-zero (a b) (b c) (c a))
        (:instance lw-ray-triangle-same-ray-zero (a c) (b a) (c b))
        lw-ray-triangle-index-cyclic
        (:instance lw-ray-triangle-index-cyclic (a b) (b c) (c a)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edgep lw-ray-determinant-index lw-rts-left-commutes lw-rts-left-distributes lw-rts-fold-constants lw-rts-times-negative lw-rts-negative-times lw-rts-zero-times lw-rts-minus-one lw-rts-double-negative lw-rts-add-cancel lw-rts-double lw-rts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

