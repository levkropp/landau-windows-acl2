(in-package "ACL2")

(include-book "ray-triangle-signs")

; Orientation-preserving complex multiplication scales determinants and
; dot products by the same strictly positive rational norm square.

(local (defthm lw-rtm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rtm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rtm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rtm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rtm-times-negative (a b) (b a)))
                 :in-theory (disable lw-rtm-times-negative)))))

(local (defthm lw-rtm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rtm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rtm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rtm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rtm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rtm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rtm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rtm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rtm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rtm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rtm-left-commutes)))))

(defthm lw-complex-det-products
 (implies (and (lw-complexp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-det (lw-complex-mul factor a) (lw-complex-mul factor b))
         (* (lw-complex-norm-square factor) (lw-complex-det a b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-det lw-complex-mul lw-complex-norm-square lw-rtm-left-commutes lw-rtm-left-distributes lw-rtm-fold-constants lw-rtm-times-negative lw-rtm-negative-times lw-rtm-zero-times lw-rtm-minus-one lw-rtm-double-negative lw-rtm-add-cancel lw-rtm-double lw-rtm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-complex-dot-products
 (implies (and (lw-complexp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-dot (lw-complex-mul factor a) (lw-complex-mul factor b))
         (* (lw-complex-norm-square factor) (lw-complex-dot a b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-dot lw-complex-mul lw-complex-norm-square lw-rtm-left-commutes lw-rtm-left-distributes lw-rtm-fold-constants lw-rtm-times-negative lw-rtm-negative-times lw-rtm-zero-times lw-rtm-minus-one lw-rtm-double-negative lw-rtm-add-cancel lw-rtm-double lw-rtm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-rtm-product-sign
 (implies (and (rationalp s) (< 0 s) (rationalp x))
  (and (equal (< 0 (* s x)) (< 0 x))
       (equal (< (* s x) 0) (< x 0))
       (equal (equal (* s x) 0) (equal x 0))))
 :hints (("Goal" :cases ((< 0 x) (< x 0)) :nonlinearp t))))

(defthm lw-ray-safe-edge-data
 (implies (lw-ray-safe-edgep a b)
  (and (lw-complexp a) (lw-complexp b)
       (not (equal a (cons 0 0))) (not (equal b (cons 0 0)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edgep lw-complex-det lw-complex-dot lw-rtm-left-commutes lw-rtm-left-distributes lw-rtm-fold-constants lw-rtm-times-negative lw-rtm-negative-times lw-rtm-zero-times lw-rtm-minus-one lw-rtm-double-negative lw-rtm-add-cancel lw-rtm-double lw-rtm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-safe-edge-reverse
 (implies (lw-ray-safe-edgep a b) (lw-ray-safe-edgep b a))
 :hints (("Goal" :use (lw-complex-det-reverse lw-complex-dot-commutative)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edgep lw-rtm-left-commutes lw-rtm-left-distributes lw-rtm-fold-constants lw-rtm-times-negative lw-rtm-negative-times lw-rtm-zero-times lw-rtm-minus-one lw-rtm-double-negative lw-rtm-add-cancel lw-rtm-double lw-rtm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil)

(defthm lw-ray-safe-edge-products
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-ray-safe-edgep a b))
  (lw-ray-safe-edgep (lw-complex-mul factor a) (lw-complex-mul factor b)))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-positive (point factor))
        (:instance lw-complex-norm-square-valid (point factor))
        lw-complex-orientation-rational)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edgep lw-complex-ring-rational lw-complex-det-products lw-complex-dot-products lw-rtm-product-sign lw-rtm-left-commutes lw-rtm-left-distributes lw-rtm-fold-constants lw-rtm-times-negative lw-rtm-negative-times lw-rtm-zero-times lw-rtm-minus-one lw-rtm-double-negative lw-rtm-add-cancel lw-rtm-double lw-rtm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-triangle-product-invariant
 (implies (and (lw-complexp factor) (not (equal factor (cons 0 0)))
               (lw-ray-safe-edgep a b) (lw-ray-safe-edgep b c) (lw-ray-safe-edgep c a))
  (equal (lw-ray-triangle-index (lw-complex-mul factor a)
                                (lw-complex-mul factor b)
                                (lw-complex-mul factor c))
         (lw-ray-triangle-index a b c)))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-positive (point factor))
        (:instance lw-complex-norm-square-valid (point factor))
        lw-complex-orientation-rational
        (:instance lw-complex-orientation-rational (a b) (b c))
        (:instance lw-complex-orientation-rational (a c) (b a))
        lw-ray-triangle-determinants
        (:instance lw-ray-triangle-determinants
          (a (lw-complex-mul factor a)) (b (lw-complex-mul factor b))
          (c (lw-complex-mul factor c))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edge-data lw-ray-safe-edge-products lw-complex-det-products lw-ray-determinant-index lw-rtm-product-sign lw-rtm-left-commutes lw-rtm-left-distributes lw-rtm-fold-constants lw-rtm-times-negative lw-rtm-negative-times lw-rtm-zero-times lw-rtm-minus-one lw-rtm-double-negative lw-rtm-add-cancel lw-rtm-double lw-rtm-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

