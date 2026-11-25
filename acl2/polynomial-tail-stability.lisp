; Uniform bounds for polynomial tails, including their value at the origin.
(in-package "ACL2")
(include-book "polynomial-geometric-bounds")
(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner
                 lw-polynomial-add-constant lw-polynomial-multiply-coefficients)))
(local (in-theory (disable lw-polynomial-coefficient-caps lw-polynomial-pad
 lw-polynomial-difference lw-complex-coefficient-at)))
(local (defthm lw-pts-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pts-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pts-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pts-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pts-times-negative (a b) (b a)))
                 :in-theory (disable lw-pts-times-negative)))))

(local (defthm lw-pts-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pts-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pts-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pts-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pts-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pts-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pts-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pts-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pts-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pts-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pts-left-commutes)))))

(local (defthm lw-pts-polynomial-nil
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complex-polynomial endp lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pts-cdr-length-equality
 (implies (equal (len left) (len right)) (equal (len (cdr left)) (len (cdr right))))
 :hints (("Goal" :cases ((consp left) (consp right)) :in-theory (enable len)))))

(defthm lw-polynomial-tail-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap))
 (and (lw-complex-coefficientsp (cdr coefficients)) (lw-polynomial-coefficient-caps (cdr coefficients) cap)))
 :hints (("Goal"
 :in-theory (union-theories
 '(lw-complex-coefficientsp lw-polynomial-coefficient-caps endp lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-polynomial-tail-half-bound
 (implies (and (lw-complex-coefficientsp coefficients) (lw-polynomial-coefficient-caps coefficients cap)
  (rationalp cap) (<= 0 cap) (lw-complex-diskp point 1/2))
 (lw-complex-diskp (lw-complex-polynomial (cdr coefficients) point 0) (* 2 cap)))
 :hints (("Goal"
 :use (lw-polynomial-tail-data
       (:instance lw-complex-polynomial-geometric-tail-bound (coefficients (cdr coefficients)) (radius 1/2) (offset 0)))
 :in-theory (union-theories
 '(lw-geometric-disk-gain (:executable-counterpart lw-rational-power) lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-pts-pad-tail-data
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (< 0 count) (<= (len coefficients) count))
 (and (natp (- count 1)) (<= (len (cdr coefficients)) (- count 1))))
 :hints (("Goal" :cases ((consp coefficients)) :in-theory (enable len lw-complex-coefficientsp)))
 :rule-classes nil))

(local (defthm lw-pts-length-natural
 (natp (len coefficients))
 :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-polynomial-pad-tail-evaluation
 (implies (and (lw-complex-coefficientsp coefficients) (natp count) (<= (len coefficients) count)
  (lw-complexp point))
 (equal (lw-complex-polynomial (cdr (lw-polynomial-pad coefficients count)) point 0)
        (lw-complex-polynomial (cdr coefficients) point 0)))
 :hints (("Goal"
 :cases ((zp count))
 :use (lw-pts-pad-tail-data
       (:instance lw-pts-length-natural (coefficients (cdr coefficients)))
       (:instance lw-polynomial-pad-evaluation (coefficients (cdr coefficients)) (count (- count 1)) (offset 0)))
 :expand ((lw-polynomial-pad coefficients count) (lw-polynomial-pad nil count))
 :in-theory (union-theories
 '(lw-complex-coefficientsp endp len lw-pts-polynomial-nil (:executable-counterpart lw-polynomial-pad) lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-pts-difference-cdr
 (equal (cdr (lw-polynomial-difference left right))
        (lw-polynomial-difference (cdr left) (cdr right)))
 :hints (("Goal" :expand ((lw-polynomial-difference left right))
 :in-theory (union-theories
 '(lw-polynomial-difference lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))))

(defthm lw-complex-polynomial-tail-difference-half-bound
 (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right)
  (equal (len left) (len right))
  (lw-polynomial-coefficient-caps (lw-polynomial-difference left right) cap)
  (rationalp cap) (<= 0 cap) (lw-complex-diskp point 1/2))
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-polynomial (cdr left) point 0)
                 (lw-complex-polynomial (cdr right) point 0)) (* 2 cap)))
 :hints (("Goal"
 :use (lw-polynomial-difference-valid lw-pts-cdr-length-equality
       (:instance lw-complex-disk-data (radius 1/2))
       (:instance lw-complex-polynomial-tail-half-bound (coefficients (lw-polynomial-difference left right)))
       (:instance lw-polynomial-difference-evaluation (left (cdr left)) (right (cdr right)) (offset 0)))
 :in-theory (union-theories
 '(lw-complex-coefficientsp endp lw-pts-difference-cdr lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-complex-polynomial-first-tail-identity
 (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
 (equal (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                       (lw-complex-polynomial coefficients (cons 0 0) 0))
        (lw-complex-mul point (lw-complex-polynomial (cdr coefficients) point 0))))
 :hints (("Goal"
 :cases ((consp coefficients))
 :use (lw-complex-polynomial-at-zero lw-complex-polynomial-horner
       (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (offset 0)))
 :in-theory (union-theories
 '(lw-complex-polynomial-horner lw-complex-polynomial-at-zero lw-complex-coefficient-at-below-offset lw-complex-add-zero lw-complex-coefficientsp lw-complex-coefficient-at endp lw-pts-polynomial-nil lw-complex-sub-add-cancel lw-complex-ring-rational lw-complex-mul-zero lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-pts-left-commutes lw-pts-left-distributes lw-pts-fold-constants lw-pts-times-negative lw-pts-negative-times lw-pts-zero-times lw-pts-minus-one lw-pts-double-negative lw-pts-add-cancel lw-pts-double lw-pts-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

