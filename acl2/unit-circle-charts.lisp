; Two computed rational charts cover every rational point of the unit circle.
(in-package "ACL2")
(include-book "cauchy-orbits")
(include-book "phase-continuity")
(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub
 lw-complex-scale lw-complex-diskp lw-diskp lw-complex-norm-square
 lw-phase-rotation lw-phase-denominator)))
(local (defthm lw-ucg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ucg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ucg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ucg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ucg-times-negative (a b) (b a)))
                 :in-theory (disable lw-ucg-times-negative)))))

(local (defthm lw-ucg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ucg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ucg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ucg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ucg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ucg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ucg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ucg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ucg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ucg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ucg-left-commutes)))))

(local (defthm lw-ucg-square-nonnegative
 (implies (rationalp value) (<= 0 (* value value)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ucg-unit-coordinate-bounds
 (implies (and (rationalp x) (rationalp y) (equal (+ (* x x) (* y y)) 1))
 (and (<= -1 x) (<= x 1) (<= -1 y) (<= y 1)))
 :hints (("Goal" :use ((:instance lw-ucg-square-nonnegative (value x))
                       (:instance lw-ucg-square-nonnegative (value y)))
 :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ucg-inverse-bounds
 (implies (and (rationalp x) (<= 0 x))
 (and (rationalp (/ (+ 1 x))) (< 0 (/ (+ 1 x))) (<= (/ (+ 1 x)) 1)))
 :hints (("Goal" :use ((:instance inverse-of-* (x (+ 1 x))))
 :in-theory (union-theories
 '( lw-ucg-left-commutes lw-ucg-left-distributes lw-ucg-fold-constants lw-ucg-times-negative lw-ucg-negative-times lw-ucg-zero-times lw-ucg-minus-one lw-ucg-double-negative lw-ucg-add-cancel lw-ucg-double lw-ucg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t)) :rule-classes nil))


(local (defthm lw-ucg-cayley-quotient
 (implies (rationalp value)
 (equal (lw-phase-rotation value)
 (lw-complex-mul (cons 2 value) (lw-complex-reciprocal (cons 2 (- value))))))
 :hints (("Goal" :in-theory (enable lw-phase-rotation lw-phase-denominator
 lw-complex-reciprocal lw-complex-norm-square lw-complex-conjugate lw-complex-scale lw-complex-mul)))))

(local (defthm lw-ucg-half-cross
 (implies (and (rationalp x) (rationalp y) (<= 0 x)
 (equal (+ (* x x) (* y y)) 1))
 (equal (lw-complex-mul (cons x y) (cons 2 (- (* 2 y (/ (+ 1 x)))))) (cons 2 (* 2 y (/ (+ 1 x))))))
 :hints (("Goal"
 :use ((:instance lw-ucg-inverse-factor (divisor (+ 1 x)) (coefficient (* 2 y)))
       (:instance lw-ucg-inverse-factor (divisor (+ 1 x)) (coefficient (* 2 (- 1 x)))))
 :in-theory (union-theories
 '(lw-complex-mul cons-equal lw-ucg-left-commutes lw-ucg-left-distributes lw-ucg-fold-constants lw-ucg-times-negative lw-ucg-negative-times lw-ucg-zero-times lw-ucg-minus-one lw-ucg-double-negative lw-ucg-add-cancel lw-ucg-double lw-ucg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ucg-positive-half-inverse
 (implies (and (rationalp x) (rationalp y) (<= 0 x)
               (equal (+ (* x x) (* y y)) 1))
 (and (rationalp (* 2 y (/ (+ 1 x)))) (<= -2 (* 2 y (/ (+ 1 x)))) (<= (* 2 y (/ (+ 1 x))) 2)
      (equal (lw-phase-rotation (* 2 y (/ (+ 1 x)))) (cons x y))))
 :hints (("Goal"
 :use (lw-ucg-inverse-bounds lw-ucg-unit-coordinate-bounds lw-ucg-half-cross
       (:instance lw-complex-reciprocal-inverse (point (cons 2 (- (* 2 y (/ (+ 1 x)))))))
       (:instance lw-complex-reciprocal-rational (point (cons 2 (- (* 2 y (/ (+ 1 x)))))))
       (:instance lw-complex-mul-associative (left (cons x y)) (middle (cons 2 (- (* 2 y (/ (+ 1 x)))))) (right (lw-complex-reciprocal (cons 2 (- (* 2 y (/ (+ 1 x))))))))
       (:instance lw-complex-mul-one (point (cons x y))))
 :in-theory (union-theories
 '(lw-ucg-cayley-quotient (:executable-counterpart lw-complexp) lw-complexp cons-equal lw-ucg-left-commutes lw-ucg-left-distributes lw-ucg-fold-constants lw-ucg-times-negative lw-ucg-negative-times lw-ucg-zero-times lw-ucg-minus-one lw-ucg-double-negative lw-ucg-add-cancel lw-ucg-double lw-ucg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t))
 :rule-classes nil))


(defun lw-unit-circle-sign (point) (if (< (car point) 0) -1 1))
(defun lw-unit-circle-parameter (point)
 (let ((sign (lw-unit-circle-sign point)))
  (* 2 sign (cdr point) (/ (+ 1 (* sign (car point)))))))
(local (in-theory (disable lw-unit-circle-sign lw-unit-circle-parameter)))

(defthm lw-unit-circle-chart-data
 (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (and (rationalp (lw-unit-circle-sign point))
      (or (equal (lw-unit-circle-sign point) 1) (equal (lw-unit-circle-sign point) -1))
      (rationalp (lw-unit-circle-parameter point))
      (<= -2 (lw-unit-circle-parameter point))
      (<= (lw-unit-circle-parameter point) 2)))
 :hints (("Goal"
 :cases ((< (car point) 0))
 :use ((:instance lw-ucg-positive-half-inverse (x (car point)) (y (cdr point)))
       (:instance lw-ucg-positive-half-inverse (x (- (car point))) (y (- (cdr point)))))
 :in-theory (union-theories
 '(lw-complexp lw-complex-norm-square lw-unit-circle-sign lw-unit-circle-parameter lw-ucg-left-commutes lw-ucg-left-distributes lw-ucg-fold-constants lw-ucg-times-negative lw-ucg-negative-times lw-ucg-zero-times lw-ucg-minus-one lw-ucg-double-negative lw-ucg-add-cancel lw-ucg-double lw-ucg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)))

(defthm lw-unit-circle-chart-reconstruction
 (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1))
 (equal (lw-complex-scale (lw-unit-circle-sign point)
         (lw-phase-rotation (lw-unit-circle-parameter point))) point))
 :hints (("Goal"
 :cases ((< (car point) 0))
 :use ((:instance lw-ucg-positive-half-inverse (x (car point)) (y (cdr point)))
       (:instance lw-ucg-positive-half-inverse (x (- (car point))) (y (- (cdr point)))))
 :in-theory (union-theories
 '(lw-complexp lw-complex-norm-square lw-complex-scale lw-unit-circle-sign lw-unit-circle-parameter lw-ucg-left-commutes lw-ucg-left-distributes lw-ucg-fold-constants lw-ucg-times-negative lw-ucg-negative-times lw-ucg-zero-times lw-ucg-minus-one lw-ucg-double-negative lw-ucg-add-cancel lw-ucg-double lw-ucg-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :nonlinearp t :do-not-induct t)))

