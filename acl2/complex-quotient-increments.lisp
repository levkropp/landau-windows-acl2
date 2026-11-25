(in-package "ACL2")

(include-book "euler-difference-quotient")
(include-book "complex-quotients")

; Rational clearance and exact difference quotients for a linear denominator.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-euler-derivative-modulus lw-euler-derivative-curvature
 lw-complex-euler-continuation-value lw-complex-euler-local-coefficient-value
 lw-complex-l1 lw-complex-norm-square lw-complex-reciprocal lw-complex-quotient lw-complex-linear-remainder)))
(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
          lw-complex-reciprocal lw-complex-quotient
          lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes)))

(local (defthm lw-cqi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cqi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cqi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cqi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cqi-times-negative (a b) (b a)))
                 :in-theory (disable lw-cqi-times-negative)))))

(local (defthm lw-cqi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cqi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cqi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cqi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cqi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cqi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cqi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cqi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cqi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cqi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cqi-left-commutes)))))

(local (defthm lw-cqi-abs-reverse
 (implies (and (rationalp x) (rationalp y))
  (<= (abs x) (+ (abs (+ x y)) (abs y))))
 :hints (("Goal" :cases ((<= 0 x) (<= 0 y) (<= 0 (+ x y)))
                  :in-theory (enable abs)))))

(defthm lw-complex-l1-add-lower
 (implies (and (lw-complexp anchor) (lw-complexp offset))
  (<= (lw-complex-l1 anchor)
      (+ (lw-complex-l1 (lw-complex-add anchor offset)) (lw-complex-l1 offset))))
 :hints (("Goal"
  :use ((:instance lw-cqi-abs-reverse (x (car anchor)) (y (car offset)))
        (:instance lw-cqi-abs-reverse (x (cdr anchor)) (y (cdr offset))))
  :in-theory (union-theories
 '(lw-complexp lw-complex-l1 lw-complex-add lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cqi-l1-zero
 (equal (lw-complex-l1 (cons 0 0)) 0)
 :hints (("Goal" :in-theory (enable lw-complex-l1)))))

(defthm lw-complex-small-shift-clearance
 (implies (and (lw-complexp anchor) (not (equal anchor (cons 0 0)))
               (lw-complexp offset) (<= (lw-complex-l1 offset) (* 1/2 (lw-complex-l1 anchor))))
  (and (lw-complexp (lw-complex-add anchor offset))
       (not (equal (lw-complex-add anchor offset) (cons 0 0)))
       (<= (* 1/16 (lw-complex-l1 anchor) (lw-complex-l1 anchor))
           (lw-complex-norm-square (lw-complex-add anchor offset)))
       (lw-complex-diskp (lw-complex-reciprocal (lw-complex-add anchor offset))
                         (/ (* 1/4 (lw-complex-l1 anchor))))))
 :hints (("Goal"
  :cases ((equal (lw-complex-add anchor offset) (cons 0 0)))
  :use (lw-complex-l1-add-lower
        (:instance lw-complex-l1-bound (point offset))
        (:instance lw-complex-l1-clearance (point anchor))
        (:instance lw-complex-ring-rational (left anchor) (right offset))
        (:instance lw-complex-l1-clearance (point (lw-complex-add anchor offset)))
        (:instance lw-complex-reciprocal-disk-bound
         (point (lw-complex-add anchor offset)) (lower (* 1/4 (lw-complex-l1 anchor)))))
  :in-theory (union-theories
 '(lw-cqi-l1-zero lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-complex-quotient-denominator-product
 (implies (and (lw-complexp numerator) (lw-complexp denominator) (not (equal denominator (cons 0 0))))
  (equal (lw-complex-mul denominator (lw-complex-quotient numerator denominator)) numerator))
 :hints (("Goal"
  :use ((:instance lw-complex-reciprocal-cancel-product (a denominator) (b numerator))
        (:instance lw-complex-reciprocal-rational (point denominator))
        (:instance lw-complex-mul-commutative (left numerator) (right (lw-complex-reciprocal denominator))))
  :in-theory (union-theories
 '(lw-complex-quotient lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cqi-pair-equality
 (implies (equal left right)
  (and (equal (car left) (car right)) (equal (cdr left) (cdr right))))
 :rule-classes nil))

(local (defthm lw-cqi-cons-equality
 (equal (equal (cons a b) (cons c d)) (and (equal a c) (equal b d)))
 :hints (("Goal" :use ((:instance lw-cqi-pair-equality (left (cons a b)) (right (cons c d))))
                 :in-theory (union-theories
 '( lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))))

(local (defthm lw-cqi-cross-algebra
 (implies (and (lw-complexp denominator) (lw-complexp offset) (lw-complexp x) (lw-complexp y)
               (lw-complexp d) (lw-complexp value) (lw-complexp anchor)
               (equal (lw-complex-mul (lw-complex-add denominator offset) x) value)
               (equal (lw-complex-mul denominator y) anchor)
               (equal (lw-complex-mul offset d) (lw-complex-sub value anchor)))
  (equal (lw-complex-mul (lw-complex-add denominator offset) (lw-complex-sub x y))
         (lw-complex-mul offset (lw-complex-sub d y))))
 :hints (("Goal" :use ((:instance lw-cqi-pair-equality
                   (left (lw-complex-mul offset d)) (right (lw-complex-sub value anchor))))
                 :in-theory (union-theories
 '(lw-cqi-cons-equality lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-cqi-cross-solve
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp x) (lw-complexp y)
               (not (equal a (cons 0 0))) (not (equal b (cons 0 0)))
               (equal (lw-complex-mul a x) (lw-complex-mul b y)))
  (equal (lw-complex-quotient x b) (lw-complex-quotient y a)))
 :hints (("Goal"
  :use ((:instance lw-complex-reciprocal-rational (point a))
        (:instance lw-complex-reciprocal-rational (point b))
        (:instance lw-complex-reciprocal-cancel-product (a b) (b y))
        (:instance lw-complex-mul-left-commutes (a a) (b (lw-complex-reciprocal b)) (c x))
        (:instance lw-complex-mul-commutative (left x) (right (lw-complex-reciprocal b)))
        (:instance lw-complex-mul-commutative (left y) (right (lw-complex-reciprocal a)))
        (:instance lw-complex-linear-solve (a a) (b (lw-complex-quotient x b)) (c y)))
  :in-theory (union-theories
 '(lw-complex-quotient lw-complex-ring-rational lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-quotient-increment-identity
 (implies (and (lw-complexp value) (lw-complexp anchor) (lw-complexp denominator) (lw-complexp offset)
               (not (equal denominator (cons 0 0))) (not (equal offset (cons 0 0)))
               (not (equal (lw-complex-add denominator offset) (cons 0 0))))
  (equal (lw-complex-quotient (lw-complex-sub (lw-complex-quotient value (lw-complex-add denominator offset)) (lw-complex-quotient anchor denominator)) offset) (lw-complex-quotient (lw-complex-sub (lw-complex-quotient (lw-complex-sub value anchor) offset) (lw-complex-quotient anchor denominator)) (lw-complex-add denominator offset))))
 :hints (("Goal"
  :use ((:instance lw-complex-quotient-denominator-product (numerator value) (denominator (lw-complex-add denominator offset)))
        (:instance lw-complex-quotient-denominator-product (numerator anchor))
        (:instance lw-complex-quotient-denominator-product (numerator (lw-complex-sub value anchor)) (denominator offset))
        (:instance lw-cqi-cross-algebra (x (lw-complex-quotient value (lw-complex-add denominator offset))) (y (lw-complex-quotient anchor denominator)) (d (lw-complex-quotient (lw-complex-sub value anchor) offset)))
        (:instance lw-cqi-cross-solve (a (lw-complex-add denominator offset)) (b offset) (x (lw-complex-sub (lw-complex-quotient value (lw-complex-add denominator offset)) (lw-complex-quotient anchor denominator))) (y (lw-complex-sub (lw-complex-quotient (lw-complex-sub value anchor) offset) (lw-complex-quotient anchor denominator)))))
  :in-theory (union-theories
 '(lw-complex-ring-rational lw-complex-quotient-rational lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cqi-difference-of-differences
 (implies (and (lw-complexp left) (lw-complexp right) (lw-complexp anchor) (lw-complexp approximate-anchor))
  (equal (lw-complex-sub (lw-complex-sub left anchor) (lw-complex-sub right approximate-anchor))
         (lw-complex-sub (lw-complex-sub left right) (lw-complex-sub anchor approximate-anchor))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-sub lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cqi-denominator-shift
 (implies (and (lw-complexp denominator) (lw-complexp offset))
  (equal (lw-complex-sub (lw-complex-add denominator offset) denominator) offset))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-quotient-increment-bound
 (implies (and (lw-complexp value) (lw-complexp anchor) (lw-complexp denominator) (lw-complexp offset)
               (lw-complexp slope) (lw-complexp approximate-anchor)
               (not (equal denominator (cons 0 0))) (not (equal offset (cons 0 0)))
               (<= (lw-complex-l1 offset) (* 1/2 (lw-complex-l1 denominator)))
               (lw-complex-diskp (lw-complex-sub (lw-complex-quotient (lw-complex-sub value anchor) offset) slope) derivative-error)
               (lw-complex-diskp (lw-complex-sub (lw-complex-quotient anchor denominator) approximate-anchor) anchor-error)
               (lw-complex-diskp (lw-complex-sub slope approximate-anchor) numerator-cap))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-quotient (lw-complex-sub (lw-complex-quotient value (lw-complex-add denominator offset)) (lw-complex-quotient anchor denominator)) offset) (lw-complex-quotient (lw-complex-sub slope approximate-anchor) denominator))
   (+ (* (/ (* 1/4 (lw-complex-l1 denominator))) (+ derivative-error anchor-error))
      (* numerator-cap (/ (* 1/4 (lw-complex-l1 denominator))) (/ (* 1/2 (lw-complex-l1 denominator))) (lw-complex-l1 offset)))))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-clearance (point denominator))
        (:instance lw-complex-l1-bound (point offset))
        (:instance lw-complex-small-shift-clearance (anchor denominator))
        lw-complex-quotient-increment-identity
        (:instance lw-complex-sub-disk
         (left (lw-complex-sub (lw-complex-quotient (lw-complex-sub value anchor) offset) slope)) (right (lw-complex-sub (lw-complex-quotient anchor denominator) approximate-anchor))
         (radius derivative-error) (other-radius anchor-error))
        (:instance lw-complex-quotient-difference-bound
         (numerator (lw-complex-sub (lw-complex-quotient (lw-complex-sub value anchor) offset) (lw-complex-quotient anchor denominator))) (denominator (lw-complex-add denominator offset))
         (approximate-numerator (lw-complex-sub slope approximate-anchor)) (approximate-denominator denominator)
         (left-clearance (* 1/4 (lw-complex-l1 denominator))) (right-clearance (* 1/2 (lw-complex-l1 denominator)))
         (numerator-error (+ derivative-error anchor-error)) (denominator-error (lw-complex-l1 offset))))
  :in-theory (union-theories
 '(lw-complex-ring-rational lw-complex-quotient-rational lw-cqi-difference-of-differences lw-cqi-denominator-shift lw-cqi-left-commutes lw-cqi-left-distributes lw-cqi-fold-constants lw-cqi-times-negative lw-cqi-negative-times lw-cqi-zero-times lw-cqi-minus-one lw-cqi-double-negative lw-cqi-add-cancel lw-cqi-double lw-cqi-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))



