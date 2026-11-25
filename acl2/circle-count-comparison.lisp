(in-package "ACL2")

(include-book "circle-count-polynomial")
(include-book "cauchy-real-constant")
(include-book "polynomial-subtraction")
(include-book "polynomial-quadratic-bounds")

(defun lw-circle-count-difference (left right radius)
  (lw-polynomial-subtract (lw-circle-count-polynomial left radius 1/16) (lw-circle-count-polynomial right radius 1/16)))

(local (in-theory
        (disable lw-circle-count-difference lw-circle-count-polynomial
                 lw-cauchy-real-boundary-check lw-cauchy-coefficient-count
                 lw-complexp lw-complex-polynomial lw-complex-coefficient-at
                 lw-complex-coefficientsp lw-polynomial-subtract)))

(local (defthm lw-ccc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ccc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ccc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ccc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ccc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ccc-times-negative)))))

(local (defthm lw-ccc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ccc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ccc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ccc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ccc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ccc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ccc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-ccc-length-natural
         (natp (len roots))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ccc-real-subtract
   (implies (and (rationalp a) (rationalp b))
            (equal (lw-complex-sub (cons a 0) (cons b 0)) (cons (- a b) 0)))
   :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local
 (defthm lw-ccc-difference-data
   (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
                (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root left radius))
                (not (lw-circle-boundary-root right radius)))
            (and (lw-complex-coefficientsp (lw-circle-count-difference left right radius))
                 (equal (lw-complex-coefficient-at (lw-circle-count-difference left right radius) 0 0) (cons (- (len (lw-circle-pole-roots left radius)) (len (lw-circle-pole-roots right radius))) 0))))
   :hints (("Goal"
            :use ((:instance lw-polynomial-subtract-evaluation (left (lw-circle-count-polynomial left radius 1/16)) (right (lw-circle-count-polynomial right radius 1/16)) (point (cons 0 0))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-count-difference lw-circle-count-polynomial-data lw-polynomial-subtract-valid lw-complex-polynomial-at-zero lw-ccc-real-subtract lw-ccc-length-natural lw-ccc-left-commutes lw-ccc-left-distributes lw-ccc-fold-constants lw-ccc-times-negative lw-ccc-negative-times lw-ccc-zero-times lw-ccc-minus-one lw-ccc-double-negative lw-ccc-add-cancel lw-ccc-double lw-ccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ccc-real-triangle
   (implies (and (rationalp a) (rationalp b) (rationalp x) (rationalp y)
                 (<= (abs (- a x)) 1/16) (<= (abs (- b y)) 1/16)
                 (<= (abs (- a b)) 1/4))
            (<= (abs (- x y)) 3/8))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) abs lw-ccc-left-commutes lw-ccc-left-distributes lw-ccc-fold-constants lw-ccc-times-negative lw-ccc-negative-times lw-ccc-zero-times lw-ccc-minus-one lw-ccc-double-negative lw-ccc-add-cancel lw-ccc-double lw-ccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-ccc-real-coordinate
   (implies (lw-complexp point) (rationalp (car point)))
   :hints (("Goal" :in-theory (enable lw-complexp)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ccc-real-subtract-car
   (implies (and (lw-complexp a) (lw-complexp b))
            (equal (car (lw-complex-sub a b)) (- (car a) (car b))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ consp lw-complexp lw-complex-sub lw-ccc-left-commutes lw-ccc-left-distributes lw-ccc-fold-constants lw-ccc-times-negative lw-ccc-negative-times lw-ccc-zero-times lw-ccc-minus-one lw-ccc-double-negative lw-ccc-add-cancel lw-ccc-double lw-ccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-count-difference-point-bound
  (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
                (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root left radius))
                (not (lw-circle-boundary-root right radius))
                (lw-complexp point) (equal (lw-complex-norm-square point) 1)
                (<= (abs (- (car (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum left (lw-complex-scale radius point)))) (car (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum right (lw-complex-scale radius point)))))) 1/4))
           (<= (abs (car (lw-complex-polynomial (lw-circle-count-difference left right radius) point 0))) 3/8))
  :hints (("Goal"
           :use ((:instance lw-circle-count-polynomial-error (roots left) (error 1/16))
                 (:instance lw-circle-count-polynomial-error (roots right) (error 1/16))
                 (:instance lw-ccc-real-triangle
                   (a (car (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum left (lw-complex-scale radius point))))) (b (car (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum right (lw-complex-scale radius point)))))
                   (x (car (lw-complex-polynomial (lw-circle-count-polynomial left radius 1/16) point 0))) (y (car (lw-complex-polynomial (lw-circle-count-polynomial right radius 1/16) point 0)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-count-difference lw-circle-count-polynomial-data lw-polynomial-subtract-evaluation lw-ccc-real-subtract-car lw-ccc-real-coordinate lw-complex-polynomial-rational lw-complex-scale-rational lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-ccc-left-commutes lw-ccc-left-distributes lw-ccc-fold-constants lw-ccc-times-negative lw-ccc-negative-times lw-ccc-zero-times lw-ccc-minus-one lw-ccc-double-negative lw-ccc-add-cancel lw-ccc-double lw-ccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local (defthm lw-ccc-nil-constant
         (equal (lw-complex-coefficient-at nil 0 0) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-coefficient-at)))))

(local
 (defthm lw-ccc-integer-equality
   (implies (and (integerp a) (integerp b) (<= (abs (- a b)) 1/2))
            (equal a b))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) abs lw-ccc-left-commutes lw-ccc-left-distributes lw-ccc-fold-constants lw-ccc-times-negative lw-ccc-negative-times lw-ccc-zero-times lw-ccc-minus-one lw-ccc-double-negative lw-ccc-add-cancel lw-ccc-double lw-ccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
   :rule-classes nil))

(local (defthm lw-ccc-length-positive
         (implies (consp coefficients) (< 0 (len coefficients)))
         :rule-classes (:linear :rewrite)))

(defthm lw-circle-interior-count-from-comparison
  (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
                (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root left radius))
                (not (lw-circle-boundary-root right radius))
                (lw-cauchy-real-boundary-check
                 (lw-circle-count-difference left right radius)
                 (lw-cauchy-orbit-rotation (len (lw-circle-count-difference left right radius)))
                 (lw-cauchy-coefficient-count (lw-circle-count-difference left right radius) (len (lw-circle-count-difference left right radius)) 1/8)
                 3/8))
           (equal (len (lw-circle-pole-roots left radius)) (len (lw-circle-pole-roots right radius))))
  :hints (("Goal"
           :cases ((consp (lw-circle-count-difference left right radius)))
           :use (lw-ccc-difference-data
                 (:instance lw-complex-coefficient-at-nth
                   (coefficients (lw-circle-count-difference left right radius)) (target 0) (offset 0))
                 (:instance lw-cauchy-finite-real-constant-bound
                   (coefficients (lw-circle-count-difference left right radius)) (degree (len (lw-circle-count-difference left right radius)))
                   (cap 3/8) (error 1/8))
                 (:instance lw-ccc-integer-equality (a (len (lw-circle-pole-roots left radius))) (b (len (lw-circle-pole-roots right radius)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-coefficientsp lw-ccc-length-natural lw-ccc-nil-constant lw-ccc-length-positive cons-equal len nth lw-ccc-left-commutes lw-ccc-left-distributes lw-ccc-fold-constants lw-ccc-times-negative lw-ccc-negative-times lw-ccc-zero-times lw-ccc-minus-one lw-ccc-double-negative lw-ccc-add-cancel lw-ccc-double lw-ccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
