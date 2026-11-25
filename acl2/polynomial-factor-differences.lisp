(in-package "ACL2")

(include-book "polynomial-factor-annuli")

; A recursive Lipschitz bound for the actual product values on the square.

(local (defthm lw-pfd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfd-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfd-times-negative)))))

(local (defthm lw-pfd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfd-left-commutes)))))
(local (defthm lw-pfd-point-type
 (implies (lw-unit-square-pointp point) (lw-complexp point))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-pointp lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))
(local (defthm lw-pfd-zero-difference
 (implies (lw-complexp leading)
  (lw-complex-diskp (lw-complex-sub leading leading) 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pfd-difference-algebra
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp root) (lw-complexp p) (lw-complexp q))
  (equal
   (lw-complex-sub (lw-complex-mul (lw-complex-sub a root) p)
                   (lw-complex-mul (lw-complex-sub b root) q))
   (lw-complex-add
    (lw-complex-mul (lw-complex-sub a root) (lw-complex-sub p q))
    (lw-complex-mul (lw-complex-sub a b) q))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-mul lw-complex-add lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-factor-value-difference
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading)
               (lw-unit-square-pointp a) (lw-unit-square-pointp b)
               (lw-complex-diskp (lw-complex-sub a b) error))
  (lw-complex-diskp
   (lw-complex-sub (lw-polynomial-linear-factor-value roots leading a)
                   (lw-polynomial-linear-factor-value roots leading b))
   (* (lw-polynomial-factor-lipschitz roots leading) error)))
 :hints (("Goal" :induct (lw-polynomial-linear-factor-value roots leading a)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-linear-factor-value) lw-polynomial-linear-factor-value lw-polynomial-factor-lipschitz lw-unit-square-roots-awayp lw-unit-square-roots-away-data lw-polynomial-linear-factor-value-rational lw-pfd-point-type lw-pfd-zero-difference lw-pfd-difference-algebra endp lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-unit-square-root-cap-bound (root (car roots)) (point a))
                  (:instance lw-polynomial-factor-value-upper (roots (cdr roots)) (point b))
                  (:instance lw-complex-mul-disk
                    (left (lw-complex-sub a (car roots))) (radius (lw-unit-square-root-cap (car roots)))
                    (right (lw-complex-sub
                      (lw-polynomial-linear-factor-value (cdr roots) leading a)
                      (lw-polynomial-linear-factor-value (cdr roots) leading b)))
                    (other-radius (* (lw-polynomial-factor-lipschitz (cdr roots) leading) error)))
                  (:instance lw-complex-mul-disk
                    (left (lw-complex-sub a b)) (radius error)
                    (right (lw-polynomial-linear-factor-value (cdr roots) leading b))
                    (other-radius (lw-polynomial-factor-upper (cdr roots) leading)))
                  (:instance lw-complex-add-disk
                    (left (lw-complex-mul (lw-complex-sub a (car roots))
                           (lw-complex-sub (lw-polynomial-linear-factor-value (cdr roots) leading a)
                                           (lw-polynomial-linear-factor-value (cdr roots) leading b))))
                    (radius (* (lw-unit-square-root-cap (car roots))
                               (lw-polynomial-factor-lipschitz (cdr roots) leading) error))
                    (right (lw-complex-mul (lw-complex-sub a b)
                            (lw-polynomial-linear-factor-value (cdr roots) leading b)))
                    (other-radius (* error (lw-polynomial-factor-upper (cdr roots) leading)))))
            :do-not-induct t))))

(local (defthm lw-pfd-map-consp
 (equal (consp (lw-polynomial-factor-path-values roots leading points)) (consp points))
 :hints (("Goal" :expand ((lw-polynomial-factor-path-values roots leading points))
          :in-theory (union-theories
 '(fold-consts-in-+ endp lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pfd-unit-head
 (implies (and (consp points) (lw-ray-unit-square-pointsp points)) (lw-unit-square-pointp (car points)))
 :hints (("Goal" :expand ((lw-ray-unit-square-pointsp points)) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-factor-path-step
 (implies (and (lw-unit-square-roots-awayp roots) (lw-complexp leading)
               (lw-ray-unit-square-pointsp points) (lw-ray-path-step-check points error))
  (lw-ray-path-step-check (lw-polynomial-factor-path-values roots leading points)
                          (* (lw-polynomial-factor-lipschitz roots leading) error)))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values roots leading points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-ray-unit-square-pointsp lw-ray-path-step-check lw-polynomial-factor-path-head lw-pfd-map-consp lw-pfd-unit-head endp lw-pfd-left-commutes lw-pfd-left-distributes lw-pfd-fold-constants lw-pfd-times-negative lw-pfd-negative-times lw-pfd-zero-times lw-pfd-minus-one lw-pfd-double-negative lw-pfd-add-cancel lw-pfd-double lw-pfd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-polynomial-factor-value-difference (a (cadr points)) (b (car points))))
            :do-not-induct t))))
