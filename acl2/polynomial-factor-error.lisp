(in-package "ACL2")

(include-book "polynomial-factor-roots")

; Uniform error propagation through one rational approximate linear factor.

(local (defthm lw-pfe-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfe-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfe-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfe-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfe-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfe-times-negative)))))

(local (defthm lw-pfe-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfe-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfe-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfe-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfe-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfe-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfe-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfe-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfe-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfe-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfe-left-commutes)))))
(local (defthm lw-pfe-affine-algebra
 (implies (and (lw-complexp residual) (lw-complexp delta) (lw-complexp q) (lw-complexp a))
  (equal (lw-complex-sub (lw-complex-add residual (lw-complex-mul delta q))
                         (lw-complex-mul delta a))
         (lw-complex-add residual (lw-complex-mul delta (lw-complex-sub q a)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-pfe-left-commutes lw-pfe-left-distributes lw-pfe-fold-constants lw-pfe-times-negative lw-pfe-negative-times lw-pfe-zero-times lw-pfe-minus-one lw-pfe-double-negative lw-pfe-add-cancel lw-pfe-double lw-pfe-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-complex-affine-factor-error
 (implies (and (lw-complexp q) (lw-complexp a)
               (lw-complex-diskp residual residual-cap)
               (lw-complex-diskp delta delta-cap)
               (lw-complex-diskp (lw-complex-sub q a) error)
               (rationalp epsilon) (<= (+ residual-cap (* delta-cap error)) epsilon))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-add residual (lw-complex-mul delta q)) (lw-complex-mul delta a))
   epsilon))
 :hints (("Goal"
  :use ((:instance lw-complex-mul-disk (left delta) (radius delta-cap)
          (right (lw-complex-sub q a)) (other-radius error))
        (:instance lw-complex-add-disk (left residual) (radius residual-cap)
          (right (lw-complex-mul delta (lw-complex-sub q a))) (other-radius (* delta-cap error)))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-add residual (lw-complex-mul delta (lw-complex-sub q a))))
          (radius (+ residual-cap (* delta-cap error))) (cap epsilon)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-disk-data lw-pfe-affine-algebra lw-pfe-left-commutes lw-pfe-left-distributes lw-pfe-fold-constants lw-pfe-times-negative lw-pfe-negative-times lw-pfe-zero-times lw-pfe-minus-one lw-pfe-double-negative lw-pfe-add-cancel lw-pfe-double lw-pfe-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-polynomial-factor-error-step
 (implies
  (and (lw-polynomial-factor-inputp coefficients bound epsilon) (consp (cdr coefficients))
       (lw-complex-diskp point bound) (lw-ray-pointsp roots)
       (lw-complex-diskp
        (lw-complex-sub
         (lw-complex-polynomial
          (lw-polynomial-divided-difference coefficients (lw-polynomial-factor-root coefficients epsilon)) point 0)
         (lw-polynomial-linear-factor-value roots
          (lw-polynomial-leading
           (lw-polynomial-divided-difference coefficients (lw-polynomial-factor-root coefficients epsilon))) point))
        (lw-polynomial-factor-next-error coefficients bound epsilon)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
    (lw-complex-mul (lw-complex-sub point (lw-polynomial-factor-root coefficients epsilon))
                   (lw-polynomial-linear-factor-value roots (lw-polynomial-leading coefficients) point)))
   epsilon))
 :hints (("Goal"
  :use (lw-polynomial-factor-step-data lw-polynomial-factor-next-error-data lw-polynomial-leading-valid
        (:instance lw-polynomial-linear-factor-value-rational
          (leading (lw-polynomial-leading coefficients)))
        (:instance lw-polynomial-synthetic-decomposition (anchor (lw-polynomial-factor-root coefficients epsilon)))
        (:instance lw-complex-sub-disk (left point) (radius bound)
          (right (lw-polynomial-factor-root coefficients epsilon))
          (other-radius (* 2 (lw-polynomial-leading-radius coefficients))))
        (:instance lw-complex-affine-factor-error
          (residual (lw-complex-polynomial coefficients (lw-polynomial-factor-root coefficients epsilon) 0))
          (residual-cap (* 1/2 epsilon))
          (delta (lw-complex-sub point (lw-polynomial-factor-root coefficients epsilon)))
          (delta-cap (+ bound (* 2 (lw-polynomial-leading-radius coefficients))))
          (q (lw-complex-polynomial
              (lw-polynomial-divided-difference coefficients (lw-polynomial-factor-root coefficients epsilon)) point 0))
          (a (lw-polynomial-linear-factor-value roots (lw-polynomial-leading coefficients) point))
          (error (lw-polynomial-factor-next-error coefficients bound epsilon))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-complex-polynomial-rational lw-complex-disk-data lw-pfe-left-commutes lw-pfe-left-distributes lw-pfe-fold-constants lw-pfe-times-negative lw-pfe-negative-times lw-pfe-zero-times lw-pfe-minus-one lw-pfe-double-negative lw-pfe-add-cancel lw-pfe-double lw-pfe-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
