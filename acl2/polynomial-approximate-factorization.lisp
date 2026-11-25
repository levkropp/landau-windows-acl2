(in-package "ACL2")

(include-book "polynomial-factor-error")

; A complete list of degree-many rational linear factors uniformly
; approximates the polynomial on the requested closed rational disk.

(local (defthm lw-paf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-paf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-paf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-paf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-paf-times-negative (a b) (b a)))
                 :in-theory (disable lw-paf-times-negative)))))

(local (defthm lw-paf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-paf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-paf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-paf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-paf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-paf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-paf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-paf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-paf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-paf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-paf-left-commutes)))))
(local (defthm lw-paf-constant-value
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon)
               (not (consp (cdr coefficients))) (lw-complexp point))
  (equal (lw-complex-polynomial coefficients point 0) (lw-polynomial-leading coefficients)))
 :hints (("Goal"
  :expand ((lw-complex-polynomial coefficients point 0) (lw-complex-power point 0))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-complex-coefficientsp lw-polynomial-leading lw-complex-polynomial lw-complexp lw-complex-mul lw-complex-add endp lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-paf-zero-error
 (implies (and (lw-complexp point) (rationalp epsilon) (<= 0 epsilon))
  (lw-complex-diskp (lw-complex-sub point point) epsilon))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-paf-base-error
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon)
               (not (consp (cdr coefficients))) (lw-complex-diskp point bound))
  (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                                   (lw-polynomial-leading coefficients)) epsilon))
 :hints (("Goal" :use (lw-polynomial-leading-valid lw-paf-constant-value)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-complex-disk-data lw-paf-zero-error lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t))))

(local (defthm lw-paf-roots-base
 (implies (not (consp (cdr coefficients)))
  (equal (lw-polynomial-factor-roots coefficients bound epsilon) nil))
 :hints (("Goal" :expand ((lw-polynomial-factor-roots coefficients bound epsilon))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-paf-roots-step
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon) (consp (cdr coefficients)))
  (equal (lw-polynomial-factor-roots coefficients bound epsilon)
   (cons (lw-polynomial-factor-root coefficients epsilon)
    (lw-polynomial-factor-roots
     (lw-polynomial-divided-difference coefficients (lw-polynomial-factor-root coefficients epsilon))
     bound (lw-polynomial-factor-next-error coefficients bound epsilon)))))
 :hints (("Goal" :expand ((lw-polynomial-factor-roots coefficients bound epsilon))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(defthm lw-polynomial-approximate-factorization-error
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon)
               (lw-complex-diskp point bound))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-polynomial coefficients point 0)
    (lw-polynomial-linear-factor-value (lw-polynomial-factor-roots coefficients bound epsilon)
                                       (lw-polynomial-leading coefficients) point))
   epsilon))
 :hints (("Goal" :induct (lw-polynomial-factor-roots coefficients bound epsilon)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-roots) lw-paf-roots-base lw-paf-roots-step lw-paf-base-error lw-polynomial-linear-factor-value endp lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:use (lw-polynomial-factor-step-data
                  (:instance lw-polynomial-factor-roots-data
                   (coefficients (lw-polynomial-divided-difference coefficients (lw-polynomial-factor-root coefficients epsilon)))
                   (epsilon (lw-polynomial-factor-next-error coefficients bound epsilon)))
                  (:instance lw-polynomial-factor-error-step
                   (roots (lw-polynomial-factor-roots
                    (lw-polynomial-divided-difference coefficients (lw-polynomial-factor-root coefficients epsilon))
                    bound (lw-polynomial-factor-next-error coefficients bound epsilon)))))
            :do-not-induct t))))

(defthm lw-polynomial-approximate-factorization
 (implies (and (lw-polynomial-factor-inputp coefficients bound epsilon)
               (lw-complex-diskp point bound))
  (let ((roots (lw-polynomial-factor-roots coefficients bound epsilon)))
   (and (lw-ray-pointsp roots)
        (equal (len roots) (len (lw-polynomial-without-leading coefficients)))
        (lw-complex-diskp
         (lw-complex-sub (lw-complex-polynomial coefficients point 0)
          (lw-polynomial-linear-factor-value roots (lw-polynomial-leading coefficients) point))
         epsilon))))
 :hints (("Goal" :use (lw-polynomial-approximate-factorization-error
                       lw-polynomial-factor-roots-data lw-polynomial-leading-valid)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-paf-left-commutes lw-paf-left-distributes lw-paf-fold-constants lw-paf-times-negative lw-paf-negative-times lw-paf-zero-times lw-paf-minus-one lw-paf-double-negative lw-paf-add-cancel lw-paf-double lw-paf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
