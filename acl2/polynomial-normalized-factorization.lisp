(in-package "ACL2")

(include-book "polynomial-trim")
(include-book "polynomial-approximate-factorization")

; Complete approximate factorization for arbitrary coefficient lists,
; including padding, constants and the zero polynomial.

(local (defthm lw-pnf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pnf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pnf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pnf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pnf-times-negative (a b) (b a)))
                 :in-theory (disable lw-pnf-times-negative)))))

(local (defthm lw-pnf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pnf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pnf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pnf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pnf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pnf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pnf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pnf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pnf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pnf-left-commutes)))))
(defun lw-polynomial-normalized-factor-roots (coefficients bound epsilon)
 (lw-polynomial-factor-roots (lw-polynomial-trim coefficients) bound epsilon))

(local (defthm lw-pnf-empty-coefficients
 (implies (and (lw-complex-coefficientsp coefficients) (not (consp coefficients)))
  (equal coefficients nil))
 :rule-classes nil
 :hints (("Goal" :expand ((lw-complex-coefficientsp coefficients)) :in-theory (union-theories
 '(fold-consts-in-+ endp lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pnf-empty-roots
 (equal (lw-polynomial-factor-roots nil bound epsilon) nil)
 :hints (("Goal" :expand ((lw-polynomial-factor-roots nil bound epsilon))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-inputp lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-normalized-factor-roots-data
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp bound) (<= 0 bound)
               (rationalp epsilon) (< 0 epsilon))
  (and (lw-ray-pointsp (lw-polynomial-normalized-factor-roots coefficients bound epsilon))
       (equal (len (lw-polynomial-normalized-factor-roots coefficients bound epsilon))
              (len (lw-polynomial-without-leading (lw-polynomial-trim coefficients))))))
 :hints (("Goal" :cases ((consp (lw-polynomial-trim coefficients)))
  :use (lw-polynomial-trim-valid lw-polynomial-trim-nonzero-leading
        (:instance lw-pnf-empty-coefficients (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-factor-roots-data (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-leading-valid (coefficients (lw-polynomial-trim coefficients))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-normalized-factor-roots lw-polynomial-factor-inputp lw-pnf-empty-roots (:executable-counterpart lw-polynomial-without-leading) lw-ray-pointsp len endp lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-pnf-empty-value
 (equal (lw-polynomial-linear-factor-value nil leading point) leading)
 :hints (("Goal" :expand ((lw-polynomial-linear-factor-value nil leading point)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pnf-empty-polynomial
 (equal (lw-complex-polynomial nil point offset) (cons 0 0))
 :hints (("Goal" :expand ((lw-complex-polynomial nil point offset)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pnf-zero-error
 (implies (and (rationalp epsilon) (<= 0 epsilon))
  (lw-complex-diskp (lw-complex-sub (cons 0 0) (cons 0 0)) epsilon))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-diskp lw-diskp lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-normalized-approximate-factorization
 (implies (and (lw-complex-coefficientsp coefficients) (rationalp bound) (<= 0 bound)
               (rationalp epsilon) (< 0 epsilon) (lw-complex-diskp point bound))
  (let ((roots (lw-polynomial-normalized-factor-roots coefficients bound epsilon))
        (leading (lw-polynomial-leading (lw-polynomial-trim coefficients))))
   (and (lw-ray-pointsp roots)
        (equal (len roots) (len (lw-polynomial-without-leading (lw-polynomial-trim coefficients))))
        (lw-complex-diskp
         (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                         (lw-polynomial-linear-factor-value roots leading point))
         epsilon))))
 :hints (("Goal" :cases ((consp (lw-polynomial-trim coefficients)))
  :use (lw-polynomial-normalized-factor-roots-data lw-polynomial-trim-valid lw-polynomial-trim-nonzero-leading
        (:instance lw-pnf-empty-coefficients (coefficients (lw-polynomial-trim coefficients)))
        (:instance lw-polynomial-trim-evaluation (offset 0))
        (:instance lw-polynomial-approximate-factorization-error (coefficients (lw-polynomial-trim coefficients))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-normalized-factor-roots lw-polynomial-factor-inputp lw-pnf-empty-roots lw-pnf-empty-value lw-pnf-empty-polynomial lw-pnf-zero-error lw-complex-disk-data (:executable-counterpart lw-polynomial-leading) lw-pnf-left-commutes lw-pnf-left-distributes lw-pnf-fold-constants lw-pnf-times-negative lw-pnf-negative-times lw-pnf-zero-times lw-pnf-minus-one lw-pnf-double-negative lw-pnf-add-cancel lw-pnf-double lw-pnf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
