; Exact access to every edge of finite polygon paths, including explicit closure.
(in-package "ACL2")
(include-book "polynomial-square-path-control")
(local (in-theory (disable lw-ray-row-near-check lw-ray-row-avoids
 lw-polynomial-path-values lw-square-point-listp lw-square-containsp
 lw-complex-diskp lw-complex-sub lw-complex-polynomial)))
(local (defthm lw-pea-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pea-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pea-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pea-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pea-times-negative (a b) (b a)))
                 :in-theory (disable lw-pea-times-negative)))))

(local (defthm lw-pea-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pea-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pea-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pea-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pea-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pea-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pea-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pea-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pea-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pea-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pea-left-commutes)))))
(local (defthm lw-pea-nth-zero-one
 (and (equal (nth 0 points) (car points)) (equal (nth 1 points) (cadr points)))
 :hints (("Goal" :expand ((nth 0 points) (nth 1 points) (nth 0 (cdr points)))
 :in-theory (union-theories
 '(nth lw-pea-left-commutes lw-pea-left-distributes lw-pea-fold-constants lw-pea-times-negative lw-pea-negative-times lw-pea-zero-times lw-pea-minus-one lw-pea-double-negative lw-pea-add-cancel lw-pea-double lw-pea-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pea-two-points
 (implies (< 1 (len points)) (consp (cdr points)))
 :hints (("Goal" :in-theory (union-theories
 '(len endp lw-pea-left-commutes lw-pea-left-distributes lw-pea-fold-constants lw-pea-times-negative lw-pea-negative-times lw-pea-zero-times lw-pea-minus-one lw-pea-double-negative lw-pea-add-cancel lw-pea-double lw-pea-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-row-near-nth
 (implies (and (natp index) (< (+ 1 index) (len points))
               (lw-ray-row-near-check points points step))
 (lw-complex-diskp (lw-complex-sub (nth (+ 1 index) points) (nth index points)) step))
 :hints (("Goal" :induct (nth index points)
 :in-theory (union-theories
 '(lw-pea-nth-zero-one lw-pea-two-points nth len endp lw-ray-row-near-check fold-consts-in-+ lw-pea-left-commutes lw-pea-left-distributes lw-pea-fold-constants lw-pea-times-negative lw-pea-negative-times lw-pea-zero-times lw-pea-minus-one lw-pea-double-negative lw-pea-add-cancel lw-pea-double lw-pea-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-row-avoids-nth
 (implies (and (natp index) (< index (len points)) (lw-ray-row-avoids points radius))
 (not (lw-complex-diskp (nth index points) radius)))
 :hints (("Goal" :induct (nth index points)
 :in-theory (union-theories
 '(lw-pea-nth-zero-one lw-pea-two-points nth len endp lw-ray-row-avoids fold-consts-in-+ lw-pea-left-commutes lw-pea-left-distributes lw-pea-fold-constants lw-pea-times-negative lw-pea-negative-times lw-pea-zero-times lw-pea-minus-one lw-pea-double-negative lw-pea-add-cancel lw-pea-double lw-pea-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-path-values-nth
 (implies (and (natp index) (< index (len points)))
 (equal (nth index (lw-polynomial-path-values coefficients points))
        (lw-complex-polynomial coefficients (nth index points) 0)))
 :hints (("Goal" :induct (nth index points)
 :in-theory (union-theories
 '(lw-pea-nth-zero-one lw-pea-two-points nth len endp lw-polynomial-path-values fold-consts-in-+ lw-pea-left-commutes lw-pea-left-distributes lw-pea-fold-constants lw-pea-times-negative lw-pea-negative-times lw-pea-zero-times lw-pea-minus-one lw-pea-double-negative lw-pea-add-cancel lw-pea-double lw-pea-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-square-point-list-nth
 (implies (and (lw-square-point-listp anchor side points) (natp index) (< index (len points)))
 (lw-square-containsp anchor side (nth index points)))
 :hints (("Goal" :induct (nth index points)
 :in-theory (union-theories
 '(lw-pea-nth-zero-one lw-pea-two-points nth len endp lw-square-point-listp fold-consts-in-+ lw-pea-left-commutes lw-pea-left-distributes lw-pea-fold-constants lw-pea-times-negative lw-pea-negative-times lw-pea-zero-times lw-pea-minus-one lw-pea-double-negative lw-pea-add-cancel lw-pea-double lw-pea-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

