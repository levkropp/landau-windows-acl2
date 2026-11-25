(in-package "ACL2")

(include-book "polynomial-factor-roots")
(include-book "unit-square-linear-bounds")

; Finite product paths for the complete rational approximate factor model.

(local (defthm lw-pfp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pfp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pfp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pfp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pfp-times-negative (a b) (b a)))
                 :in-theory (disable lw-pfp-times-negative)))))

(local (defthm lw-pfp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pfp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pfp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pfp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pfp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pfp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pfp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pfp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pfp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pfp-left-commutes)))))
(defun lw-unit-square-roots-awayp (roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) (equal roots nil)
  (and (lw-complexp (car roots)) (not (lw-unit-square-pointp (car roots)))
       (lw-unit-square-roots-awayp (cdr roots)))))

(defun lw-unit-square-factor-count (roots)
 (declare (xargs :measure (acl2-count roots) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) 0
  (+ (lw-unit-square-root-index (car roots)) (lw-unit-square-factor-count (cdr roots)))))

(defthm lw-unit-square-roots-away-data
 (implies (lw-unit-square-roots-awayp roots) (lw-ray-pointsp roots))
 :hints (("Goal" :induct (lw-unit-square-roots-awayp roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-roots-awayp) lw-unit-square-roots-awayp lw-ray-pointsp endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-factor-count-data
 (and (natp (lw-unit-square-factor-count roots))
      (<= (lw-unit-square-factor-count roots) (len roots)))
 :hints (("Goal" :induct (lw-unit-square-factor-count roots)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-unit-square-factor-count) lw-unit-square-factor-count lw-unit-square-root-index len endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-polynomial-factor-path-values (roots leading points)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) nil
  (cons (lw-polynomial-linear-factor-value roots leading (car points))
        (lw-polynomial-factor-path-values roots leading (cdr points)))))

(defthm lw-polynomial-factor-path-data
 (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-ray-pointsp points))
  (and (lw-ray-pointsp (lw-polynomial-factor-path-values roots leading points))
       (equal (len (lw-polynomial-factor-path-values roots leading points)) (len points))
       (equal (consp (lw-polynomial-factor-path-values roots leading points)) (consp points))))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values roots leading points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-polynomial-linear-factor-value-rational lw-ray-pointsp len endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-factor-path-head
 (implies (consp points)
  (equal (car (lw-polynomial-factor-path-values roots leading points))
         (lw-polynomial-linear-factor-value roots leading (car points))))
 :hints (("Goal" :expand ((lw-polynomial-factor-path-values roots leading points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-factor-path-last
 (equal (lw-ray-path-last (lw-polynomial-linear-factor-value roots leading current)
                          (lw-polynomial-factor-path-values roots leading points))
        (lw-polynomial-linear-factor-value roots leading (lw-ray-path-last current points)))
 :hints (("Goal" :induct (lw-ray-path-last current points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-ray-path-last) lw-ray-path-last lw-polynomial-factor-path-values endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-factor-path-closed
 (implies (and (consp points) (equal (lw-ray-row-last points) (car points)))
  (equal (lw-ray-row-last (lw-polynomial-factor-path-values roots leading points))
         (car (lw-polynomial-factor-path-values roots leading points))))
 :hints (("Goal" :expand ((lw-polynomial-factor-path-values roots leading points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-row-last lw-polynomial-factor-path-last lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-polynomial-factor-path-product
 (implies (and (lw-complexp root) (lw-ray-pointsp roots) (lw-complexp leading) (lw-ray-pointsp points))
  (equal (lw-polynomial-factor-path-values (cons root roots) leading points)
         (lw-ray-pointwise-products (lw-ray-translate-points root points)
                                    (lw-polynomial-factor-path-values roots leading points))))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values roots leading points)
          :expand ((lw-polynomial-linear-factor-value (cons root roots) leading (car points)))
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-ray-pointwise-products lw-ray-translate-points lw-polynomial-linear-factor-value-rational lw-complex-ring-rational lw-complex-mul-commutative lw-ray-pointsp endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pfp-empty-factors
 (equal (lw-polynomial-linear-factor-value nil leading point) leading)
 :hints (("Goal" :expand ((lw-polynomial-linear-factor-value nil leading point)) :in-theory (union-theories
 '(fold-consts-in-+ lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pfp-constant-path-zero
 (implies (lw-complexp leading)
  (equal (lw-ray-path-index leading (lw-polynomial-factor-path-values nil leading points)) 0))
 :hints (("Goal" :induct (lw-polynomial-factor-path-values nil leading points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-pfp-empty-factors lw-ray-path-index lw-ray-crossing-self endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))
(local (defthm lw-pfp-constant-path-last
 (equal (lw-ray-path-last leading (lw-polynomial-factor-path-values nil leading points)) leading)
 :hints (("Goal" :induct (lw-polynomial-factor-path-values nil leading points)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-polynomial-factor-path-values) lw-polynomial-factor-path-values lw-pfp-empty-factors lw-ray-path-last endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-constant-factor-path-index
 (implies (lw-complexp leading)
  (equal (lw-ray-polygon-index (lw-polynomial-factor-path-values nil leading points)) 0))
 :hints (("Goal" :expand ((lw-polynomial-factor-path-values nil leading points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-polygon-index lw-pfp-empty-factors lw-pfp-constant-path-zero lw-pfp-constant-path-last lw-ray-crossing-self endp lw-pfp-left-commutes lw-pfp-left-distributes lw-pfp-fold-constants lw-pfp-times-negative lw-pfp-negative-times lw-pfp-zero-times lw-pfp-minus-one lw-pfp-double-negative lw-pfp-add-cancel lw-pfp-double lw-pfp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not-induct t)))
