(in-package "ACL2")

(include-book "mobius-hyperbola-product")
(include-book "dirichlet-hyperbola-tail")
(include-book "dirichlet-node-mass")

; A product outside the hyperbola has at least one index above the
; square cutoff. The rectangle tail is bounded by the two mass products.

(local (defthm lw-mht-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mht-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mht-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mht-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mht-times-negative (a b) (b a)))
                 :in-theory (disable lw-mht-times-negative)))))

(local (defthm lw-mht-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mht-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mht-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mht-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mht-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mht-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mht-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mht-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mht-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mht-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-mht-left-commutes)))))

(local (deftheory lw-mht-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-mht-left-commutes lw-mht-left-distributes lw-mht-fold-constants
              lw-mht-times-negative lw-mht-negative-times lw-mht-zero-times
              lw-mht-minus-one lw-mht-double-negative lw-mht-add-cancel lw-mht-double lw-mht-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(local
 (defthm lw-mht-empty-mass
   (implies (<= upper lower) (equal (lw-dirichlet-node-mass upper lower nodes) 0))
   :hints (("Goal" :in-theory (union-theories '(lw-dirichlet-node-mass) (theory 'lw-mht-arithmetic))))))

(local
 (deftheory lw-mht-disk-theory
   (union-theories
    '(lw-dirichlet-node-rational lw-complex-ring-rational lw-complex-scale-rational
      lw-dirichlet-hyperbola-tail-row-rational lw-dirichlet-hyperbola-tail-sum-rational
      lw-complex-add-zero lw-complex-zero-disk lw-mht-empty-mass (:executable-counterpart lw-complexp))
    (theory 'lw-mht-arithmetic))))

(local
 (defthm lw-mht-contract-scale
   (implies (and (rationalp weight) (<= (abs weight) 1)
                 (lw-complex-diskp point radius))
            (lw-complex-diskp (lw-complex-scale weight point) radius))
   :hints (("Goal"
            :use (lw-complex-disk-data
                  (:instance lw-complex-scale-disk (factor weight))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale weight point))
                     (radius (* (abs weight) radius)) (cap radius))
                  (:instance lw-mht-multiply-order (a (abs weight)) (b 1) (factor radius)))
            :in-theory (union-theories '(abs) (theory 'lw-mht-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-mht-cell-disk
   (implies (and (posp divisor) (posp index) (natp total) (<= divisor total))
            (lw-complex-diskp (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) divisor) (lw-complex-mul (lw-dirichlet-node nodes divisor) (lw-dirichlet-node nodes index)))
                              (* (lw-complex-l1 (lw-dirichlet-node nodes divisor)) (lw-complex-l1 (lw-dirichlet-node nodes index)))))
   :hints (("Goal"
            :use ((:instance lw-mobius-prefix-table-coefficient-bound (value divisor) (limit total))
                  (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes divisor)))
                  (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes index)))
                  (:instance lw-complex-mul-disk (left (lw-dirichlet-node nodes divisor)) (right (lw-dirichlet-node nodes index))
                      (radius (lw-complex-l1 (lw-dirichlet-node nodes divisor))) (other-radius (lw-complex-l1 (lw-dirichlet-node nodes index))))
                  (:instance lw-mht-contract-scale (weight (lw-dirichlet-coefficient (lw-mobius-prefix-table total) divisor))
                      (point (lw-complex-mul (lw-dirichlet-node nodes divisor) (lw-dirichlet-node nodes index)))
                      (radius (* (lw-complex-l1 (lw-dirichlet-node nodes divisor)) (lw-complex-l1 (lw-dirichlet-node nodes index))))))
            :in-theory (union-theories '(lw-dirichlet-coefficient-rational) (theory 'lw-mht-disk-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-mht-possible-product
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= 0 b)) (<= 0 (* a b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-mht-row-bound
   (implies (and (posp divisor) (natp bound) (posp start) (natp total) (<= divisor total)
                 (natp cutoff) (<= (* start start) cutoff))
            (lw-complex-diskp (lw-dirichlet-hyperbola-tail-row divisor bound cutoff (lw-mobius-prefix-table total) nodes)
                              (* (lw-complex-l1 (lw-dirichlet-node nodes divisor)) (lw-dirichlet-node-mass bound (if (< start divisor) 0 start) nodes))))
   :hints (("Goal"
            :induct (lw-dirichlet-hyperbola-tail-row divisor bound cutoff (lw-mobius-prefix-table total) nodes)
            :in-theory (union-theories '(lw-dirichlet-hyperbola-tail-row lw-dirichlet-node-mass)
                                     (theory 'lw-mht-disk-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-hyperbola-square-containment (left divisor) (right bound))
                        (:instance lw-dirichlet-node-mass-data (upper (- bound 1)) (lower (if (< start divisor) 0 start)))
                        (:instance lw-dirichlet-node-mass-data (upper bound) (lower (if (< start divisor) 0 start)))
                        (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes divisor)))
                        (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes bound)))
                        (:instance lw-mht-cell-disk (index bound))
                        (:instance lw-mht-possible-product
                          (a (lw-complex-l1 (lw-dirichlet-node nodes divisor)))
                          (b (lw-complex-l1 (lw-dirichlet-node nodes bound))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-dirichlet-hyperbola-tail-row divisor (- bound 1) cutoff (lw-mobius-prefix-table total) nodes))
                          (radius (* (lw-complex-l1 (lw-dirichlet-node nodes divisor))
                                     (lw-dirichlet-node-mass (- bound 1) (if (< start divisor) 0 start) nodes)))
                          (cap (+ (* (lw-complex-l1 (lw-dirichlet-node nodes divisor))
                                     (lw-dirichlet-node-mass (- bound 1) (if (< start divisor) 0 start) nodes))
                                  (* (lw-complex-l1 (lw-dirichlet-node nodes divisor))
                                     (lw-complex-l1 (lw-dirichlet-node nodes bound))))))
                        (:instance lw-complex-add-disk
                         (left (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) divisor) (lw-complex-mul (lw-dirichlet-node nodes divisor) (lw-dirichlet-node nodes bound))))
                         (right (lw-dirichlet-hyperbola-tail-row divisor (- bound 1) cutoff (lw-mobius-prefix-table total) nodes))
                         (radius (* (lw-complex-l1 (lw-dirichlet-node nodes divisor)) (lw-complex-l1 (lw-dirichlet-node nodes bound))))
                         (other-radius (* (lw-complex-l1 (lw-dirichlet-node nodes divisor)) (lw-dirichlet-node-mass (- bound 1) (if (< start divisor) 0 start) nodes)))))
                  :in-theory (theory 'lw-mht-disk-theory)
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-mht-enlarge-positive-product
   (implies (and (lw-complex-diskp point radius)
                 (rationalp a) (rationalp b) (<= 0 a) (<= 0 b))
            (lw-complex-diskp point (+ radius (* a b))))
   :hints (("Goal"
            :use (lw-complex-disk-data lw-mht-possible-product
                  (:instance lw-complex-disk-enlarge (cap (+ radius (* a b)))))
            :in-theory (theory 'lw-mht-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-mobius-hyperbola-tail-mass-bound
  (implies (and (natp left) (natp bound) (posp start) (natp total) (<= left total)
                (natp cutoff) (<= (* start start) cutoff))
           (lw-complex-diskp (lw-dirichlet-hyperbola-tail-sum left bound cutoff (lw-mobius-prefix-table total) nodes)
                             (+ (* (lw-dirichlet-node-mass left 0 nodes) (lw-dirichlet-node-mass bound start nodes))
      (* (lw-dirichlet-node-mass left start nodes) (lw-dirichlet-node-mass bound 0 nodes)))))
  :hints (("Goal"
           :induct (lw-dirichlet-hyperbola-tail-sum left bound cutoff (lw-mobius-prefix-table total) nodes)
           :in-theory (union-theories '(lw-dirichlet-hyperbola-tail-sum lw-dirichlet-node-mass)
                                    (theory 'lw-mht-disk-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mht-row-bound (divisor left))
                       (:instance lw-dirichlet-node-mass-data (upper (- left 1)) (lower 0))
                       (:instance lw-dirichlet-node-mass-data (upper (- left 1)) (lower start))
                       (:instance lw-dirichlet-node-mass-data (upper bound) (lower 0))
                       (:instance lw-dirichlet-node-mass-data (upper bound) (lower start))
                       (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes left)))
                       (:instance lw-mht-enlarge-positive-product
                        (point (lw-complex-add
                                (lw-dirichlet-hyperbola-tail-row left bound cutoff (lw-mobius-prefix-table total) nodes)
                                (lw-dirichlet-hyperbola-tail-sum (- left 1) bound cutoff (lw-mobius-prefix-table total) nodes)))
                        (a (lw-complex-l1 (lw-dirichlet-node nodes left)))
                        (b (lw-dirichlet-node-mass bound start nodes))
                        (radius (+ (* (lw-complex-l1 (lw-dirichlet-node nodes left)) (lw-dirichlet-node-mass bound 0 nodes))
                                   (* (lw-dirichlet-node-mass (- left 1) 0 nodes) (lw-dirichlet-node-mass bound start nodes))
                                   (* (lw-dirichlet-node-mass (- left 1) start nodes) (lw-dirichlet-node-mass bound 0 nodes)))))
                       (:instance lw-complex-add-disk
                        (left (lw-dirichlet-hyperbola-tail-row left bound cutoff (lw-mobius-prefix-table total) nodes))
                        (right (lw-dirichlet-hyperbola-tail-sum (- left 1) bound cutoff (lw-mobius-prefix-table total) nodes))
                        (radius (* (lw-complex-l1 (lw-dirichlet-node nodes left)) (lw-dirichlet-node-mass bound (if (< start left) 0 start) nodes)))
                        (other-radius (+ (* (lw-dirichlet-node-mass (- left 1) 0 nodes) (lw-dirichlet-node-mass bound start nodes))
      (* (lw-dirichlet-node-mass (- left 1) start nodes) (lw-dirichlet-node-mass bound 0 nodes))))))
                 :in-theory (theory 'lw-mht-disk-theory)
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-mobius-weighted-prefix-mass-bound
  (implies (and (natp count) (natp total) (<= count total))
           (lw-complex-diskp (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table total) nodes)
                             (lw-dirichlet-node-mass count 0 nodes)))
  :hints (("Goal"
           :induct (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table total) nodes)
           :in-theory (union-theories '(lw-dirichlet-weighted-prefix lw-dirichlet-weighted-prefix-rational lw-dirichlet-node-mass)
                                    (theory 'lw-mht-disk-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-dirichlet-node-mass-data (upper (- count 1)) (lower 0))
                       (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes count)))
                       (:instance lw-mobius-prefix-table-coefficient-bound (value count) (limit total))
                       (:instance lw-mht-contract-scale
                        (weight (lw-dirichlet-coefficient (lw-mobius-prefix-table total) count))
                        (point (lw-dirichlet-node nodes count)) (radius (lw-complex-l1 (lw-dirichlet-node nodes count))))
                       (:instance lw-complex-add-disk
                        (left (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) count)
                                                (lw-dirichlet-node nodes count)))
                        (right (lw-dirichlet-weighted-prefix (- count 1) (lw-mobius-prefix-table total) nodes))
                        (radius (lw-complex-l1 (lw-dirichlet-node nodes count)))
                        (other-radius (lw-dirichlet-node-mass (- count 1) 0 nodes))))
                 :in-theory (union-theories '(lw-dirichlet-coefficient-rational) (theory 'lw-mht-disk-theory))
                 :do-not-induct t)))
  :rule-classes nil)
