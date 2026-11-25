(in-package "ACL2")

(include-book "mobius-sieve-inversion")
(include-book "dirichlet-hyperbola-product")

; Finite pair products with Möbius coefficients, using the existing
; Dirichlet hyperbola rows and their common primitive-precision budget.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
                           lw-complex-mul lw-complex-diskp lw-diskp lw-dirichlet-sample
                           lw-mobius-prefix-table lw-dirichlet-sample-table
                           lw-dirichlet-coefficient lw-dirichlet-node lw-dirichlet-pair-cost
                           lw-dirichlet-hyperbola-row-reindex lw-dirichlet-hyperbola-reindex
                           lw-complex-sub-add-first lw-complex-sub-add-cancel
                           lw-complex-scale-product lw-complex-add-commutative
                           lw-complex-mul-commutative)))

(local
 (defthm lw-mhp-times-negative
   (equal (* factor (- value)) (- (* factor value)))
   :hints (("Goal" :use ((:instance distributivity (x factor) (y value) (z (- value))))
                    :in-theory (disable distributivity)))))

(local (defthm lw-mhp-scale-sub
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
         (lw-complex-scale factor (lw-complex-sub a b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-sub)))))

(local
 (defthm lw-mhp-multiply-order
   (implies (and (rationalp a) (rationalp b) (<= a b)
                 (rationalp factor) (<= 0 factor))
            (<= (* a factor) (* b factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-mhp-scale-cost-order
   (implies (and (rationalp weight) (<= (abs weight) 1) (posp left)
                 (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
            (<= (* (abs weight) cost error) (* left cost error)))
   :hints (("Goal"
            :use ((:instance lw-mhp-multiply-order (a (abs weight)) (b left) (factor (* cost error)))
                  (:instance lw-mhp-multiply-order (a 0) (b cost) (factor error)))
            :in-theory (disable lw-mhp-times-negative commutativity-of-*)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-mhp-weighted-pair
   (implies
    (and (rationalp rate) (<= 0 rate) (rationalp height)
         (posp left) (posp right) (rationalp error) (< 0 error)
         (rationalp weight) (<= (abs weight) 1))
    (lw-complex-diskp
     (lw-complex-sub
      (lw-complex-scale weight
       (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                       (lw-dirichlet-sample rate height right error error)))
      (lw-complex-scale weight
       (lw-dirichlet-sample rate height (* left right) error error)))
     (* left (lw-dirichlet-pair-cost rate height left right) error)))
   :hints (("Goal"
    :use (lw-dirichlet-sample-product-error lw-dirichlet-pair-cost-valid
          (:instance lw-mhp-scale-cost-order (cost (lw-dirichlet-pair-cost rate height left right)))
          (:instance lw-complex-scale-disk
           (factor weight)
           (point (lw-complex-sub
                   (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                                   (lw-dirichlet-sample rate height right error error))
                   (lw-dirichlet-sample rate height (* left right) error error)))
           (radius (* (lw-dirichlet-pair-cost rate height left right) error)))
          (:instance lw-complex-disk-enlarge
           (point (lw-complex-scale weight
                   (lw-complex-sub
                    (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                                    (lw-dirichlet-sample rate height right error error))
                    (lw-dirichlet-sample rate height (* left right) error error))))
           (radius (* (abs weight) (lw-dirichlet-pair-cost rate height left right) error))
           (cap (* left (lw-dirichlet-pair-cost rate height left right) error))))
    :in-theory (disable lw-dirichlet-sample-product-error lw-dirichlet-pair-cost-valid
                        lw-complex-scale-disk lw-complex-disk-enlarge
                        lw-complex-sub-add)
    :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-mobius-dirichlet-pair-error
   (implies
    (and (rationalp rate) (<= 0 rate) (rationalp height)
         (posp left) (posp right) (rationalp error) (< 0 error)
         (natp total) (<= left total))
    (lw-complex-diskp
     (lw-complex-sub
      (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) left)
       (lw-complex-mul (lw-dirichlet-sample rate height left error error)
                       (lw-dirichlet-sample rate height right error error)))
      (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) left)
       (lw-dirichlet-sample rate height (* left right) error error)))
     (* left (lw-dirichlet-pair-cost rate height left right) error)))
   :hints (("Goal"
    :use ((:instance lw-mobius-prefix-table-coefficient-bound (value left) (limit total))
          (:instance lw-mhp-weighted-pair
           (weight (lw-dirichlet-coefficient (lw-mobius-prefix-table total) left))))
    :in-theory (disable lw-mhp-scale-sub lw-complex-sub-add)
    :do-not-induct t))
   :rule-classes nil))

(local (in-theory (disable lw-mhp-scale-sub)))

(local (defthm lw-mhp-add-errors
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (lw-complex-diskp (lw-complex-sub a b) radius)
               (lw-complex-diskp (lw-complex-sub c d) other-radius))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add a c) (lw-complex-add b d))
                    (+ radius other-radius)))
 :hints (("Goal"
  :use ((:instance lw-complex-sub-add (a a) (b c) (c b) (d d))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub a b)) (right (lw-complex-sub c d))))
  :in-theory (disable lw-complex-sub-add lw-complex-add-disk)
  :do-not-induct t))
 :rule-classes nil))


(local
 (defthm lw-mhp-sub-self
   (equal (lw-complex-sub point point) (cons 0 0))
   :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-mhp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (deftheory lw-mhp-arithmetic (union-theories
            '(fold-consts-in-+
              lw-mhp-times-negative
              lw-mhp-left-commutes natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(local
 (deftheory lw-mhp-row-theory
   (union-theories
    '(lw-dirichlet-hyperbola-product-row-rational lw-dirichlet-hyperbola-row-rational
      lw-dirichlet-hyperbola-product-sum-rational lw-dirichlet-hyperbola-sum-rational
      lw-dirichlet-sample-table-lookup lw-dirichlet-sample-rational
      lw-dirichlet-node-rational lw-dirichlet-coefficient-rational
      lw-complex-scale-rational lw-complex-ring-rational lw-complex-add-zero
      lw-complex-zero-disk lw-mhp-sub-self (:executable-counterpart lw-complexp)
      (:rewrite lw-complex-disk-data))
    (theory 'lw-mhp-arithmetic))))

(defthm lw-mobius-hyperbola-product-row-error
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (posp divisor) (natp bound) (natp limit) (natp total)
               (<= divisor total) (<= bound total) (<= limit total)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-dirichlet-hyperbola-product-row
     divisor bound limit (lw-mobius-prefix-table total)
     (lw-dirichlet-sample-table rate height total error error))
    (lw-dirichlet-hyperbola-row
     divisor bound limit (lw-mobius-prefix-table total)
     (lw-dirichlet-sample-table rate height total error error)))
   (* (lw-dirichlet-hyperbola-row-cost rate height divisor bound limit) error)))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-product-row
           divisor bound limit (lw-mobius-prefix-table total)
           (lw-dirichlet-sample-table rate height total error error))
  :in-theory (union-theories
              '(lw-dirichlet-hyperbola-product-row lw-dirichlet-hyperbola-row lw-dirichlet-hyperbola-row-cost)
              (theory 'lw-mhp-row-theory))
  :do-not '(generalize fertilize))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-hyperbola-row-cost-valid (bound (- bound 1)))
           (:instance lw-dirichlet-pair-cost-valid (left divisor) (right bound))
           (:instance lw-mobius-dirichlet-pair-error (left divisor) (right bound))
           (:instance lw-mhp-add-errors
            (a (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) divisor)
              (lw-complex-mul (lw-dirichlet-sample rate height divisor error error)
                              (lw-dirichlet-sample rate height bound error error))))
            (b (lw-complex-scale (lw-dirichlet-coefficient (lw-mobius-prefix-table total) divisor)
              (lw-dirichlet-sample rate height (* divisor bound) error error)))
            (c (lw-dirichlet-hyperbola-product-row
              divisor (- bound 1) limit (lw-mobius-prefix-table total)
              (lw-dirichlet-sample-table rate height total error error)))
            (d (lw-dirichlet-hyperbola-row
              divisor (- bound 1) limit (lw-mobius-prefix-table total)
              (lw-dirichlet-sample-table rate height total error error)))
            (radius (* divisor (lw-dirichlet-pair-cost rate height divisor bound) error))
            (other-radius (* (lw-dirichlet-hyperbola-row-cost rate height divisor (- bound 1) limit) error))))
     :in-theory (theory 'lw-mhp-row-theory)
     :do-not-induct t))))

(local (in-theory (disable lw-dirichlet-hyperbola-product-row lw-dirichlet-hyperbola-cost)))

(defthm lw-mobius-hyperbola-product-error
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
               (natp left) (natp bound) (natp limit) (natp total)
               (<= left total) (<= bound total) (<= limit total)
               (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-dirichlet-hyperbola-product-sum
     left bound limit (lw-mobius-prefix-table total)
     (lw-dirichlet-sample-table rate height total error error))
    (lw-dirichlet-hyperbola-sum
     left bound limit (lw-mobius-prefix-table total)
     (lw-dirichlet-sample-table rate height total error error)))
   (* (lw-dirichlet-hyperbola-cost rate height left bound limit) error)))
 :hints (("Goal"
  :induct (lw-dirichlet-hyperbola-product-sum
           left bound limit (lw-mobius-prefix-table total)
           (lw-dirichlet-sample-table rate height total error error))
  :in-theory (union-theories
              '(lw-dirichlet-hyperbola-product-sum lw-dirichlet-hyperbola-sum lw-dirichlet-hyperbola-cost)
              (theory 'lw-mhp-row-theory))
  :do-not '(generalize fertilize))
  (and stable-under-simplificationp
   '(:use ((:instance lw-dirichlet-hyperbola-cost-valid (left (- left 1)))
           (:instance lw-dirichlet-hyperbola-row-cost-valid (divisor left))
           (:instance lw-mobius-hyperbola-product-row-error (divisor left))
           (:instance lw-mhp-add-errors
            (a (lw-dirichlet-hyperbola-product-row
              left bound limit (lw-mobius-prefix-table total)
              (lw-dirichlet-sample-table rate height total error error)))
            (b (lw-dirichlet-hyperbola-row
              left bound limit (lw-mobius-prefix-table total)
              (lw-dirichlet-sample-table rate height total error error)))
            (c (lw-dirichlet-hyperbola-product-sum
              (- left 1) bound limit (lw-mobius-prefix-table total)
              (lw-dirichlet-sample-table rate height total error error)))
            (d (lw-dirichlet-hyperbola-sum
              (- left 1) bound limit (lw-mobius-prefix-table total)
              (lw-dirichlet-sample-table rate height total error error)))
            (radius (* (lw-dirichlet-hyperbola-row-cost rate height left bound limit) error))
            (other-radius (* (lw-dirichlet-hyperbola-cost rate height (- left 1) bound limit) error))))
     :in-theory (theory 'lw-mhp-row-theory)
     :do-not-induct t))))
