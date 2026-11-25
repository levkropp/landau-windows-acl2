(in-package "ACL2")

(include-book "mobius-hyperbola-tail")

; Combine the exact divisor cancellation with the primitive rounding
; budget and the bound for pairs outside the finite hyperbola.

(local (defthm lw-dri-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dri-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dri-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dri-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dri-times-negative (a b) (b a)))
                 :in-theory (disable lw-dri-times-negative)))))

(local (defthm lw-dri-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dri-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dri-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dri-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dri-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dri-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dri-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dri-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dri-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dri-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dri-left-commutes)))))

(local (deftheory lw-dri-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-dri-left-commutes lw-dri-left-distributes lw-dri-fold-constants
              lw-dri-times-negative lw-dri-negative-times lw-dri-zero-times
              lw-dri-minus-one lw-dri-double-negative lw-dri-add-cancel lw-dri-double lw-dri-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(local
 (defthm lw-dri-sample-one
   (equal (lw-dirichlet-sample rate height 1 log-error node-error) (cons 1 0))
   :hints (("Goal" :in-theory (union-theories '(lw-dirichlet-sample) (theory 'lw-dri-arithmetic))))))

(defthm lw-mobius-rectangle-inverse-error
  (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
                (posp count) (posp start) (<= (* start start) count)
                (rationalp request) (< 0 request))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-mul (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table count) (lw-dirichlet-sample-table rate height count request request))
                      (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height count request request)))
                            (cons 1 0))
            (+ (* 2 (lw-dirichlet-node-mass count 0 (lw-dirichlet-sample-table rate height count request request))
         (lw-dirichlet-node-mass count start (lw-dirichlet-sample-table rate height count request request)))
               (* (lw-dirichlet-hyperbola-cost rate height count count count) request))))
  :hints (("Goal"
           :use ((:instance lw-mobius-prefix-table-hyperbola-identity (limit count) (nodes (lw-dirichlet-sample-table rate height count request request)))
                 (:instance lw-dirichlet-sample-table-lookup (index 1) (log-error request) (node-error request))
                 (:instance lw-dirichlet-rectangle-hyperbola-difference (left count) (bound count) (cutoff count)
                  (weights (lw-mobius-prefix-table count)) (nodes (lw-dirichlet-sample-table rate height count request request)))
                 (:instance lw-mobius-hyperbola-tail-mass-bound (left count) (bound count) (cutoff count) (total count)
                  (nodes (lw-dirichlet-sample-table rate height count request request)))
                 (:instance lw-mobius-hyperbola-product-error (left count) (bound count) (limit count) (total count) (error request))
                 (:instance lw-dirichlet-node-mass-data (upper count) (lower 0) (nodes (lw-dirichlet-sample-table rate height count request request)))
                 (:instance lw-dirichlet-node-mass-data (upper count) (lower start) (nodes (lw-dirichlet-sample-table rate height count request request)))
                 (:instance lw-complex-difference-triangle
                  (left (lw-complex-mul (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table count) (lw-dirichlet-sample-table rate height count request request))
                      (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height count request request))))
                  (middle (lw-dirichlet-hyperbola-product-sum count count count (lw-mobius-prefix-table count)
                                                (lw-dirichlet-sample-table rate height count request request)))
                  (right (cons 1 0)) (radius (* 2 (lw-dirichlet-node-mass count 0 (lw-dirichlet-sample-table rate height count request request))
         (lw-dirichlet-node-mass count start (lw-dirichlet-sample-table rate height count request request)))) (other-radius (* (lw-dirichlet-hyperbola-cost rate height count count count) request))))
           :in-theory (union-theories
                       '(lw-dirichlet-node-prefix-rational lw-dirichlet-weighted-prefix-rational
                         lw-dirichlet-hyperbola-product-sum-rational lw-complex-ring-rational
                         lw-dri-sample-one (:executable-counterpart lw-complexp))
                       (theory 'lw-dri-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-dri-inverse-quarter
   (implies (and (rationalp cap) (< 0 cap))
            (equal (* cap (* 1/4 (/ cap))) 1/4))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x cap)))
            :in-theory (disable inverse-of-*)))
   :rule-classes nil))

(local
 (defthm lw-dri-unit-product-separation
   (implies (and (rationalp cap) (< 0 cap)
                 (lw-complex-diskp inverse cap)
                 (lw-complex-diskp (lw-complex-sub (lw-complex-mul inverse ordinary) (cons 1 0)) 1/2))
            (not (lw-complex-diskp ordinary (* 1/4 (/ cap)))))
   :hints (("Goal"
            :use ((:instance lw-complex-mul-disk (left inverse) (right ordinary)
                   (radius cap) (other-radius (* 1/4 (/ cap))))
                  (:instance lw-complex-disk-coordinates (point (lw-complex-mul inverse ordinary)) (radius 1/4))
                  (:instance lw-complex-disk-coordinates
                   (point (lw-complex-sub (lw-complex-mul inverse ordinary) (cons 1 0))) (radius 1/2))
                  lw-dri-inverse-quarter
                  (:instance lw-complex-disk-data (point ordinary) (radius (* 1/4 (/ cap))))
                  (:instance lw-complex-disk-data (point inverse) (radius cap)))
            :in-theory (union-theories '(lw-complex-sub abs lw-complex-ring-rational lw-complexp) (theory 'lw-dri-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-dirichlet-prefix-clearance-from-mobius
  (implies (and (rationalp rate) (<= 0 rate) (rationalp height)
                (posp count) (posp start) (<= (* start start) count)
                (rationalp request) (< 0 request)
                (rationalp cap) (< 0 cap)
                (<= (lw-dirichlet-node-mass count 0 (lw-dirichlet-sample-table rate height count request request)) cap)
                (<= (+ (* 2 (lw-dirichlet-node-mass count 0 (lw-dirichlet-sample-table rate height count request request))
         (lw-dirichlet-node-mass count start (lw-dirichlet-sample-table rate height count request request)))
                        (* (lw-dirichlet-hyperbola-cost rate height count count count) request)) 1/2))
           (not (lw-complex-diskp (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height count request request)) (* 1/4 (/ cap)))))
  :hints (("Goal"
           :use (lw-mobius-rectangle-inverse-error
                 (:instance lw-mobius-weighted-prefix-mass-bound (total count) (nodes (lw-dirichlet-sample-table rate height count request request)))
                 (:instance lw-complex-disk-enlarge (point (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table count) (lw-dirichlet-sample-table rate height count request request))) (radius (lw-dirichlet-node-mass count 0 (lw-dirichlet-sample-table rate height count request request))))
                 (:instance lw-complex-disk-enlarge
                  (point (lw-complex-sub (lw-complex-mul (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table count) (lw-dirichlet-sample-table rate height count request request))
                      (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height count request request))) (cons 1 0)))
                  (radius (+ (* 2 (lw-dirichlet-node-mass count 0 (lw-dirichlet-sample-table rate height count request request))
         (lw-dirichlet-node-mass count start (lw-dirichlet-sample-table rate height count request request))) (* (lw-dirichlet-hyperbola-cost rate height count count count) request))) (cap 1/2))
                 (:instance lw-dri-unit-product-separation (inverse (lw-dirichlet-weighted-prefix count (lw-mobius-prefix-table count) (lw-dirichlet-sample-table rate height count request request))) (ordinary (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height count request request)))))
           :in-theory (theory 'lw-dri-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
