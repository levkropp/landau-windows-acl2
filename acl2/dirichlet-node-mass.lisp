(in-package "ACL2")

(include-book "dirichlet-right-dyadic-mass")

; Mass of the nodes with indices in (lower, upper], in the order in
; which the rectangle and hyperbola sums consume the sample table.

(local (defthm lw-dnm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dnm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dnm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-dnm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-dnm-times-negative (a b) (b a)))
                 :in-theory (disable lw-dnm-times-negative)))))

(local (defthm lw-dnm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-dnm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-dnm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-dnm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-dnm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-dnm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-dnm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-dnm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dnm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dnm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-dnm-left-commutes)))))

(local (deftheory lw-dnm-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-dnm-left-commutes lw-dnm-left-distributes lw-dnm-fold-constants
              lw-dnm-times-negative lw-dnm-negative-times lw-dnm-zero-times
              lw-dnm-minus-one lw-dnm-double-negative lw-dnm-add-cancel lw-dnm-double lw-dnm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-dirichlet-node-mass (upper lower nodes)
  (declare (xargs :measure (nfix upper)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (or (zp upper) (<= upper lower)) 0
    (+ (lw-complex-l1 (lw-dirichlet-node nodes upper))
       (lw-dirichlet-node-mass (- upper 1) lower nodes))))

(defthm lw-dirichlet-node-mass-data
  (and (rationalp (lw-dirichlet-node-mass upper lower nodes))
       (<= 0 (lw-dirichlet-node-mass upper lower nodes)))
  :hints (("Goal"
           :induct (lw-dirichlet-node-mass upper lower nodes)
           :in-theory (union-theories '(lw-dirichlet-node-mass) (theory 'lw-dnm-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-dirichlet-node-rational (table nodes) (index upper))
                       (:instance lw-complex-l1-bound (point (lw-dirichlet-node nodes upper))))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-dnm-sample-mass-step
   (implies (and (rationalp rate) (rationalp height) (rationalp error) (< 0 error)
                 (natp lower) (posp upper) (< lower upper))
            (equal (lw-dirichlet-sample-mass rate height (+ 1 lower) (- upper lower) error)
                   (+ (lw-complex-l1 (lw-dirichlet-sample rate height upper error error))
                      (lw-dirichlet-sample-mass rate height (+ 1 lower) (- (- upper lower) 1) error))))
   :hints (("Goal"
            :use ((:instance lw-dirichlet-sample-mass-split (start (+ 1 lower))
                    (first (- (- upper lower) 1)) (last 1))
                  (:instance lw-dirichlet-sample-mass-rational (start (+ 1 lower)) (count (- (- upper lower) 1)))
                  (:instance lw-dirichlet-sample-rational (index upper) (log-error error) (node-error error))
                  (:instance lw-complex-l1-bound (point (lw-dirichlet-sample rate height upper error error))))
            :expand ((lw-dirichlet-sample-mass rate height upper 1 error)
                     (lw-dirichlet-sample-mass rate height (+ 1 upper) 0 error))
            :in-theory (theory 'lw-dnm-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-dnm-empty-sample-mass
   (equal (lw-dirichlet-sample-mass rate height start 0 error) 0)
   :hints (("Goal" :in-theory (union-theories '(lw-dirichlet-sample-mass) (theory 'lw-dnm-arithmetic))))))

(defthm lw-dirichlet-node-mass-sample-table
  (implies (and (rationalp rate) (rationalp height) (rationalp error) (< 0 error)
                (natp total) (natp lower) (natp upper) (<= lower upper) (<= upper total))
           (equal (lw-dirichlet-node-mass upper lower (lw-dirichlet-sample-table rate height total error error))
                  (lw-dirichlet-sample-mass rate height (+ 1 lower) (- upper lower) error)))
  :hints (("Goal"
           :induct (lw-dirichlet-node-mass upper lower (lw-dirichlet-sample-table rate height total error error))
           :in-theory (union-theories '(lw-dirichlet-node-mass lw-dnm-empty-sample-mass) (theory 'lw-dnm-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-dnm-sample-mass-step
                       (:instance lw-dirichlet-node-mass-data (upper (- upper 1))
                          (nodes (lw-dirichlet-sample-table rate height total error error)))
                       (:instance lw-dirichlet-sample-table-lookup (count total) (index upper)
                          (log-error error) (node-error error))
                       (:instance lw-dirichlet-node-rational
                          (table (lw-dirichlet-sample-table rate height total error error)) (index upper))
                       (:instance lw-complex-l1-bound
                          (point (lw-dirichlet-node (lw-dirichlet-sample-table rate height total error error) upper))))
                 :do-not-induct t)))
  :rule-classes nil)
