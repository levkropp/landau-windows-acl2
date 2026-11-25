(in-package "ACL2")

(include-book "weighted-power-sums")

; Finite coefficient blocks and first-order propagation. All bounds are
; closed rational disks; the backward counter makes every prefix explicit.

(local (defthm lw-psb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psb-times-negative (a b) (b a)))
                 :in-theory (disable lw-psb-times-negative)))))

(local (defthm lw-psb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psb-left-commutes)))))

(defun lw-power-block-boundedp (entries start count cap)
 (declare (xargs :measure (nfix count)))
 (if (zp count) t
  (and (lw-complex-diskp
        (lw-weighted-power-sum entries (+ start count -1)) cap)
       (lw-power-block-boundedp entries start (- count 1) cap))))

(local (defthm lw-psb-empty
 (implies (zp count) (lw-power-block-boundedp entries start count cap))
 :hints (("Goal" :in-theory (enable lw-power-block-boundedp)))))

(local (defun lw-psb-countdown (count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil (lw-psb-countdown (- count 1)))))

(defthm lw-power-block-at
 (implies (and (natp start) (natp count) (natp index)
               (<= start index) (< index (+ start count))
               (lw-power-block-boundedp entries start count cap))
          (lw-complex-diskp (lw-weighted-power-sum entries index) cap))
 :hints (("Goal" :induct (lw-power-block-boundedp entries start count cap)
          :in-theory (union-theories
 '(lw-psb-empty lw-power-block-boundedp lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-block-enlarge
 (implies (and (natp count) (rationalp cap) (rationalp larger) (<= cap larger)
               (lw-power-block-boundedp entries start count cap))
          (lw-power-block-boundedp entries start count larger))
 :hints (("Goal" :induct (lw-power-block-boundedp entries start count cap)
          :in-theory (union-theories
 '(lw-psb-empty lw-power-block-boundedp lw-complex-disk-enlarge lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-block-shrink
 (implies (and (natp start) (natp smaller) (natp count) (<= smaller count)
               (lw-power-block-boundedp entries start count cap))
          (lw-power-block-boundedp entries start smaller cap))
 :hints (("Goal" :induct (lw-psb-countdown smaller)
          :in-theory (union-theories
 '(lw-psb-empty (:induction lw-psb-countdown) lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:expand ((lw-power-block-boundedp entries start smaller cap))
            :use ((:instance lw-power-block-at (index (+ start smaller -1))))
            :in-theory (union-theories
 '(lw-psb-empty  lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psb-residual-bound
 (implies (and (consp entries) (lw-power-unit-systemp entries) (natp index)
               (lw-complex-diskp (lw-weighted-power-sum entries index) cap)
               (lw-complex-diskp (lw-weighted-power-sum entries (+ 1 index)) cap))
  (lw-complex-diskp
   (lw-weighted-power-sum (lw-power-difference-system (caar entries) (cdr entries)) index)
   (* 2 cap)))
 :hints (("Goal"
  :use (lw-power-unit-system-typed lw-power-sum-first-residual
        (:instance lw-complex-mul-disk (left (caar entries))
         (right (lw-weighted-power-sum entries index)) (radius 1) (other-radius cap))
        (:instance lw-complex-sub-disk
         (left (lw-weighted-power-sum entries (+ 1 index)))
         (right (lw-complex-mul (caar entries) (lw-weighted-power-sum entries index)))
         (radius cap) (other-radius cap)))
  :in-theory (union-theories
 '(lw-psb-empty lw-power-unit-systemp lw-complex-disk-data lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-power-difference-block
 (implies (and (consp entries) (lw-power-unit-systemp entries)
               (natp start) (natp count)
               (lw-power-block-boundedp entries start (+ 1 count) cap))
  (lw-power-block-boundedp
   (lw-power-difference-system (caar entries) (cdr entries)) start count (* 2 cap)))
 :hints (("Goal" :induct (lw-psb-countdown count)
          :in-theory (union-theories
 '(lw-psb-empty (:induction lw-psb-countdown) lw-power-block-boundedp lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-psb-residual-bound (index (+ start count -1)))
                  (:instance lw-power-block-at
                   (count (+ 1 count)) (index (+ start count -1)))
                  (:instance lw-power-block-at
                   (count (+ 1 count)) (index (+ start count))))
            :in-theory (union-theories
 '(lw-psb-empty  lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psb-next-bound
 (implies (and (consp entries) (lw-power-unit-systemp entries) (natp index)
               (lw-complex-diskp (lw-weighted-power-sum entries index) previous)
               (lw-complex-diskp
                (lw-weighted-power-sum
                 (lw-power-difference-system (caar entries) (cdr entries)) index)
                residual))
  (lw-complex-diskp (lw-weighted-power-sum entries (+ 1 index))
                    (+ previous residual)))
 :hints (("Goal"
  :use (lw-power-unit-system-typed lw-power-sum-first-difference
        (:instance lw-complex-mul-disk (left (caar entries))
         (right (lw-weighted-power-sum entries index)) (radius 1) (other-radius previous))
        (:instance lw-complex-add-disk
         (left (lw-complex-mul (caar entries) (lw-weighted-power-sum entries index)))
         (right (lw-weighted-power-sum
                 (lw-power-difference-system (caar entries) (cdr entries)) index))
         (radius previous) (other-radius residual)))
  :in-theory (union-theories
 '(lw-psb-empty lw-power-unit-systemp lw-complex-disk-data lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-power-first-order-prefix-bound
 (implies (and (consp entries) (lw-power-unit-systemp entries) (natp index)
               (rationalp initial) (<= 0 initial)
               (rationalp residual) (<= 0 residual)
               (lw-complex-diskp (lw-weighted-power-sum entries 0) initial)
               (lw-power-block-boundedp
                (lw-power-difference-system (caar entries) (cdr entries))
                0 index residual))
  (lw-power-block-boundedp entries 0 (+ 1 index) (+ initial (* index residual))))
 :hints (("Goal" :induct (lw-psb-countdown index)
          :in-theory (union-theories
 '(lw-psb-empty (:induction lw-psb-countdown) lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:expand ((lw-power-block-boundedp entries 0 (+ 1 index)
                       (+ initial (* index residual))))
            :use ((:instance lw-power-block-shrink
                    (entries (lw-power-difference-system (caar entries) (cdr entries)))
                    (start 0) (count index) (smaller (- index 1)) (cap residual))
                  (:instance lw-power-block-at
                    (start 0) (count index) (index (- index 1))
                    (cap (+ initial (* (- index 1) residual))))
                  (:instance lw-power-block-at
                    (entries (lw-power-difference-system (caar entries) (cdr entries)))
                    (start 0) (count index) (index (- index 1)) (cap residual))
                  (:instance lw-psb-next-bound
                    (index (- index 1)) (previous (+ initial (* (- index 1) residual))))
                  (:instance lw-power-block-enlarge
                    (start 0) (count index) (cap (+ initial (* (- index 1) residual)))
                    (larger (+ initial (* index residual)))))
            :in-theory (union-theories
 '(lw-psb-empty lw-power-block-boundedp lw-psb-left-commutes lw-psb-left-distributes lw-psb-fold-constants lw-psb-times-negative lw-psb-negative-times lw-psb-zero-times lw-psb-minus-one lw-psb-double-negative lw-psb-add-cancel lw-psb-double lw-psb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

