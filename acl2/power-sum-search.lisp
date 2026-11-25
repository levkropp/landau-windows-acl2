(in-package "ACL2")

(include-book "power-sum-reversal")

; A bounded, executable large-term search. A nonzero total weight forces
; a term outside the explicit disk in every block of M consecutive orders.

(local (defthm lw-pss-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pss-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pss-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pss-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pss-times-negative (a b) (b a)))
                 :in-theory (disable lw-pss-times-negative)))))

(local (defthm lw-pss-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pss-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pss-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pss-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pss-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pss-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pss-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pss-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pss-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pss-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pss-left-commutes)))))

(defun lw-power-block-search (entries start count cap)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil
  (if (lw-complex-diskp (lw-weighted-power-sum entries (+ start count -1)) cap)
      (lw-power-block-search entries start (- count 1) cap)
    (+ start count -1))))

(defthm lw-power-block-search-empty
 (equal (equal (lw-power-block-search entries start count cap) nil)
        (not (not (lw-power-block-boundedp entries start count cap))))
 :hints (("Goal" :induct (lw-power-block-search entries start count cap)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-power-block-search lw-power-block-boundedp lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-block-search-sound
 (implies (and (natp start) (natp count)
               (lw-power-block-search entries start count cap))
  (let ((index (lw-power-block-search entries start count cap)))
   (and (natp index) (<= start index) (< index (+ start count))
        (not (lw-complex-diskp (lw-weighted-power-sum entries index) cap)))))
 :hints (("Goal" :induct (lw-power-block-search entries start count cap)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-power-block-search lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defun lw-power-large-term-cap (entries start)
 (* 1/8 (lw-complex-l1 (lw-weighted-power-sum entries 0))
    (/ (lw-power-domination-factor (len entries) (+ start (len entries))))))

(defun lw-power-sum-large-index (entries start)
 (lw-power-block-search entries (+ 1 start) (len entries)
                        (lw-power-large-term-cap entries start)))

(local (defthm lw-pss-l1-positive
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
          (< 0 (lw-complex-l1 point)))
 :hints (("Goal" :cases ((<= 0 (car point)) (<= 0 (cdr point)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-l1 abs lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pss-small-disk-excluded
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
          (not (lw-complex-diskp point (* 1/8 (lw-complex-l1 point)))))
 :hints (("Goal" :use (lw-pss-l1-positive
                       (:instance lw-complex-disk-coordinates
                        (radius (* 1/8 (lw-complex-l1 point)))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-l1 lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-pss-positive-inverse
 (implies (and (rationalp factor) (< 0 factor)) (< 0 (/ factor)))
 :hints (("Goal" :use ((:instance inverse-of-* (x factor)))
          :in-theory (disable inverse-of-*) :nonlinearp t))
 :rule-classes nil))

(local (defthm lw-pss-cap-algebra
 (implies (and (rationalp mass) (< 0 mass)
               (rationalp factor) (<= 1 factor))
  (and (rationalp (* 1/8 mass (/ factor)))
       (< 0 (* 1/8 mass (/ factor)))
       (equal (* factor 1/8 mass (/ factor)) (* 1/8 mass))))
 :hints (("Goal"
  :use ((:instance lw-pss-positive-inverse)
        (:instance lw-pss-inverse-factor (divisor factor) (coefficient (* 1/8 mass))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defthm lw-power-large-term-cap-valid
 (implies (and (lw-power-systemp entries)
               (not (equal (lw-weighted-power-sum entries 0) (cons 0 0))))
  (and (rationalp (lw-power-large-term-cap entries start))
       (< 0 (lw-power-large-term-cap entries start))
       (equal
        (* (lw-power-domination-factor (len entries) (+ start (len entries)))
           (lw-power-large-term-cap entries start))
        (* 1/8 (lw-complex-l1 (lw-weighted-power-sum entries 0))))))
 :hints (("Goal"
  :use ((:instance lw-pss-cap-algebra
         (mass (lw-complex-l1 (lw-weighted-power-sum entries 0)))
         (factor (lw-power-domination-factor (len entries) (+ start (len entries))))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-power-large-term-cap lw-weighted-power-sum-rational lw-complex-l1-bound lw-pss-l1-positive lw-power-domination-factor-valid lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-sum-late-block-nontrivial
 (implies (and (consp entries) (lw-power-outer-systemp entries) (natp start)
               (not (equal (lw-weighted-power-sum entries 0) (cons 0 0))))
  (not (lw-power-block-boundedp entries (+ 1 start) (len entries)
                               (lw-power-large-term-cap entries start))))
 :hints (("Goal"
  :use (lw-power-outer-system-typed
        lw-power-large-term-cap-valid
        (:instance lw-power-sum-late-block-domination
          (cap (lw-power-large-term-cap entries start)))
        (:instance lw-pss-small-disk-excluded
          (point (lw-weighted-power-sum entries 0))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-weighted-power-sum-rational lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pss-length-natural
 (natp (len entries)) :rule-classes (:rewrite :type-prescription)))

(defthm lw-power-sum-large-index-certificate
 (implies (and (consp entries) (lw-power-outer-systemp entries) (natp start)
               (not (equal (lw-weighted-power-sum entries 0) (cons 0 0))))
  (let ((index (lw-power-sum-large-index entries start)))
   (and (natp index) (< start index) (<= index (+ start (len entries)))
        (not (lw-complex-diskp (lw-weighted-power-sum entries index)
                               (lw-power-large-term-cap entries start))))))
 :hints (("Goal"
  :use (lw-power-sum-late-block-nontrivial
        (:instance lw-power-block-search-empty
          (start (+ 1 start)) (count (len entries))
          (cap (lw-power-large-term-cap entries start)))
        (:instance lw-power-block-search-sound
          (start (+ 1 start)) (count (len entries))
          (cap (lw-power-large-term-cap entries start))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-power-sum-large-index lw-pss-length-natural lw-pss-left-commutes lw-pss-left-distributes lw-pss-fold-constants lw-pss-times-negative lw-pss-negative-times lw-pss-zero-times lw-pss-minus-one lw-pss-double-negative lw-pss-add-cancel lw-pss-double lw-pss-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

