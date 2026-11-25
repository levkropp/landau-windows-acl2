(in-package "ACL2")

(include-book "power-sum-domination")

; Reverse a finite power sum at a specified order. Nodes outside the
; open unit disk become unit-disk nodes, with exact rational weights.

(local (defthm lw-psr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psr-times-negative (a b) (b a)))
                 :in-theory (disable lw-psr-times-negative)))))

(local (defthm lw-psr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psr-left-commutes)))))

(defun lw-power-outer-systemp (entries)
 (if (atom entries) (equal entries nil)
  (and (consp (car entries)) (lw-complexp (caar entries))
       (<= 1 (lw-complex-norm-square (caar entries)))
       (lw-complexp (cdar entries))
       (lw-power-outer-systemp (cdr entries)))))

(defun lw-power-reverse-system (entries order)
 (if (endp entries) nil
  (cons (cons (lw-complex-reciprocal (caar entries))
              (lw-complex-mul (cdar entries) (lw-complex-power (caar entries) order)))
        (lw-power-reverse-system (cdr entries) order))))

(defthm lw-power-outer-system-typed
 (implies (lw-power-outer-systemp entries) (lw-power-systemp entries))
 :hints (("Goal" :induct (lw-power-outer-systemp entries)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-power-outer-systemp lw-power-systemp lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-reverse-system-length
 (equal (len (lw-power-reverse-system entries order)) (len entries))
 :hints (("Goal" :induct (lw-power-reverse-system entries order)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-power-reverse-system len lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-reverse-system-unit
 (implies (lw-power-outer-systemp entries)
  (lw-power-unit-systemp (lw-power-reverse-system entries order)))
 :hints (("Goal" :induct (lw-power-reverse-system entries order)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-power-reverse-system lw-power-unit-systemp lw-power-outer-systemp lw-complex-power-rational lw-complex-ring-rational lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-reciprocal-disk-bound
                    (point (caar entries)) (lower 1)))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-power-rational lw-complex-ring-rational lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psr-one-power
 (equal (lw-complex-power (cons 1 0) index) (cons 1 0))
 :hints (("Goal" :induct (lw-complex-power (cons 1 0) index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-power lw-complex-mul lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psr-inverse-power
 (implies (and (lw-complexp point) (not (equal point (cons 0 0))) (natp index))
  (equal (lw-complex-mul (lw-complex-power point index)
                         (lw-complex-power (lw-complex-reciprocal point) index))
         (cons 1 0)))
 :hints (("Goal"
          :use ((:instance lw-complex-power-product
                  (left point) (right (lw-complex-reciprocal point))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-reciprocal-rational lw-complex-reciprocal-inverse lw-psr-one-power lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psr-cancel-power
 (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
               (natp order) (natp index) (<= index order))
  (equal (lw-complex-mul (lw-complex-power point order)
                         (lw-complex-power (lw-complex-reciprocal point) index))
         (lw-complex-power point (- order index))))
 :hints (("Goal"
          :use ((:instance lw-complex-power-add (left (- order index)) (right index)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-power-rational lw-complex-reciprocal-rational lw-complex-mul-associative lw-complex-mul-one lw-psr-inverse-power lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psr-outer-nonzero
 (implies (and (lw-complexp point) (<= 1 (lw-complex-norm-square point)))
          (not (equal point (cons 0 0))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-norm-square lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-power-reverse-sum
 (implies (and (lw-power-outer-systemp entries) (natp order) (natp index) (<= index order))
  (equal (lw-weighted-power-sum (lw-power-reverse-system entries order) index)
         (lw-weighted-power-sum entries (- order index))))
 :hints (("Goal" :induct (lw-power-reverse-system entries order)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-power-reverse-system lw-power-outer-systemp lw-weighted-power-sum lw-complex-mul-associative lw-complex-power-rational lw-complex-reciprocal-rational lw-psr-outer-nonzero lw-psr-cancel-power lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-psr-empty-block
 (implies (zp count) (lw-power-block-boundedp entries start count cap))
 :hints (("Goal" :in-theory (enable lw-power-block-boundedp)))))

(local (defun lw-psr-countdown (count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) nil (lw-psr-countdown (- count 1)))))

(defthm lw-power-reverse-prefix
 (implies (and (lw-power-outer-systemp entries) (natp start) (natp count)
               (natp smaller) (<= smaller count)
               (lw-power-block-boundedp entries (+ 1 start) count cap))
  (lw-power-block-boundedp (lw-power-reverse-system entries (+ start count))
                          0 smaller cap))
 :hints (("Goal" :induct (lw-psr-countdown smaller)
          :in-theory (union-theories
 '(fold-consts-in-+ (:induction lw-psr-countdown) lw-psr-empty-block lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
         (and stable-under-simplificationp
          '(:expand ((:free (system offset radius)
                       (lw-power-block-boundedp system offset smaller radius)))
            :use ((:instance lw-power-block-at
                    (start (+ 1 start)) (index (+ start count 1 (- smaller)))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-power-reverse-sum lw-psr-empty-block lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-power-reverse-block
 (implies (and (lw-power-outer-systemp entries) (natp start) (natp count)
               (lw-power-block-boundedp entries (+ 1 start) count cap))
  (lw-power-block-boundedp (lw-power-reverse-system entries (+ start count))
                          0 count cap))
 :hints (("Goal" :use ((:instance lw-power-reverse-prefix (smaller count)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-psr-length-natural
 (natp (len entries)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-psr-reverse-consp
 (implies (consp entries) (consp (lw-power-reverse-system entries order)))
 :hints (("Goal" :expand ((lw-power-reverse-system entries order))))))

(defthm lw-power-sum-late-block-domination
 (implies (and (consp entries) (lw-power-outer-systemp entries) (natp start)
               (rationalp cap) (<= 0 cap)
               (lw-power-block-boundedp entries (+ 1 start) (len entries) cap))
  (lw-complex-diskp (lw-weighted-power-sum entries 0)
   (* cap (lw-power-domination-factor (len entries) (+ start (len entries))))))
 :hints (("Goal"
          :use ((:instance lw-power-reverse-block (count (len entries)))
                (:instance lw-power-sum-domination
                  (entries (lw-power-reverse-system entries (+ start (len entries))))
                  (index (+ start (len entries))))
                (:instance lw-power-reverse-sum
                  (order (+ start (len entries))) (index (+ start (len entries)))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-psr-length-natural lw-psr-reverse-consp lw-power-reverse-system-length lw-power-reverse-system-unit lw-psr-left-commutes lw-psr-left-distributes lw-psr-fold-constants lw-psr-times-negative lw-psr-negative-times lw-psr-zero-times lw-psr-minus-one lw-psr-double-negative lw-psr-add-cancel lw-psr-double lw-psr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

