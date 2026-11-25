(in-package "ACL2")

(include-book "power-sum-blocks")

; A deliberately loose polynomial bound, uniform in node separation.
; For M unit-disk nodes, M initial bounds control every finite prefix.

(local (defthm lw-psd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psd-times-negative (a b) (b a)))
                 :in-theory (disable lw-psd-times-negative)))))

(local (defthm lw-psd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psd-left-commutes)))))

(defun lw-power-domination-factor (count index)
 (lw-rational-power (* 3 (+ 1 (nfix index))) (nfix (- count 1))))

(local (defthm lw-psd-length-natural
 (natp (len entries)) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-psd-difference-length
 (equal (len (lw-power-difference-system anchor entries)) (len entries))
 :hints (("Goal" :induct (lw-power-difference-system anchor entries)
          :in-theory (union-theories
 '(lw-power-difference-system len lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-power-domination-factor-valid
 (and (rationalp (lw-power-domination-factor count index))
      (<= 1 (lw-power-domination-factor count index)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-power-domination-factor nfix lw-rational-power-rational lw-rational-power-at-least-one lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes (:rewrite :type-prescription))

(local (defthm lw-psd-factor-single
 (equal (lw-power-domination-factor 1 index) 1)
 :hints (("Goal" :in-theory (union-theories
 '(lw-power-domination-factor lw-rational-power nfix lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psd-power-step
 (implies (posp exponent)
  (equal (lw-rational-power base exponent)
         (* base (lw-rational-power base (- exponent 1)))))
 :hints (("Goal" :expand ((lw-rational-power base exponent))))))

(defthm lw-power-domination-factor-step
 (implies (and (natp count) (<= 2 count) (natp index))
  (equal (lw-power-domination-factor count index)
         (* 3 (+ 1 index) (lw-power-domination-factor (- count 1) index))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-power-domination-factor nfix lw-psd-power-step lw-rational-power-rational lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-psd-zero-block
 (lw-power-block-boundedp nil start count 0)
 :hints (("Goal" :induct (lw-power-block-boundedp nil start count 0)
          :in-theory (union-theories
 '(lw-power-block-boundedp lw-weighted-power-sum lw-complex-diskp lw-complexp lw-diskp lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psd-empty-difference
 (equal (lw-power-difference-system anchor nil) nil)
 :hints (("Goal" :in-theory (enable lw-power-difference-system)))))

(local (defthm lw-psd-single-prefix
 (implies (and (consp entries) (equal (cdr entries) nil)
               (lw-power-unit-systemp entries) (natp index)
               (rationalp cap) (<= 0 cap)
               (lw-power-block-boundedp entries 0 1 cap))
          (lw-power-block-boundedp entries 0 (+ 1 index) cap))
 :hints (("Goal"
          :use ((:instance lw-power-block-at (start 0) (count 1) (index 0))
                (:instance lw-power-first-order-prefix-bound (initial cap) (residual 0)))
          :in-theory (union-theories
 '(lw-psd-empty-difference lw-psd-zero-block lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defun lw-psd-induct (entries cap)
 (declare (xargs :measure (len entries)
   :hints (("Goal" :in-theory (enable lw-psd-difference-length)))))
 (if (or (endp entries) (endp (cdr entries))) cap
  (lw-psd-induct (lw-power-difference-system (caar entries) (cdr entries)) (* 2 cap)))))

(local (defthm lw-psd-budget
 (implies (and (rationalp cap) (<= 0 cap) (natp index)
               (rationalp factor) (<= 1 factor))
          (<= (+ cap (* index 2 cap factor)) (* 3 (+ 1 index) cap factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))


(local (defthm lw-psd-length-step
 (implies (consp entries) (equal (len entries) (+ 1 (len (cdr entries)))))
 :hints (("Goal" :expand ((len entries))))))

(local (defthm lw-psd-head
 (implies (and (consp entries) (lw-power-unit-systemp entries))
  (and (lw-complexp (caar entries))
       (lw-power-unit-systemp (cdr entries))
       (implies (atom (cdr entries)) (equal (cdr entries) nil))))
 :hints (("Goal" :expand ((lw-power-unit-systemp entries)
                         (lw-power-unit-systemp (cdr entries)) (lw-power-unit-systemp nil))
          :in-theory (union-theories
 '(lw-complex-disk-data lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psd-children
 (implies (and (consp entries) (consp (cdr entries))
               (lw-power-unit-systemp entries)
               (lw-power-block-boundedp entries 0 (len entries) cap))
  (and
   (consp (lw-power-difference-system (caar entries) (cdr entries)))
   (lw-power-unit-systemp (lw-power-difference-system (caar entries) (cdr entries)))
   (lw-power-block-boundedp (lw-power-difference-system (caar entries) (cdr entries))
                           0 (len (cdr entries)) (* 2 cap))))
 :hints (("Goal"
  :use ((:instance lw-power-difference-system-unit
          (anchor (caar entries)) (entries (cdr entries)))
        (:instance lw-power-difference-block
          (start 0) (count (len (cdr entries)))))
  :expand ((lw-power-difference-system (caar entries) (cdr entries)))
  :in-theory (union-theories
 '(lw-psd-head lw-psd-length-natural lw-psd-length-step lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psd-base
 (implies (and (consp entries) (endp (cdr entries))
               (lw-power-unit-systemp entries) (natp index)
               (rationalp cap) (<= 0 cap)
               (lw-power-block-boundedp entries 0 (len entries) cap))
  (lw-power-block-boundedp entries 0 (+ 1 index)
   (* cap (lw-power-domination-factor (len entries) index))))
 :hints (("Goal" :use (lw-psd-single-prefix)
          :in-theory (union-theories
 '(lw-psd-head lw-psd-length-step lw-psd-factor-single len lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-psd-step
 (implies (and (consp entries) (consp (cdr entries))
               (lw-power-unit-systemp entries) (natp index)
               (rationalp cap) (<= 0 cap)
               (lw-power-block-boundedp entries 0 (len entries) cap)
               (lw-power-block-boundedp
                 (lw-power-difference-system (caar entries) (cdr entries))
                 0 (+ 1 index)
                 (* 2 cap (lw-power-domination-factor (len (cdr entries)) index))))
  (lw-power-block-boundedp entries 0 (+ 1 index)
   (* cap (lw-power-domination-factor (len entries) index))))
 :hints (("Goal"
  :use ((:instance lw-power-block-at
          (start 0) (count (len entries)) (index 0))
        (:instance lw-power-block-shrink
          (entries (lw-power-difference-system (caar entries) (cdr entries)))
          (start 0) (count (+ 1 index)) (smaller index)
          (cap (* 2 cap (lw-power-domination-factor (len (cdr entries)) index))))
        (:instance lw-power-first-order-prefix-bound
          (initial cap)
          (residual (* 2 cap (lw-power-domination-factor (len (cdr entries)) index))))
        (:instance lw-power-block-enlarge
          (start 0) (count (+ 1 index))
          (cap (+ cap (* index 2 cap (lw-power-domination-factor (len (cdr entries)) index))))
          (larger (* cap (lw-power-domination-factor (len entries) index))))
        (:instance lw-psd-budget
          (factor (lw-power-domination-factor (len (cdr entries)) index))))
  :in-theory (union-theories
 '(lw-psd-length-natural lw-psd-length-step lw-power-domination-factor-valid lw-power-domination-factor-step lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-power-sum-prefix-domination
 (implies (and (consp entries) (lw-power-unit-systemp entries) (natp index)
               (rationalp cap) (<= 0 cap)
               (lw-power-block-boundedp entries 0 (len entries) cap))
  (lw-power-block-boundedp entries 0 (+ 1 index)
   (* cap (lw-power-domination-factor (len entries) index))))
 :hints (("Goal" :induct (lw-psd-induct entries cap)
          :in-theory (union-theories
 '((:induction lw-psd-induct) lw-psd-difference-length lw-psd-children lw-psd-base lw-psd-step lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-sum-domination
 (implies (and (consp entries) (lw-power-unit-systemp entries) (natp index)
               (rationalp cap) (<= 0 cap)
               (lw-power-block-boundedp entries 0 (len entries) cap))
  (lw-complex-diskp (lw-weighted-power-sum entries index)
   (* cap (lw-power-domination-factor (len entries) index))))
 :hints (("Goal" :use (lw-power-sum-prefix-domination
                       (:instance lw-power-block-at (start 0) (count (+ 1 index))
                        (cap (* cap (lw-power-domination-factor (len entries) index)))))
          :in-theory (union-theories
 '( lw-psd-left-commutes lw-psd-left-distributes lw-psd-fold-constants lw-psd-times-negative lw-psd-negative-times lw-psd-zero-times lw-psd-minus-one lw-psd-double-negative lw-psd-add-cancel lw-psd-double lw-psd-add-double
 fold-consts-in-+ natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

