(in-package "ACL2")

(include-book "cauchy-resolvents")

; Weighted finite power sums. Repeated nodes and zero weights are allowed.
; First differences eliminate one node without division by node separation.

(local (defthm lw-wps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-wps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-wps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-wps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-wps-times-negative (a b) (b a)))
                 :in-theory (disable lw-wps-times-negative)))))

(local (defthm lw-wps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-wps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-wps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-wps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-wps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-wps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-wps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-wps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-wps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-wps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-wps-left-commutes)))))

(defun lw-power-systemp (entries)
  (if (atom entries) (equal entries nil)
    (and (consp (car entries))
         (lw-complexp (caar entries)) (lw-complexp (cdar entries))
         (lw-power-systemp (cdr entries)))))

(defun lw-power-unit-systemp (entries)
  (if (atom entries) (equal entries nil)
    (and (consp (car entries))
         (lw-complex-diskp (caar entries) 1) (lw-complexp (cdar entries))
         (lw-power-unit-systemp (cdr entries)))))

(defun lw-weighted-power-sum (entries index)
  (if (endp entries) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul (cdar entries) (lw-complex-power (caar entries) index))
     (lw-weighted-power-sum (cdr entries) index))))

(defun lw-power-difference-system (anchor entries)
  (if (endp entries) nil
    (cons (cons (caar entries)
                (lw-complex-mul (lw-complex-sub (caar entries) anchor)
                                (cdar entries)))
          (lw-power-difference-system anchor (cdr entries)))))

(defthm lw-power-unit-system-typed
  (implies (lw-power-unit-systemp entries) (lw-power-systemp entries))
  :hints (("Goal" :induct (lw-power-unit-systemp entries)
           :in-theory (union-theories
 '(lw-power-unit-systemp lw-power-systemp lw-complex-disk-data lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-weighted-power-sum-rational
  (implies (lw-power-systemp entries)
           (lw-complexp (lw-weighted-power-sum entries index)))
  :hints (("Goal" :induct (lw-weighted-power-sum entries index)
           :in-theory (union-theories
 '(lw-weighted-power-sum lw-power-systemp lw-complexp lw-complex-ring-rational lw-complex-power-rational lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-difference-system-valid
  (implies (and (lw-complexp anchor) (lw-power-systemp entries))
           (and (lw-power-systemp (lw-power-difference-system anchor entries))
                (equal (len (lw-power-difference-system anchor entries)) (len entries))))
  :hints (("Goal" :induct (lw-power-difference-system anchor entries)
           :in-theory (union-theories
 '(lw-power-difference-system lw-power-systemp len lw-complex-ring-rational lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-power-difference-system-unit
  (implies (and (lw-complexp anchor) (lw-power-unit-systemp entries))
           (lw-power-unit-systemp (lw-power-difference-system anchor entries)))
  :hints (("Goal" :induct (lw-power-difference-system anchor entries)
           :in-theory (union-theories
 '(lw-power-difference-system lw-power-unit-systemp lw-complex-disk-data lw-complex-ring-rational lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-wps-difference-step
 (implies (and (lw-complexp w) (lw-complexp z) (lw-complexp c)
               (lw-complexp p) (lw-complexp a) (lw-complexp b))
  (equal
   (lw-complex-add (lw-complex-mul (lw-complex-mul (lw-complex-sub z w) c) p)
                   (lw-complex-sub b (lw-complex-mul w a)))
   (lw-complex-sub (lw-complex-add (lw-complex-mul c (lw-complex-mul z p)) b)
                   (lw-complex-mul w (lw-complex-add (lw-complex-mul c p) a)))))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(local (defthm lw-wps-sub-zero
 (equal (lw-complex-sub (cons 0 0) (cons 0 0)) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(defthm lw-power-difference-sum
  (implies (and (lw-complexp anchor) (lw-power-systemp entries) (natp index))
   (equal (lw-weighted-power-sum (lw-power-difference-system anchor entries) index)
          (lw-complex-sub (lw-weighted-power-sum entries (+ 1 index))
                          (lw-complex-mul anchor (lw-weighted-power-sum entries index)))))
  :hints (("Goal" :induct (lw-power-difference-system anchor entries)
           :in-theory (union-theories
 '(lw-power-systemp lw-weighted-power-sum lw-power-difference-system lw-complexp lw-complex-power-rational lw-weighted-power-sum-rational lw-complex-power-step lw-complex-mul-zero lw-wps-sub-zero lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) )
          (and stable-under-simplificationp
           '(:use ((:instance lw-wps-difference-step
                    (w anchor) (z (caar entries)) (c (cdar entries))
                    (p (lw-complex-power (caar entries) index))
                    (a (lw-weighted-power-sum (cdr entries) index))
                    (b (lw-weighted-power-sum (cdr entries) (+ 1 index)))))
             :in-theory (union-theories
 '(lw-power-systemp lw-weighted-power-sum lw-power-difference-system lw-complexp lw-complex-power-rational lw-weighted-power-sum-rational lw-complex-power-step lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-wps-elimination-algebra
 (implies (and (lw-complexp z) (lw-complexp c) (lw-complexp p)
               (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-add
          (lw-complex-mul z (lw-complex-add (lw-complex-mul c p) a))
          (lw-complex-sub b (lw-complex-mul z a)))
         (lw-complex-add (lw-complex-mul c (lw-complex-mul z p)) b)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
 :rule-classes nil))

(defthm lw-power-sum-first-difference
 (implies (and (consp entries) (lw-power-systemp entries) (natp index))
  (equal (lw-weighted-power-sum entries (+ 1 index))
         (lw-complex-add
          (lw-complex-mul (caar entries) (lw-weighted-power-sum entries index))
          (lw-weighted-power-sum
           (lw-power-difference-system (caar entries) (cdr entries)) index))))
 :hints (("Goal"
          :use ((:instance lw-power-difference-sum
                 (anchor (caar entries)) (entries (cdr entries)))
                (:instance lw-wps-elimination-algebra
                 (z (caar entries)) (c (cdar entries))
                 (p (lw-complex-power (caar entries) index))
                 (a (lw-weighted-power-sum (cdr entries) index))
                 (b (lw-weighted-power-sum (cdr entries) (+ 1 index)))))
          :expand ((lw-weighted-power-sum entries (+ 1 index))
                   (lw-weighted-power-sum entries index))
          :in-theory (union-theories
 '(lw-power-systemp lw-complex-power-step lw-complex-power-rational lw-weighted-power-sum-rational lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
(local (defthm lw-wps-add-cancel-complex
 (implies (and (lw-complexp a) (lw-complexp b))
          (equal (lw-complex-sub (lw-complex-add a b) a) b))
 :hints (("Goal" :in-theory (union-theories
 '(lw-complexp lw-complex-add lw-complex-sub lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-power-sum-first-residual
 (implies (and (consp entries) (lw-power-systemp entries) (natp index))
  (equal (lw-weighted-power-sum
           (lw-power-difference-system (caar entries) (cdr entries)) index)
         (lw-complex-sub
          (lw-weighted-power-sum entries (+ 1 index))
          (lw-complex-mul (caar entries) (lw-weighted-power-sum entries index)))))
 :hints (("Goal" :use (lw-power-sum-first-difference)
          :in-theory (union-theories
 '(lw-power-systemp lw-power-difference-system-valid lw-weighted-power-sum-rational lw-complex-ring-rational lw-wps-add-cancel-complex lw-wps-left-commutes lw-wps-left-distributes lw-wps-fold-constants lw-wps-times-negative lw-wps-negative-times lw-wps-zero-times lw-wps-minus-one lw-wps-double-negative lw-wps-add-cancel lw-wps-double lw-wps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))


