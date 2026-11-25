(in-package "ACL2")

(include-book "pole-cluster-search")

; Multiplication by s(s-1) couples three neighboring coefficients.
; The existing normalized zeta residue has a minus sign, so the resulting
; positive-multiplicity logarithmic-derivative coefficient is negated.

(local (defthm lw-zpq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zpq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zpq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zpq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zpq-times-negative (a b) (b a)))
                 :in-theory (disable lw-zpq-times-negative)))))

(local (defthm lw-zpq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zpq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zpq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zpq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zpq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zpq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zpq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zpq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zpq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zpq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zpq-left-commutes)))))

(defun lw-pole-quadratic-coefficient (center current previous earlier)
 (lw-complex-add
  (lw-complex-mul (lw-zeta-residue-denominator center) current)
  (lw-complex-add
   (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) previous)
   earlier)))

(local (defthm lw-zpq-reorder
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
  (equal (lw-complex-mul a (lw-complex-mul b (lw-complex-mul c d)))
         (lw-complex-mul b (lw-complex-mul (lw-complex-mul a c) d))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-mul lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-pole-coefficient-offset-step
 (implies (and (lw-complexp residue) (lw-complexp offset)
               (not (equal offset (cons 0 0))) (natp index))
  (equal (lw-complex-mul offset (lw-pole-coefficient residue offset (+ 1 index)))
         (lw-pole-coefficient residue offset index)))
 :hints (("Goal"
  :use ((:instance lw-complex-power-step
          (point (lw-complex-reciprocal offset)) (index (+ 1 index))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-coefficient nfix lw-zpq-reorder lw-complex-reciprocal-rational lw-complex-power-rational lw-complex-reciprocal-inverse lw-complex-mul-one lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-pole-coefficient-residue-product
 (implies (and (lw-complexp factor) (lw-complexp residue)
               (lw-complexp offset) (natp index))
  (equal (lw-complex-mul factor (lw-pole-coefficient residue offset index))
         (lw-pole-coefficient (lw-complex-mul factor residue) offset index)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-coefficient lw-complex-mul-associative lw-complex-power-rational lw-complex-reciprocal-rational lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zpq-scale-mul
 (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-mul (lw-complex-scale factor a) b)
         (lw-complex-scale factor (lw-complex-mul a b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-mul lw-complex-scale lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-pole-coefficient-scale-residue
 (implies (and (rationalp factor) (lw-complexp residue)
               (lw-complexp offset) (natp index))
  (equal (lw-pole-coefficient (lw-complex-scale factor residue) offset index)
         (lw-complex-scale factor (lw-pole-coefficient residue offset index))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-coefficient lw-zpq-scale-mul lw-complex-power-rational lw-complex-reciprocal-rational lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zpq-q-shift
 (implies (and (lw-complexp center) (lw-complexp zero) (lw-complexp point))
  (equal
   (lw-pole-quadratic-coefficient center point
    (lw-complex-mul (lw-complex-sub center zero) point)
    (lw-complex-mul (lw-complex-sub center zero)
                    (lw-complex-mul (lw-complex-sub center zero) point)))
   (lw-complex-mul (lw-zeta-residue-denominator zero) point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-quadratic-coefficient lw-zeta-residue-denominator lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-zpq-q-shift-values
 (implies (and (lw-complexp center) (lw-complexp zero) (lw-complexp current)
               (equal (lw-complex-mul (lw-complex-sub center zero) current) previous)
               (equal (lw-complex-mul (lw-complex-sub center zero) previous) earlier))
  (equal (lw-pole-quadratic-coefficient center current previous earlier)
         (lw-complex-mul (lw-zeta-residue-denominator zero) current)))
 :hints (("Goal" :use ((:instance lw-zpq-q-shift (point current)))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-pole-quadratic-shift
 (implies (and (lw-complexp center) (lw-complexp zero) (lw-complexp residue)
               (not (equal (lw-complex-sub center zero) (cons 0 0))) (natp index))
  (equal
   (lw-pole-quadratic-coefficient center
    (lw-pole-coefficient residue (lw-complex-sub center zero) (+ 2 index))
    (lw-pole-coefficient residue (lw-complex-sub center zero) (+ 1 index))
    (lw-pole-coefficient residue (lw-complex-sub center zero) index))
   (lw-pole-coefficient (lw-complex-mul (lw-zeta-residue-denominator zero) residue)
                        (lw-complex-sub center zero) (+ 2 index))))
 :hints (("Goal"
  :use ((:instance lw-pole-coefficient-offset-step
          (offset (lw-complex-sub center zero)) (index (+ 1 index)))
        (:instance lw-pole-coefficient-offset-step
          (offset (lw-complex-sub center zero)))
        (:instance lw-zpq-q-shift-values
          (current (lw-pole-coefficient residue (lw-complex-sub center zero) (+ 2 index)))
          (previous (lw-pole-coefficient residue (lw-complex-sub center zero) (+ 1 index)))
          (earlier (lw-pole-coefficient residue (lw-complex-sub center zero) index))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-ring-rational lw-pole-coefficient-rational lw-zeta-residue-denominator-rational lw-pole-coefficient-residue-product lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zpq-negative-multiplicity
 (implies (natp multiplicity)
  (equal (cons (- multiplicity) 0) (lw-complex-scale -1 (cons multiplicity 0))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-zeta-pole-quadratic-coefficient
 (implies (and (lw-complexp center) (lw-complexp zero)
               (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0)))
               (not (equal (lw-complex-sub center zero) (cons 0 0)))
               (posp multiplicity) (natp index))
  (equal
   (lw-pole-quadratic-coefficient center
    (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                         (lw-complex-sub center zero) (+ 2 index))
    (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                         (lw-complex-sub center zero) (+ 1 index))
    (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                         (lw-complex-sub center zero) index))
   (lw-complex-scale -1
    (lw-pole-coefficient (cons multiplicity 0) (lw-complex-sub center zero) (+ 2 index)))))
 :hints (("Goal"
  :use ((:instance lw-pole-quadratic-shift (residue (lw-zeta-pole-residue zero multiplicity))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-zeta-pole-residue-rational lw-zeta-pole-residue-cancel lw-zpq-negative-multiplicity lw-pole-coefficient-scale-residue lw-complex-ring-rational lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-pole-quadratic-coefficient-add
 (implies (and (lw-complexp center) (lw-complexp a) (lw-complexp b) (lw-complexp c)
               (lw-complexp d) (lw-complexp e) (lw-complexp f))
  (equal
   (lw-pole-quadratic-coefficient center (lw-complex-add a d) (lw-complex-add b e) (lw-complex-add c f))
   (lw-complex-add (lw-pole-quadratic-coefficient center a b c)
                   (lw-pole-quadratic-coefficient center d e f))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-quadratic-coefficient lw-zeta-residue-denominator lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zpq-q-zero
 (equal (lw-pole-quadratic-coefficient center (cons 0 0) (cons 0 0) (cons 0 0)) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-quadratic-coefficient lw-complex-mul lw-complex-add lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-zeta-pole-cluster-quadratic-coefficients
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (lw-factor-model-away-check center entries) (natp index))
  (equal
   (lw-pole-quadratic-coefficient center
    (lw-zeta-pole-coefficient-sum center entries (+ 2 index))
    (lw-zeta-pole-coefficient-sum center entries (+ 1 index))
    (lw-zeta-pole-coefficient-sum center entries index))
   (lw-complex-scale -1 (lw-pole-log-coefficient-sum center entries (+ 2 index)))))
 :hints (("Goal" :induct (lw-zeta-pole-coefficient-sum center entries index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-zeta-pole-coefficient-sum lw-pole-log-coefficient-sum lw-factor-model-away-check lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-zeta-pole-coefficient-sum-rational lw-pole-log-coefficient-sum-rational lw-pole-coefficient-rational lw-zeta-pole-residue-rational lw-pole-quadratic-coefficient-add lw-zeta-pole-quadratic-coefficient lw-zpq-q-zero lw-complex-scale-zero lw-complex-scale-add lw-zpq-left-commutes lw-zpq-left-distributes lw-zpq-fold-constants lw-zpq-times-negative lw-zpq-negative-times lw-zpq-zero-times lw-zpq-minus-one lw-zpq-double-negative lw-zpq-add-cancel lw-zpq-double lw-zpq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

