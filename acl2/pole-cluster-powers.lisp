(in-package "ACL2")

(include-book "power-sum-search")
(include-book "polynomial-factor-model")

; A finite positive-multiplicity pole cluster to the left of an anchor.
; The check uses actual pole distances. It does not assume separation,
; a distinguished dominant pole, or a nonzero aggregate coefficient.

(local (defthm lw-pcp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcp-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcp-times-negative)))))

(local (defthm lw-pcp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pcp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pcp-left-commutes)))))

(defun lw-pole-cluster-check (center entries radius)
 (if (endp entries) t
  (let ((offset (lw-complex-sub center (caar entries))))
   (and (< 0 (car offset)) (lw-complex-diskp offset radius)
        (lw-pole-cluster-check center (cdr entries) radius)))))

(defun lw-pole-cluster-power-system (center entries radius)
 (if (endp entries) nil
  (let ((offset (lw-complex-sub center (caar entries))))
   (cons (cons (lw-pole-resolvent-ratio offset radius)
               (lw-pole-resolvent-factor (cons (cdar entries) 0) offset))
         (lw-pole-cluster-power-system center (cdr entries) radius)))))

(defun lw-pole-log-coefficient-sum (center entries index)
 (if (endp entries) (cons 0 0)
  (lw-complex-add
   (lw-pole-coefficient (cons (cdar entries) 0)
                        (lw-complex-sub center (caar entries)) index)
   (lw-pole-log-coefficient-sum center (cdr entries) index))))

(defthm lw-pole-cluster-power-system-length
 (equal (len (lw-pole-cluster-power-system center entries radius)) (len entries))
 :hints (("Goal" :induct (lw-pole-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-power-system len lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pcp-ratio-rational
 (implies (and (lw-complexp offset) (rationalp radius))
          (lw-complexp (lw-pole-resolvent-ratio offset radius)))
 :hints (("Goal" :use ((:instance lw-pole-resolvent-data (residue (cons 0 0))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-pole-cluster-power-system-typed
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries) (rationalp radius))
  (lw-power-systemp (lw-pole-cluster-power-system center entries radius)))
 :hints (("Goal" :induct (lw-pole-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-cluster-power-system lw-power-systemp lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-pcp-ratio-rational lw-pole-resolvent-data lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-pole-log-coefficient-sum-rational
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries) (natp index))
  (lw-complexp (lw-pole-log-coefficient-sum center entries index)))
 :hints (("Goal" :induct (lw-pole-log-coefficient-sum center entries index)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-log-coefficient-sum lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-pole-coefficient-rational lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pcp-ratio-norm
 (implies (and (lw-complexp offset) (not (equal offset (cons 0 0)))
               (rationalp radius))
  (equal (lw-complex-norm-square (lw-pole-resolvent-ratio offset radius))
         (* radius radius (/ (lw-complex-norm-square offset)))))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-product
         (left (cons radius 0)) (right (lw-complex-reciprocal offset))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-resolvent-ratio lw-complex-norm-square-reciprocal lw-complex-reciprocal-rational lw-complexp lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :expand ((lw-complex-norm-square (cons radius 0)))))))

(local (defthm lw-pcp-offset-nonzero
 (implies (< 0 (car offset)) (not (equal offset (cons 0 0))))))

(local (defthm lw-pcp-inverse-rational
 (implies (rationalp x) (rationalp (/ x)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-pcp-inverse-positive
 (implies (and (rationalp x) (< 0 x)) (< 0 (/ x)))
 :hints (("Goal" :use ((:instance inverse-of-*))
          :in-theory (disable inverse-of-*) :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pcp-ratio-outer
 (implies (and (lw-complexp offset) (< 0 (car offset))
               (lw-complex-diskp offset radius) (rationalp radius) (< 0 radius))
  (<= 1 (lw-complex-norm-square (lw-pole-resolvent-ratio offset radius))))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-norm-square (point offset))
        (:instance lw-complex-norm-square-valid (point offset))
        (:instance lw-pcp-multiply-order
          (a (lw-complex-norm-square offset)) (b (* radius radius))
          (factor (/ (lw-complex-norm-square offset))))
        (:instance lw-complex-norm-square-positive (point offset))
        (:instance lw-pcp-inverse-positive (x (lw-complex-norm-square offset)))
        (:instance inverse-of-* (x (lw-complex-norm-square offset))))
  :in-theory (union-theories
 '(lw-pcp-inverse-rational fold-consts-in-+ lw-pcp-offset-nonzero lw-pcp-ratio-norm lw-complex-norm-square-valid lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))))

(defthm lw-pole-cluster-power-system-outer
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (< 0 radius)
               (lw-pole-cluster-check center entries radius))
  (lw-power-outer-systemp (lw-pole-cluster-power-system center entries radius)))
 :hints (("Goal" :induct (lw-pole-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(lw-pcp-inverse-rational fold-consts-in-+ lw-pole-cluster-power-system lw-pole-cluster-check lw-power-outer-systemp lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-pcp-ratio-rational lw-pole-resolvent-data lw-pcp-ratio-outer lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pcp-weight-real-positive
 (implies (and (lw-complexp offset) (< 0 (car offset)) (posp multiplicity))
  (< 0 (car (lw-pole-resolvent-factor (cons multiplicity 0) offset))))
 :hints (("Goal"
  :use ((:instance lw-complex-norm-square-positive (point offset))
        (:instance lw-pcp-inverse-positive (x (lw-complex-norm-square offset))))
  :in-theory (union-theories
 '(lw-pcp-inverse-rational fold-consts-in-+ lw-pcp-offset-nonzero lw-complex-norm-square-valid lw-pole-resolvent-factor lw-complex-mul lw-complex-reciprocal lw-complex-conjugate lw-complex-scale lw-complexp lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t))
 :rule-classes (:rewrite :linear)))

(local (defthm lw-pcp-zero-order
 (equal (lw-complex-power point 0) (cons 1 0))
 :hints (("Goal" :in-theory (enable lw-complex-power)))))

(defthm lw-pole-cluster-total-weight-positive
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (lw-pole-cluster-check center entries radius))
  (and (<= 0 (car (lw-weighted-power-sum
                   (lw-pole-cluster-power-system center entries radius) 0)))
       (implies (consp entries)
        (< 0 (car (lw-weighted-power-sum
                   (lw-pole-cluster-power-system center entries radius) 0))))))
 :hints (("Goal" :induct (lw-pole-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(lw-pcp-inverse-rational fold-consts-in-+ lw-pole-cluster-power-system lw-pole-cluster-check lw-weighted-power-sum lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-add lw-complex-ring-rational lw-pcp-ratio-rational lw-pole-resolvent-data lw-pcp-weight-real-positive lw-pcp-zero-order lw-complex-mul-one lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-pcp-unit-term
 (implies (and (lw-complexp residue) (lw-complexp offset)
               (rationalp radius) (natp index))
  (equal
   (lw-complex-mul (lw-pole-resolvent-factor residue offset)
                   (lw-complex-power (lw-pole-resolvent-ratio offset radius) index))
   (lw-complex-scale (lw-rational-power radius index)
                     (lw-pole-coefficient residue offset index))))
 :hints (("Goal" :use (lw-pole-unit-coefficient-scaled)
          :in-theory (union-theories
 '(lw-pcp-inverse-rational fold-consts-in-+ lw-pole-unit-coefficient lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-pole-cluster-power-sum-coefficients
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (rationalp radius) (natp index))
  (equal
   (lw-weighted-power-sum (lw-pole-cluster-power-system center entries radius) index)
   (lw-complex-scale (lw-rational-power radius index)
                     (lw-pole-log-coefficient-sum center entries index))))
 :hints (("Goal" :induct (lw-pole-cluster-power-system center entries radius)
          :in-theory (union-theories
 '(lw-pcp-inverse-rational fold-consts-in-+ lw-pole-cluster-power-system lw-weighted-power-sum lw-pole-log-coefficient-sum lw-zeta-pole-familyp lw-zeta-pole-datap lw-complexp lw-complex-ring-rational lw-pole-log-coefficient-sum-rational lw-pole-coefficient-rational lw-pcp-unit-term lw-rational-power-rational lw-complex-scale-add lw-complex-scale-zero lw-pcp-left-commutes lw-pcp-left-distributes lw-pcp-fold-constants lw-pcp-times-negative lw-pcp-negative-times lw-pcp-zero-times lw-pcp-minus-one lw-pcp-double-negative lw-pcp-add-cancel lw-pcp-double lw-pcp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

