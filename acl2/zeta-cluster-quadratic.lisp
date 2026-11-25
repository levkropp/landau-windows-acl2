(in-package "ACL2")

(include-book "zeta-pole-quadratic")

; Scaled three-coefficient identity and an explicit norm budget.
; This is the bridge from positive-residue logarithmic derivatives to
; the normalized zeta principal parts used by the window argument.

(local (defthm lw-zcq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zcq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zcq-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zcq-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zcq-times-negative (a b) (b a)))
                 :in-theory (disable lw-zcq-times-negative)))))

(local (defthm lw-zcq-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zcq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zcq-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zcq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zcq-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zcq-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zcq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zcq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zcq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zcq-left-commutes)))))

(defun lw-pole-unit-quadratic-coefficient (center radius current previous earlier)
 (lw-complex-add
  (lw-complex-mul (lw-zeta-residue-denominator center) current)
  (lw-complex-add
   (lw-complex-scale radius
    (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) previous))
   (lw-complex-scale (* radius radius) earlier))))

(defun lw-pole-unit-quadratic-cap (center radius)
 (+ 1 (lw-complex-l1 (lw-zeta-residue-denominator center))
    (* (abs radius) (lw-complex-l1
      (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
    (* radius radius)))

(local (defthm lw-zcq-square-nonnegative
 (implies (rationalp x) (<= 0 (* x x)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-pole-unit-quadratic-cap-valid
 (implies (and (lw-complexp center) (rationalp radius))
  (and (rationalp (lw-pole-unit-quadratic-cap center radius))
       (<= 1 (lw-pole-unit-quadratic-cap center radius))))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-bound (point (lw-zeta-residue-denominator center)))
        (:instance lw-complex-l1-bound
          (point (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
        (:instance lw-zcq-square-nonnegative (x radius)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-unit-quadratic-cap lw-zeta-residue-denominator-rational lw-complex-scale-rational lw-complex-ring-rational lw-complexp abs lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t)))

(local (defthm lw-zcq-power-step
 (implies (and (rationalp radius) (natp index))
  (equal (lw-rational-power radius (+ 1 index))
         (* radius (lw-rational-power radius index))))
 :hints (("Goal" :expand ((lw-rational-power radius (+ 1 index)))))))

(local (defthm lw-zcq-power-two
 (implies (and (rationalp radius) (natp index))
  (equal (lw-rational-power radius (+ 2 index))
         (* radius radius (lw-rational-power radius index))))
 :hints (("Goal" :use ((:instance lw-zcq-power-step (index (+ 1 index))))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-zcq-power-step lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-zcq-pull-scale
 (implies (and (lw-complexp center) (rationalp radius) (rationalp factor)
               (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal
   (lw-pole-unit-quadratic-coefficient center radius
    (lw-complex-scale (* radius radius factor) a)
    (lw-complex-scale (* radius factor) b) (lw-complex-scale factor c))
   (lw-complex-scale (* radius radius factor)
    (lw-pole-quadratic-coefficient center a b c))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-unit-quadratic-coefficient lw-pole-quadratic-coefficient lw-zeta-residue-denominator lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-zcq-compose
 (implies (and (rationalp a) (rationalp b) (lw-complexp point))
  (equal (lw-complex-scale a (lw-complex-scale b point))
         (lw-complex-scale (* a b) point)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-scale lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-zeta-pole-cluster-unit-quadratic
 (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
               (lw-factor-model-away-check center entries)
               (rationalp radius) (natp index))
  (equal
   (lw-pole-unit-quadratic-coefficient center radius
    (lw-complex-scale (lw-rational-power radius (+ 2 index))
      (lw-zeta-pole-coefficient-sum center entries (+ 2 index)))
    (lw-complex-scale (lw-rational-power radius (+ 1 index))
      (lw-zeta-pole-coefficient-sum center entries (+ 1 index)))
    (lw-complex-scale (lw-rational-power radius index)
      (lw-zeta-pole-coefficient-sum center entries index)))
   (lw-complex-scale -1
    (lw-complex-scale (lw-rational-power radius (+ 2 index))
     (lw-pole-log-coefficient-sum center entries (+ 2 index))))))
 :hints (("Goal"
  :use ((:instance lw-zcq-pull-scale
          (factor (lw-rational-power radius index))
          (a (lw-zeta-pole-coefficient-sum center entries (+ 2 index)))
          (b (lw-zeta-pole-coefficient-sum center entries (+ 1 index)))
          (c (lw-zeta-pole-coefficient-sum center entries index))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-zcq-power-step lw-zcq-power-two lw-zcq-compose lw-rational-power-rational lw-zeta-pole-cluster-quadratic-coefficients lw-zeta-pole-coefficient-sum-rational lw-pole-log-coefficient-sum-rational lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-zcq-q1-rational
 (implies (lw-complexp center)
  (lw-complexp (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-scale lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-zcq-sum-cap
 (implies (and (rationalp cap) (rationalp first) (rationalp second) (rationalp radius))
  (equal (+ (* first cap) (+ (* (abs radius) (* second cap)) (* (abs (* radius radius)) cap)))
         (* cap (+ first (* (abs radius) second) (* radius radius)))))
 :hints (("Goal" :cases ((<= 0 radius))
          :in-theory (union-theories
 '(fold-consts-in-+ abs lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-zcq-abs-square
 (implies (rationalp radius) (equal (abs (* radius radius)) (* radius radius)))
 :hints (("Goal" :use ((:instance lw-zcq-square-nonnegative (x radius)))
          :in-theory (union-theories
 '(fold-consts-in-+ abs lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(local (defthm lw-zcq-rational-sum
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-zcq-rational-product
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-zcq-rational-negative
 (implies (rationalp a) (rationalp (- a)))
 :rule-classes (:rewrite :type-prescription)))

(defthm lw-pole-unit-quadratic-bound
 (implies (and (lw-complexp center) (rationalp radius)
               (rationalp cap) (<= 0 cap)
               (lw-complex-diskp current cap)
               (lw-complex-diskp previous cap)
               (lw-complex-diskp earlier cap))
  (lw-complex-diskp
   (lw-pole-unit-quadratic-coefficient center radius current previous earlier)
   (* cap (lw-pole-unit-quadratic-cap center radius))))
 :hints (("Goal"
  :use (lw-pole-unit-quadratic-cap-valid
        (:instance lw-complex-l1-bound (point (lw-zeta-residue-denominator center)))
        (:instance lw-complex-l1-bound
          (point (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
        (:instance lw-complex-mul-disk
          (left (lw-zeta-residue-denominator center)) (right current)
          (radius (lw-complex-l1 (lw-zeta-residue-denominator center))) (other-radius cap))
        (:instance lw-complex-mul-disk
          (left (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))) (right previous)
          (radius (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
          (other-radius cap))
        (:instance lw-complex-scale-disk
          (point (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) previous))
          (factor radius)
          (radius (* cap (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))))
        (:instance lw-complex-scale-disk (point earlier) (factor (* radius radius)) (radius cap))
        (:instance lw-complex-add-disk
          (left (lw-complex-scale radius
            (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) previous)))
          (right (lw-complex-scale (* radius radius) earlier))
          (radius (* (abs radius) cap
            (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)))))
          (other-radius (* (abs (* radius radius)) cap)))
        (:instance lw-complex-add-disk
          (left (lw-complex-mul (lw-zeta-residue-denominator center) current))
          (right (lw-complex-add
            (lw-complex-scale radius
             (lw-complex-mul (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center)) previous))
            (lw-complex-scale (* radius radius) earlier)))
          (radius (* cap (lw-complex-l1 (lw-zeta-residue-denominator center))))
          (other-radius (+ (* (abs radius) cap
             (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
             (* (abs (* radius radius)) cap))))
        (:instance lw-complex-disk-enlarge
          (point (lw-pole-unit-quadratic-coefficient center radius current previous earlier))
          (radius (* cap (+ (lw-complex-l1 (lw-zeta-residue-denominator center))
             (* (abs radius) (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 center))))
             (* radius radius))))
          (cap (* cap (lw-pole-unit-quadratic-cap center radius)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-unit-quadratic-coefficient lw-pole-unit-quadratic-cap lw-zeta-residue-denominator-rational lw-zcq-q1-rational lw-complex-l1-bound lw-zcq-rational-sum lw-zcq-rational-product lw-zcq-rational-negative abs lw-zcq-abs-square lw-zcq-sum-cap lw-zcq-left-commutes lw-zcq-left-distributes lw-zcq-fold-constants lw-zcq-times-negative lw-zcq-negative-times lw-zcq-zero-times lw-zcq-minus-one lw-zcq-double-negative lw-zcq-add-cancel lw-zcq-double lw-zcq-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

