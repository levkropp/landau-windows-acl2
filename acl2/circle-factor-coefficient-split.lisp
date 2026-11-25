(in-package "ACL2")

(include-book "circle-exterior-coefficient-model")
(include-book "complex-exp")
(include-book "rpow-continuity")

; A coefficient of the full reciprocal sum can be split at a different
; radius from the one used to normalize the expansion around the center.

(local (defthm lw-cfcs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfcs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfcs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfcs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfcs-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfcs-times-negative)))))

(local (defthm lw-cfcs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfcs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfcs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfcs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfcs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfcs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfcs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-cfcs-pole-unit-rational
   (implies (and (lw-complexp root) (rationalp radius) (natp index))
            (lw-complexp (lw-pole-unit-coefficient (cons 1 0) (lw-complex-scale -1 root) radius index)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pole-unit-coefficient-formula lw-complex-scale-rational lw-complex-power-rational lw-complex-ring-rational lw-complex-reciprocal-rational lw-rational-power-rational lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(defthm lw-circle-factor-coefficient-rational
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (natp index))
           (lw-complexp (lw-circle-exterior-coefficient roots radius index)))
  :hints (("Goal" :induct (lw-circle-exterior-coefficient roots radius index)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-coefficient lw-cfcs-pole-unit-rational lw-ray-pointsp lw-complex-ring-rational endp lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(defthm lw-circle-factor-coefficient-split
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (natp index))
           (equal (lw-circle-exterior-coefficient roots radius index)
                  (lw-complex-add (lw-circle-exterior-coefficient (lw-circle-pole-roots roots split-radius) radius index) (lw-circle-exterior-coefficient (lw-circle-exterior-roots roots split-radius) radius index))))
  :hints (("Goal" :induct (lw-circle-pole-roots roots split-radius)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-coefficient lw-circle-pole-roots lw-circle-exterior-roots lw-circle-pole-split-valid lw-circle-factor-coefficient-rational lw-cfcs-pole-unit-rational lw-ray-pointsp lw-complex-ring-rational lw-complex-add-associative lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-add-zero endp lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local
 (defthm lw-cfcs-pole-unit-scaled
   (implies (and (lw-complexp root) (rationalp radius) (natp index))
            (equal (lw-pole-unit-coefficient (cons 1 0) (lw-complex-scale -1 root) (- radius) index)
                   (lw-complex-scale (lw-rational-power (- radius) index)
                     (lw-pole-unit-coefficient (cons 1 0) (lw-complex-scale -1 root) 1 index))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pole-unit-coefficient-formula lw-complex-scale-rational lw-complex-power-rational lw-complex-ring-rational lw-complex-reciprocal-rational lw-rational-power-one lw-complex-scale-one lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-factor-coefficient-reflected-scaling
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (natp index))
           (equal (lw-circle-exterior-coefficient roots radius index)
                  (lw-complex-scale (lw-rational-power (- radius) index)
                                    (lw-circle-exterior-coefficient roots -1 index))))
  :hints (("Goal" :induct (lw-circle-exterior-coefficient roots radius index)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-coefficient lw-cfcs-pole-unit-scaled lw-circle-factor-coefficient-rational lw-cfcs-pole-unit-rational lw-ray-pointsp lw-complex-scale-add lw-complex-scale-zero lw-complex-scale-rational lw-complex-ring-rational lw-rational-power-rational endp lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local
 (defthm lw-cfcs-sign-power
   (or (equal (lw-rational-power -1 index) 1)
       (equal (lw-rational-power -1 index) -1))
   :hints (("Goal" :induct (lw-rational-power -1 index)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(local
 (defthm lw-cfcs-signed-scale-inverse
   (implies (and (lw-complexp point) (rationalp factor) (< 0 factor)
                 (or (equal sign 1) (equal sign -1))
                 (lw-complex-diskp (lw-complex-scale (* sign factor) point) cap))
            (lw-complex-diskp point (* cap (/ factor))))
   :hints (("Goal"
            :cases ((equal sign 1))
            :use ((:instance lw-complex-scale-disk
                    (point (lw-complex-scale (* sign factor) point)) (radius cap) (factor (* sign (/ factor))))
                  (:instance lw-complex-scale-compose
                    (left (* sign (/ factor))) (right (* sign factor)))
                  (:instance inverse-of-* (x factor)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) abs lw-complex-scale-one lw-reciprocal-positive lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-factor-reflected-scale-inverse
  (implies (and (lw-complexp point) (rationalp radius) (< 0 radius) (natp index)
                (lw-complex-diskp (lw-complex-scale (lw-rational-power (- radius) index) point) cap))
           (lw-complex-diskp point (* cap (/ (lw-rational-power radius index)))))
  :hints (("Goal"
           :use (lw-cfcs-sign-power
                 (:instance lw-rational-power-product (left -1) (right radius) (exponent index))
                 (:instance lw-rational-power-positive (base radius) (exponent index))
                 (:instance lw-cfcs-signed-scale-inverse (sign (lw-rational-power -1 index)) (factor (lw-rational-power radius index))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-rational lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-factor-reflected-scale-compose
  (implies (and (lw-complexp point) (rationalp radius) (natp index))
           (equal (lw-complex-scale (lw-rational-power (- radius) index) (lw-complex-scale (lw-rational-power -1 index) point))
                  (lw-complex-scale (lw-rational-power radius index) point)))
  :hints (("Goal"
           :use ((:instance lw-rational-power-product (left -1) (right (- radius)) (exponent index)))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-rational lw-complex-scale-compose lw-cfcs-left-commutes lw-cfcs-left-distributes lw-cfcs-fold-constants lw-cfcs-times-negative lw-cfcs-negative-times lw-cfcs-zero-times lw-cfcs-minus-one lw-cfcs-double-negative lw-cfcs-add-cancel lw-cfcs-double lw-cfcs-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
