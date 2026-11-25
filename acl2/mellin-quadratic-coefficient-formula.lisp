(in-package "ACL2")

(include-book "mellin-quadratic-normalization")
(include-book "zeta-pole-quadratic")
(include-book "polynomial-coefficient-maps")

(local (defthm lw-mqcf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mqcf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mqcf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mqcf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-mqcf-times-negative (a b) (b a)))
                 :in-theory (disable lw-mqcf-times-negative)))))

(local (defthm lw-mqcf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mqcf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mqcf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-mqcf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mqcf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-mqcf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-mqcf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-mqcf-add-constant-coefficient
   (implies (and (lw-complexp constant) (lw-complex-coefficientsp coefficients)
                 (natp target) (natp offset))
            (equal (lw-complex-coefficient-at (lw-polynomial-add-constant constant coefficients) target offset)
                   (lw-complex-add (if (equal target offset) constant (cons 0 0)) (lw-complex-coefficient-at coefficients target offset))))
   :hints (("Goal" :cases ((consp coefficients) (equal target offset))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-add-constant lw-complex-coefficientsp lw-complex-coefficient-at lw-complex-coefficient-at-rational lw-complex-add-associative lw-complex-add-zero lw-complex-ring-rational endp lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defun lw-mqcf-linear-coefficient-induct (coefficients offset)
   (if (endp coefficients) offset
     (lw-mqcf-linear-coefficient-induct (cdr coefficients) (+ 1 offset)))))

(defthm lw-polynomial-multiply-linear-coefficient
  (implies (and (lw-complexp constant) (lw-complexp slope)
                (lw-complex-coefficientsp coefficients) (natp target) (natp offset))
           (equal (lw-complex-coefficient-at (lw-polynomial-multiply-linear constant slope coefficients) target offset)
                  (lw-complex-add
                   (lw-complex-mul constant (lw-complex-coefficient-at coefficients target offset))
                   (lw-complex-mul slope (lw-complex-coefficient-at coefficients target (+ 1 offset))))))
  :hints (("Goal" :induct (lw-mqcf-linear-coefficient-induct coefficients offset)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:induction lw-mqcf-linear-coefficient-induct) lw-polynomial-multiply-linear lw-complex-coefficientsp lw-complex-coefficient-at lw-complex-coefficient-at-rational lw-polynomial-multiply-linear-valid lw-mqcf-add-constant-coefficient lw-complex-ring-rational lw-complex-add-zero lw-complex-mul-zero lw-complex-add-associative lw-complex-add-left-commutes lw-complex-add-commutative lw-complex-mul-distribute endp lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local
 (defthm lw-mqcf-product-coefficient-algebra
   (implies (and (lw-complexp a) (lw-complexp b)
                 (lw-complexp x) (lw-complexp y) (lw-complexp z))
            (equal (lw-complex-add (lw-complex-mul a (lw-complex-add (lw-complex-mul b x) y))
                                   (lw-complex-add (lw-complex-mul b y) z))
                   (lw-complex-add (lw-complex-mul (lw-complex-mul a b) x)
                                   (lw-complex-add (lw-complex-mul (lw-complex-add a b) y) z))))
   :hints (("Goal"
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-mul-distribute lw-complex-mul-add-left lw-complex-ring-rational lw-complex-mul-associative lw-complex-add-associative lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-mqcf-product-coefficient-offset
   (implies (and (lw-complexp anchor) (lw-complex-coefficientsp coefficients)
                 (natp target) (natp offset))
            (equal (lw-complex-coefficient-at (lw-polynomial-mellin-quadratic anchor coefficients) target offset)
                   (lw-complex-add
                    (lw-complex-mul (lw-zeta-residue-denominator anchor) (lw-complex-coefficient-at coefficients target offset))
                    (lw-complex-add
                     (lw-complex-mul (lw-complex-add anchor (lw-complex-sub anchor (cons 1 0))) (lw-complex-coefficient-at coefficients target (+ 1 offset)))
                     (lw-complex-coefficient-at coefficients target (+ 2 offset))))))
   :hints (("Goal"
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-mellin-quadratic lw-polynomial-multiply-linear-coefficient lw-polynomial-multiply-linear-valid lw-mqcf-product-coefficient-algebra lw-complex-mul-one lw-complex-coefficient-at-rational lw-complex-ring-rational lw-zeta-residue-denominator lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-mqcf-offset-coefficient
   (implies (and (lw-complex-coefficientsp coefficients)
                 (natp target) (natp offset) (natp delta))
            (equal (lw-complex-coefficient-at coefficients (+ delta target) (+ delta offset)) (lw-complex-coefficient-at coefficients target offset)))
   :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-coefficient-at lw-complex-coefficientsp endp lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(local
 (defthm lw-mqcf-reflected-ring
   (implies (and (lw-complexp anchor) (lw-complexp x) (lw-complexp y) (lw-complexp z) (rationalp sign))
            (equal
             (lw-complex-scale sign
              (lw-complex-add (lw-complex-mul (lw-zeta-residue-denominator anchor) x)
               (lw-complex-add (lw-complex-mul (lw-complex-add anchor (lw-complex-sub anchor (cons 1 0))) y) z)))
             (lw-pole-quadratic-coefficient anchor
              (lw-complex-scale sign x)
              (lw-complex-scale (- sign) y)
              (lw-complex-scale sign z))))
   :hints (("Goal"
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pole-quadratic-coefficient lw-zeta-residue-denominator lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale consp lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-mqcf-reflected-signs
   (implies (natp index)
            (and (equal (lw-rational-power -1 (+ 2 index)) (lw-rational-power -1 index))
                 (equal (lw-rational-power -1 (+ 1 index)) (- (lw-rational-power -1 index)))))
   :hints (("Goal"
            :expand ((lw-rational-power -1 (+ 2 index)) (lw-rational-power -1 (+ 1 index)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-rational lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-polynomial-mellin-quadratic-reflected-coefficient
  (implies (and (lw-complexp anchor) (lw-complex-coefficientsp coefficients) (natp index))
           (equal
            (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at (lw-polynomial-mellin-quadratic anchor coefficients) (+ 2 index) 0))
            (lw-pole-quadratic-coefficient anchor
             (lw-complex-scale (lw-rational-power -1 (+ 2 index)) (lw-complex-coefficient-at coefficients (+ 2 index) 0))
             (lw-complex-scale (lw-rational-power -1 (+ 1 index)) (lw-complex-coefficient-at coefficients (+ 1 index) 0))
             (lw-complex-scale (lw-rational-power -1 index) (lw-complex-coefficient-at coefficients index 0)))))
  :hints (("Goal"
           :use ((:instance lw-mqcf-product-coefficient-offset (target (+ 2 index)) (offset 0))
                 (:instance lw-mqcf-offset-coefficient (target (+ 1 index)) (offset 0) (delta 1))
                 (:instance lw-mqcf-offset-coefficient (target index) (offset 0) (delta 2))
                 (:instance lw-mqcf-reflected-ring
                   (x (lw-complex-coefficient-at coefficients (+ 2 index) 0))
                   (y (lw-complex-coefficient-at coefficients (+ 1 index) 0))
                   (z (lw-complex-coefficient-at coefficients index 0)) (sign (lw-rational-power -1 index))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-mqcf-reflected-signs lw-complex-coefficient-at-rational lw-rational-power-rational lw-mqcf-left-commutes lw-mqcf-left-distributes lw-mqcf-fold-constants lw-mqcf-times-negative lw-mqcf-negative-times lw-mqcf-zero-times lw-mqcf-minus-one lw-mqcf-double-negative lw-mqcf-add-cancel lw-mqcf-double lw-mqcf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
