(in-package "ACL2")

(include-book "rpow-continuity")

; The exact secant cofactor of x^n is a finite sum of n monomials.
; Between ordered nonnegative endpoints it lies between the endpoint slopes.

(local (defthm lw-rps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rps-times-negative (a b) (b a)))
                 :in-theory (disable lw-rps-times-negative)))))

(local (defthm lw-rps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rps-left-commutes)))))

(defun lw-rational-power-secant (left right degree)
  (declare (xargs :measure (nfix degree)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp degree)
      0
    (+ (lw-rational-power left (- degree 1)) (* right (lw-rational-power-secant left right (- degree 1))))))

(defthm lw-rational-power-secant-rational
   (implies (and (rationalp left) (rationalp right))
            (rationalp (lw-rational-power-secant left right degree)))
   :hints (("Goal" :induct (lw-rational-power-secant left right degree)
                   :in-theory (union-theories
            '(fold-consts-in-+
              (:induction lw-rational-power-secant)
              lw-rational-power-secant lw-rational-power-rational
              lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants
              lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times
              lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes (:rewrite :type-prescription))

(local
 (defthm lw-rps-scale-equality
   (implies (equal a b)
            (equal (* factor a) (* factor b)))
   :rule-classes nil))

(local
 (defthm lw-rps-secant-step
   (implies (and (rationalp left) (rationalp right) (rationalp a) (rationalp b) (rationalp old)
                 (equal (- b a) (* (- right left) old)))
            (equal (- (* right b) (* left a))
                   (* (- right left) (+ a (* right old)))))
   :hints (("Goal" :use ((:instance lw-rps-scale-equality
                              (a (- b a)) (b (* (- right left) old)) (factor right)))
                   :in-theory (union-theories
            '(fold-consts-in-+

              lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants
              lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times
              lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t :nonlinearp t))
   :rule-classes nil))

(defthm lw-rational-power-secant-identity
  (implies (and (rationalp left) (rationalp right) (natp degree))
           (equal (- (lw-rational-power right degree) (lw-rational-power left degree))
                  (* (- right left) (lw-rational-power-secant left right degree))))
  :hints (("Goal"
           :induct (lw-rational-power-secant left right degree)
           :in-theory (union-theories
            '(fold-consts-in-+
              (:induction lw-rational-power-secant)
              lw-rational-power-secant lw-rational-power lw-rational-power-rational lw-rational-power-secant-rational
              lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants
              lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times
              lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-rps-secant-step
                        (a (lw-rational-power left (- degree 1)))
                        (b (lw-rational-power right (- degree 1)))
                        (old (lw-rational-power-secant left right (- degree 1)))))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-rps-secant-budget
   (implies (and (rationalp n) (<= 0 n)
                 (rationalp previous-left) (<= 0 previous-left)
                 (rationalp previous-right) (<= 0 previous-right)
                 (rationalp next-left) (rationalp next-right) (<= next-left next-right)
                 (rationalp right) (<= 0 right)
                 (rationalp old) (<= (* n previous-left) old) (<= old (* n previous-right))
                 (<= next-left (* right previous-left))
                 (equal next-right (* right previous-right)))
            (and (<= (* (+ 1 n) next-left) (+ next-left (* right old)))
                 (<= (+ next-left (* right old)) (* (+ 1 n) next-right))))
   :hints (("Goal"
            :use ((:instance lw-rps-multiply-order (a (* n previous-left)) (b old) (factor right))
                  (:instance lw-rps-multiply-order (a old) (b (* n previous-right)) (factor right))
                  (:instance lw-rps-multiply-order (a next-left) (b (* right previous-left)) (factor n)))
            :in-theory (union-theories
            '(fold-consts-in-+

              lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants
              lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times
              lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-rps-empty-secant
   (equal (lw-rational-power-secant left right 0) 0)
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+
              lw-rational-power-secant
              lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants
              lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times
              lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-rps-power-zero
   (equal (lw-rational-power base 0) 1)
   :hints (("Goal" :in-theory (union-theories '(lw-rational-power zp) (theory 'minimal-theory))))))

(defthm lw-rational-power-secant-bounds
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right) (natp degree))
           (and (<= (* degree (lw-rational-power left (- degree 1))) (lw-rational-power-secant left right degree))
                (<= (lw-rational-power-secant left right degree) (* degree (lw-rational-power right (- degree 1))))))
  :hints (("Goal"
           :induct (lw-rational-power-secant left right degree)
           :in-theory (union-theories
            '(fold-consts-in-+
              (:induction lw-rational-power-secant)
              lw-rational-power-secant lw-rational-power-secant-rational lw-rps-empty-secant lw-rps-power-zero
              (:executable-counterpart lw-rational-power) lw-rational-power-rational
              lw-rps-left-commutes lw-rps-left-distributes lw-rps-fold-constants
              lw-rps-times-negative lw-rps-negative-times lw-rps-zero-times
              lw-rps-minus-one lw-rps-double-negative lw-rps-add-cancel lw-rps-double lw-rps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:cases ((equal degree 1))
                 :expand ((lw-rational-power left (- degree 1)) (lw-rational-power right (- degree 1)))
                 :use ((:instance lw-rational-power-nonnegative (base left) (exponent (- degree 2)))
                       (:instance lw-rational-power-nonnegative (base right) (exponent (- degree 2)))
                       (:instance lw-rational-power-monotone-base (exponent (- degree 1)))
                       (:instance lw-rps-multiply-order (a left) (b right) (factor (lw-rational-power left (- degree 2))))
                       (:instance lw-rps-secant-budget (n (- degree 1))
                         (previous-left (lw-rational-power left (- degree 2))) (previous-right (lw-rational-power right (- degree 2)))
                         (next-left (lw-rational-power left (- degree 1))) (next-right (lw-rational-power right (- degree 1))) (old (lw-rational-power-secant left right (- degree 1)))))
                 :do-not-induct t)))
  :rule-classes nil)
