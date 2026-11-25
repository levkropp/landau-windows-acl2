(in-package "ACL2")

(include-book "circle-exterior-projection")
(include-book "polynomial-subtraction")

(defun lw-circle-exterior-projection-common-degree (left right radius error)
  (max (len (lw-circle-projection-interior left radius error)) (len (lw-circle-projection-interior right radius error))))

(defun lw-circle-exterior-projection-difference (left right radius target error)
  (lw-polynomial-subtract (lw-circle-exterior-projection left radius target error (lw-circle-exterior-projection-common-degree left right radius error))
                          (lw-circle-exterior-projection right radius target error (lw-circle-exterior-projection-common-degree left right radius error))))

(local (in-theory
        (disable lw-circle-exterior-projection-common-degree
                 lw-circle-exterior-projection-difference)))
(local (defthm lw-cxpd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cxpd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cxpd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cxpd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cxpd-times-negative (a b) (b a)))
                 :in-theory (disable lw-cxpd-times-negative)))))

(local (defthm lw-cxpd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cxpd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cxpd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cxpd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cxpd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cxpd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cxpd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local (defthm lw-cxpd-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-cxpd-common-degree-data
   (and (natp (lw-circle-exterior-projection-common-degree left right radius error)) (<= (len (lw-circle-projection-interior left radius error)) (lw-circle-exterior-projection-common-degree left right radius error)) (<= (len (lw-circle-projection-interior right radius error)) (lw-circle-exterior-projection-common-degree left right radius error)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) max lw-circle-exterior-projection-common-degree lw-cxpd-length-natural lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cxpd-coefficient-empty
   (equal (lw-complex-coefficient-at nil target offset) (cons 0 0))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-coefficient-at endp lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cxpd-scale-coefficient
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp factor) (natp target) (natp offset))
            (equal
             (lw-complex-coefficient-at (lw-polynomial-multiply-coefficients factor coefficients) target offset)
             (lw-complex-mul factor (lw-complex-coefficient-at coefficients target offset))))
   :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-coefficientsp lw-complex-coefficient-at lw-polynomial-multiply-coefficients lw-polynomial-multiply-coefficients-valid lw-cxpd-coefficient-empty lw-complex-coefficient-at-rational lw-complex-mul-zero lw-complex-add-zero lw-complex-mul-distribute endp lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))))

(local
 (defthm lw-cxpd-subtract-summand
   (implies (and (lw-complexp a) (lw-complexp b))
            (equal (lw-complex-add a (lw-complex-mul (cons -1 0) b))
                   (lw-complex-sub a b)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-add lw-complex-mul lw-complex-sub consp lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cxpd-subtract-coefficient
   (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (natp target) (natp offset))
            (equal (lw-complex-coefficient-at (lw-polynomial-subtract left right) target offset)
                   (lw-complex-sub (lw-complex-coefficient-at left target offset)
                                   (lw-complex-coefficient-at right target offset))))
   :hints (("Goal"
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-subtract lw-polynomial-add-coefficient lw-polynomial-multiply-coefficients-valid lw-complex-coefficient-at-rational lw-cxpd-scale-coefficient lw-cxpd-subtract-summand lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-circle-exterior-projection-difference-data
  (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
                (rationalp radius) (< 0 radius) (natp target)
                (not (lw-circle-boundary-root left radius))
                (not (lw-circle-boundary-root right radius))
                (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-circle-exterior-projection-difference left right radius target error))
                (equal (lw-complex-coefficient-at (lw-circle-exterior-projection-difference left right radius target error) (+ 1 (lw-circle-exterior-projection-common-degree left right radius error) target) 0)
                       (lw-complex-sub (lw-circle-exterior-coefficient (lw-circle-exterior-roots left radius) radius target) (lw-circle-exterior-coefficient (lw-circle-exterior-roots right radius) radius target)))))
  :hints (("Goal"
           :use (lw-cxpd-common-degree-data
                 (:instance lw-circle-exterior-projection-data (roots left) (degree (lw-circle-exterior-projection-common-degree left right radius error)))
                 (:instance lw-circle-exterior-projection-data (roots right) (degree (lw-circle-exterior-projection-common-degree left right radius error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-projection-difference lw-cxpd-subtract-coefficient lw-polynomial-subtract-valid lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-cxpd-unit-power
   (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp power))
            (lw-complex-diskp (lw-complex-power point power) 1))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (radius 1))
                  (:instance lw-complex-power-disk (radius 1) (index power)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-one lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cxpd-rearrange-differences
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp x) (lw-complexp y))
            (equal (lw-complex-sub (lw-complex-sub x y) (lw-complex-sub a b))
                   (lw-complex-sub (lw-complex-sub b y) (lw-complex-sub a x))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub consp lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-cxpd-error-sum
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp x) (lw-complexp y)
                 (rationalp cap) (rationalp error)
                 (lw-complex-diskp (lw-complex-sub a b) cap)
                 (lw-complex-diskp (lw-complex-sub a x) error)
                 (lw-complex-diskp (lw-complex-sub b y) error))
            (lw-complex-diskp (lw-complex-sub x y) (+ cap (* 2 error))))
   :hints (("Goal"
            :use ((:instance lw-complex-sub-disk
                    (left (lw-complex-sub b y)) (right (lw-complex-sub a x))
                    (radius error) (other-radius error))
                  lw-cxpd-rearrange-differences
                  (:instance lw-complex-difference-triangle
                    (left (lw-complex-sub x y)) (middle (lw-complex-sub a b)) (right (cons 0 0))
                    (radius (* 2 error)) (other-radius cap)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-ring-rational lw-complex-scale-rational lw-complex-sub-zero lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-exterior-projection-difference-bound
  (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right)
                (rationalp radius) (< 0 radius) (natp target)
                (not (lw-circle-boundary-root left radius))
                (not (lw-circle-boundary-root right radius))
                (rationalp error) (< 0 error)
                (lw-complexp point) (equal (lw-complex-norm-square point) 1)
                (lw-complex-diskp (lw-complex-sub (lw-polynomial-factor-log-sum left (lw-complex-scale radius point)) (lw-polynomial-factor-log-sum right (lw-complex-scale radius point))) cap))
           (lw-complex-diskp (lw-complex-polynomial (lw-circle-exterior-projection-difference left right radius target error) point 0) (+ cap (* 2 error))))
  :hints (("Goal"
           :use (lw-cxpd-common-degree-data
                 (:instance lw-complex-disk-data
                   (point (lw-complex-sub
                            (lw-polynomial-factor-log-sum left (lw-complex-scale radius point))
                            (lw-polynomial-factor-log-sum right (lw-complex-scale radius point))))
                   (radius cap))
                 (:instance lw-circle-exterior-projection-data (roots left) (degree (lw-circle-exterior-projection-common-degree left right radius error)))
                 (:instance lw-circle-exterior-projection-data (roots right) (degree (lw-circle-exterior-projection-common-degree left right radius error)))
                 (:instance lw-circle-exterior-projection-error (roots left) (degree (lw-circle-exterior-projection-common-degree left right radius error)))
                 (:instance lw-circle-exterior-projection-error (roots right) (degree (lw-circle-exterior-projection-common-degree left right radius error)))
                 (:instance lw-cxpd-unit-power (power (+ 1 (lw-circle-exterior-projection-common-degree left right radius error))))
                 (:instance lw-complex-left-product-error (factor (lw-complex-power point (+ 1 (lw-circle-exterior-projection-common-degree left right radius error)))) (cap 1)
                   (a (lw-polynomial-factor-log-sum left (lw-complex-scale radius point))) (b (lw-polynomial-factor-log-sum right (lw-complex-scale radius point))) (error cap))
                 (:instance lw-cxpd-error-sum
                   (a (lw-complex-mul (lw-complex-power point (+ 1 (lw-circle-exterior-projection-common-degree left right radius error))) (lw-polynomial-factor-log-sum left (lw-complex-scale radius point)))) (b (lw-complex-mul (lw-complex-power point (+ 1 (lw-circle-exterior-projection-common-degree left right radius error))) (lw-polynomial-factor-log-sum right (lw-complex-scale radius point)))) (x (lw-complex-polynomial (lw-circle-exterior-projection left radius target error (lw-circle-exterior-projection-common-degree left right radius error)) point 0)) (y (lw-complex-polynomial (lw-circle-exterior-projection right radius target error (lw-circle-exterior-projection-common-degree left right radius error)) point 0))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-projection-difference lw-polynomial-subtract-evaluation lw-polynomial-factor-log-sum-rational lw-complex-polynomial-rational lw-complex-scale-rational lw-complex-power-rational lw-complex-ring-rational lw-cxpd-left-commutes lw-cxpd-left-distributes lw-cxpd-fold-constants lw-cxpd-times-negative lw-cxpd-negative-times lw-cxpd-zero-times lw-cxpd-minus-one lw-cxpd-double-negative lw-cxpd-add-cancel lw-cxpd-double lw-cxpd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
