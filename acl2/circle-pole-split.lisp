(in-package "ACL2")

(include-book "unit-square-pole-split")

; Radial selection in the physical offset coordinate.

(local (defthm lw-cps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cps-times-negative (a b) (b a)))
                 :in-theory (disable lw-cps-times-negative)))))

(local (defthm lw-cps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cps-left-commutes)))))

(defun lw-circle-pole-roots (roots radius)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     nil
   (if (< (lw-complex-norm-square (car roots)) (* radius radius))
       (cons (car roots) (lw-circle-pole-roots (cdr roots) radius))
     (lw-circle-pole-roots (cdr roots) radius))))

(defun lw-circle-exterior-roots (roots radius)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     nil
   (if (< (lw-complex-norm-square (car roots)) (* radius radius))
       (lw-circle-exterior-roots (cdr roots) radius)
     (cons (car roots) (lw-circle-exterior-roots (cdr roots) radius)))))

(defun lw-circle-boundary-root (roots radius)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     nil
   (if (equal (lw-complex-norm-square (car roots)) (* radius radius))
       (car roots)
     (lw-circle-boundary-root (cdr roots) radius))))

(defun lw-circle-exterior-rootsp (roots radius)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     (equal roots nil)
   (and (lw-complexp (car roots))
        (< (* radius radius) (lw-complex-norm-square (car roots)))
        (lw-circle-exterior-rootsp (cdr roots) radius))))

(defthm lw-circle-boundary-root-data
 (implies (and (lw-ray-pointsp roots) (lw-circle-boundary-root roots radius))
  (let ((root (lw-circle-boundary-root roots radius)))
   (and (lw-complexp root) (member-equal root roots)
        (equal (lw-complex-norm-square root) (* radius radius)))))
 :hints (("Goal" :induct (lw-circle-boundary-root roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-boundary-root lw-ray-pointsp member-equal endp lw-cps-left-commutes lw-cps-left-distributes lw-cps-fold-constants lw-cps-times-negative lw-cps-negative-times lw-cps-zero-times lw-cps-minus-one lw-cps-double-negative lw-cps-add-cancel lw-cps-double lw-cps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-circle-pole-split-valid
 (implies (lw-ray-pointsp roots)
  (and (lw-ray-pointsp (lw-circle-pole-roots roots radius))
       (lw-ray-pointsp (lw-circle-exterior-roots roots radius))))
 :hints (("Goal" :induct (lw-circle-pole-roots roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-pole-roots lw-circle-exterior-roots lw-ray-pointsp endp lw-cps-left-commutes lw-cps-left-distributes lw-cps-fold-constants lw-cps-times-negative lw-cps-negative-times lw-cps-zero-times lw-cps-minus-one lw-cps-double-negative lw-cps-add-cancel lw-cps-double lw-cps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-circle-exterior-roots-data
 (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius) (not (lw-circle-boundary-root roots radius)))
  (lw-circle-exterior-rootsp (lw-circle-exterior-roots roots radius) radius))
 :hints (("Goal" :induct (lw-circle-exterior-roots roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-boundary-root lw-circle-exterior-roots lw-circle-exterior-rootsp lw-ray-pointsp lw-complex-norm-square-valid (:executable-counterpart lw-complexp) endp lw-cps-left-commutes lw-cps-left-distributes lw-cps-fold-constants lw-cps-times-negative lw-cps-negative-times lw-cps-zero-times lw-cps-minus-one lw-cps-double-negative lw-cps-add-cancel lw-cps-double lw-cps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-circle-factor-log-sum-split
 (implies (and (lw-ray-pointsp roots) (lw-complexp point))
  (equal (lw-polynomial-factor-log-sum roots point)
   (lw-complex-add (lw-polynomial-factor-log-sum (lw-circle-pole-roots roots radius) point)
                   (lw-polynomial-factor-log-sum (lw-circle-exterior-roots roots radius) point))))
 :hints (("Goal" :induct (lw-circle-exterior-roots roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-pole-roots lw-circle-exterior-roots lw-circle-pole-split-valid lw-polynomial-factor-log-sum lw-ray-pointsp lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-add-associative lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-add-zero (:executable-counterpart lw-complexp) endp lw-cps-left-commutes lw-cps-left-distributes lw-cps-fold-constants lw-cps-times-negative lw-cps-negative-times lw-cps-zero-times lw-cps-minus-one lw-cps-double-negative lw-cps-add-cancel lw-cps-double lw-cps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
