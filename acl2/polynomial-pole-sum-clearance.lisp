(in-package "ACL2")

(include-book "polynomial-factor-log-sum")

; A common distance bound gives an explicit reciprocal sum bound.

(local (defthm lw-psc2-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-psc2-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-psc2-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-psc2-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-psc2-times-negative (a b) (b a)))
                 :in-theory (disable lw-psc2-times-negative)))))

(local (defthm lw-psc2-zero-times (equal (* 0 a) 0)))

(local (defthm lw-psc2-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-psc2-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-psc2-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-psc2-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-psc2-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-psc2-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-psc2-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc2-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-psc2-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-psc2-left-commutes)))))

(defun lw-polynomial-root-clearancesp (roots point clearance)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     (equal roots nil)
   (and (not (lw-complex-diskp (lw-complex-sub point (car roots)) clearance))
        (lw-polynomial-root-clearancesp (cdr roots) point clearance))))

(local (defthm lw-psc2-square-bound
 (implies (and (lw-complexp diff) (rationalp clearance) (< 0 clearance)
               (not (lw-complex-diskp diff clearance)))
  (lw-complex-diskp (lw-complex-reciprocal diff) (/ clearance)))
 :hints (("Goal"
  :use ((:instance lw-complex-disk-norm-square (point diff) (radius clearance))
        (:instance lw-complex-reciprocal-disk-bound (point diff) (lower clearance)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-psc2-left-commutes lw-psc2-left-distributes lw-psc2-fold-constants lw-psc2-times-negative lw-psc2-negative-times lw-psc2-zero-times lw-psc2-minus-one lw-psc2-double-negative lw-psc2-add-cancel lw-psc2-double lw-psc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-psc2-length-natural
 (natp (len roots)) :rule-classes (:type-prescription :rewrite)))

(defthm lw-polynomial-factor-log-sum-clearance-bound
 (implies (and (lw-ray-pointsp roots) (lw-complexp point)
               (rationalp clearance) (< 0 clearance)
               (lw-polynomial-root-clearancesp roots point clearance))
  (lw-complex-diskp (lw-polynomial-factor-log-sum roots point) (* (len roots) (/ clearance))))
 :hints (("Goal" :induct (lw-polynomial-factor-log-sum roots point)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-log-sum lw-polynomial-root-clearancesp lw-ray-pointsp lw-complex-ring-rational lw-psc2-square-bound lw-psc2-length-natural lw-complex-zero-disk len endp lw-psc2-left-commutes lw-psc2-left-distributes lw-psc2-fold-constants lw-psc2-times-negative lw-psc2-negative-times lw-psc2-zero-times lw-psc2-minus-one lw-psc2-double-negative lw-psc2-add-cancel lw-psc2-double lw-psc2-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-add-disk
           (left (lw-complex-reciprocal (lw-complex-sub point (car roots))))
           (right (lw-polynomial-factor-log-sum (cdr roots) point))
           (radius (/ clearance)) (other-radius (* (len (cdr roots)) (/ clearance)))))
    :do-not-induct t))))
