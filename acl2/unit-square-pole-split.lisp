(in-package "ACL2")

(include-book "unit-square-root-selection")
(include-book "polynomial-factor-log-sum")

; Split the reciprocal sum using exactly the selection used for the index.

(local (defthm lw-sps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-sps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-sps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-sps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-sps-times-negative (a b) (b a)))
                 :in-theory (disable lw-sps-times-negative)))))

(local (defthm lw-sps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-sps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-sps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-sps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-sps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-sps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-sps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-sps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-sps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-sps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-sps-left-commutes)))))

(defun lw-unit-square-outside-roots (roots)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) nil
   (if (equal (lw-unit-square-root-index (car roots)) 1)
       (lw-unit-square-outside-roots (cdr roots))
     (cons (car roots) (lw-unit-square-outside-roots (cdr roots))))))

(defun lw-unit-square-exterior-rootsp (roots)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) (equal roots nil)
   (and (lw-complexp (car roots))
        (< 1 (lw-complex-square-radius (car roots)))
        (lw-unit-square-exterior-rootsp (cdr roots)))))

(local (defthm lw-sps-exterior-test
 (implies (and (lw-complexp root) (not (lw-unit-square-pointp root))
               (not (equal (lw-unit-square-root-index root) 1)))
          (< 1 (lw-complex-square-radius root)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-root-index lw-unit-square-pointp lw-complex-square-radius lw-complexp abs max lw-sps-left-commutes lw-sps-left-distributes lw-sps-fold-constants lw-sps-times-negative lw-sps-negative-times lw-sps-zero-times lw-sps-minus-one lw-sps-double-negative lw-sps-add-cancel lw-sps-double lw-sps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-unit-square-exterior-roots-data
 (implies (lw-unit-square-roots-awayp roots)
          (lw-unit-square-exterior-rootsp (lw-unit-square-outside-roots roots)))
 :hints (("Goal" :induct (lw-unit-square-outside-roots roots)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-outside-roots lw-unit-square-exterior-rootsp lw-unit-square-roots-awayp lw-sps-exterior-test endp lw-sps-left-commutes lw-sps-left-distributes lw-sps-fold-constants lw-sps-times-negative lw-sps-negative-times lw-sps-zero-times lw-sps-minus-one lw-sps-double-negative lw-sps-add-cancel lw-sps-double lw-sps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-polynomial-factor-log-sum-rational
 (implies (and (lw-ray-pointsp roots) (lw-complexp point))
          (lw-complexp (lw-polynomial-factor-log-sum roots point)))
 :hints (("Goal" :induct (lw-polynomial-factor-log-sum roots point)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-polynomial-factor-log-sum lw-ray-pointsp lw-complex-ring-rational lw-complex-reciprocal-rational (:executable-counterpart lw-complexp) endp lw-sps-left-commutes lw-sps-left-distributes lw-sps-fold-constants lw-sps-times-negative lw-sps-negative-times lw-sps-zero-times lw-sps-minus-one lw-sps-double-negative lw-sps-add-cancel lw-sps-double lw-sps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-outside-roots-valid
 (implies (lw-ray-pointsp roots) (lw-ray-pointsp (lw-unit-square-outside-roots roots)))
 :hints (("Goal" :induct (lw-unit-square-outside-roots roots)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-outside-roots lw-ray-pointsp endp lw-sps-left-commutes lw-sps-left-distributes lw-sps-fold-constants lw-sps-times-negative lw-sps-negative-times lw-sps-zero-times lw-sps-minus-one lw-sps-double-negative lw-sps-add-cancel lw-sps-double lw-sps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-unit-square-factor-log-sum-split
 (implies (and (lw-ray-pointsp roots) (lw-complexp point))
  (equal (lw-polynomial-factor-log-sum roots point)
         (lw-complex-add
          (lw-polynomial-factor-log-sum (lw-unit-square-inside-roots roots) point)
          (lw-polynomial-factor-log-sum (lw-unit-square-outside-roots roots) point))))
 :hints (("Goal" :induct (lw-unit-square-outside-roots roots)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-unit-square-outside-roots lw-unit-square-inside-roots lw-polynomial-factor-log-sum lw-ray-pointsp lw-unit-square-inside-roots-valid lw-unit-square-outside-roots-valid lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-add-associative lw-complex-add-commutative lw-complex-add-zero (:executable-counterpart lw-complexp) endp lw-sps-left-commutes lw-sps-left-distributes lw-sps-fold-constants lw-sps-times-negative lw-sps-negative-times lw-sps-zero-times lw-sps-minus-one lw-sps-double-negative lw-sps-add-cancel lw-sps-double lw-sps-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))
