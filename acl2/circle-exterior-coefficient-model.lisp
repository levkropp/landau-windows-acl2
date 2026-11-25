(in-package "ACL2")

(include-book "circle-pole-split")
(include-book "circle-exterior-pole-polynomial")
(include-book "polynomial-sum-coefficients")

; Sum the finitely many exterior resolvents with a recursively split error.

(local (defthm lw-cec-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cec-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cec-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cec-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cec-times-negative (a b) (b a)))
                 :in-theory (disable lw-cec-times-negative)))))

(local (defthm lw-cec-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cec-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cec-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cec-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cec-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cec-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cec-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cec-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cec-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cec-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cec-left-commutes)))))

(local (defthm lw-cec-half-data
 (implies (and (rationalp error) (< 0 error))
  (and (rationalp (* 1/2 error)) (< 0 (* 1/2 error))
       (equal (+ (* 1/2 error) (* 1/2 error)) error)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defun lw-circle-exterior-polynomial (roots radius target error)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     nil
   (lw-polynomial-add (lw-circle-exterior-pole-polynomial (car roots) radius target (* 1/2 error)) (lw-circle-exterior-polynomial (cdr roots) radius target (* 1/2 error)))))

(defun lw-circle-exterior-coefficient (roots radius target)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots)
     (cons 0 0)
   (lw-complex-add
    (lw-pole-unit-coefficient (cons 1 0) (lw-complex-scale -1 (car roots)) (- radius) target)
    (lw-circle-exterior-coefficient (cdr roots) radius target))))

(defthm lw-circle-exterior-roots-typed
 (implies (lw-circle-exterior-rootsp roots radius) (lw-ray-pointsp roots))
 :hints (("Goal" :induct (lw-circle-exterior-rootsp roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-rootsp lw-ray-pointsp endp lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-circle-exterior-polynomial-valid
 (implies (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error)) (lw-complex-coefficientsp (lw-circle-exterior-polynomial roots radius target error)))
 :hints (("Goal" :induct (lw-circle-exterior-polynomial roots radius target error)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-polynomial lw-circle-exterior-rootsp lw-circle-exterior-pole-polynomial-valid lw-polynomial-add-valid lw-complex-coefficientsp lw-cec-half-data endp lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cec-nil-coefficient
 (equal (lw-complex-coefficient-at nil target 0) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficient-at endp lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-exterior-polynomial-coefficient
 (implies (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error))
  (equal (lw-complex-coefficient-at (lw-circle-exterior-polynomial roots radius target error) target 0)
         (lw-circle-exterior-coefficient roots radius target)))
 :hints (("Goal" :induct (lw-circle-exterior-polynomial roots radius target error)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-polynomial lw-circle-exterior-coefficient lw-circle-exterior-rootsp lw-circle-exterior-polynomial-valid lw-circle-exterior-pole-polynomial-valid lw-circle-exterior-pole-polynomial-coefficient lw-polynomial-add-coefficient lw-cec-half-data lw-cec-nil-coefficient endp lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cec-nil-evaluation
 (equal (lw-complex-polynomial nil point 0) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial endp lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-exterior-polynomial-error
 (implies (and (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error)) (lw-complex-diskp point 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point)) (lw-complex-polynomial (lw-circle-exterior-polynomial roots radius target error) point 0))
   error))
 :hints (("Goal" :induct (lw-circle-exterior-polynomial roots radius target error)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-polynomial lw-circle-exterior-rootsp lw-polynomial-factor-log-sum lw-circle-exterior-polynomial-valid lw-circle-exterior-pole-polynomial-valid lw-circle-exterior-roots-typed lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-complex-scale-rational lw-complex-reciprocal-rational lw-complex-polynomial-rational lw-complex-sub-zero lw-complex-zero-disk lw-cec-half-data lw-cec-nil-evaluation (:executable-counterpart lw-complexp) endp lw-cec-left-commutes lw-cec-left-distributes lw-cec-fold-constants lw-cec-times-negative lw-cec-negative-times lw-cec-zero-times lw-cec-minus-one lw-cec-double-negative lw-cec-add-cancel lw-cec-double lw-cec-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-disk-data (radius 1))
          (:instance lw-circle-exterior-pole-polynomial-error (root (car roots)) (error (* 1/2 error)))
          (:instance lw-polynomial-add-evaluation (left (lw-circle-exterior-pole-polynomial (car roots) radius target (* 1/2 error))) (right (lw-circle-exterior-polynomial (cdr roots) radius target (* 1/2 error))) (offset 0))
          (:instance lw-complex-sub-add (a (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) (car roots)))) (b (lw-polynomial-factor-log-sum (cdr roots) (lw-complex-scale radius point)))
           (c (lw-complex-polynomial (lw-circle-exterior-pole-polynomial (car roots) radius target (* 1/2 error)) point 0)) (d (lw-complex-polynomial (lw-circle-exterior-polynomial (cdr roots) radius target (* 1/2 error)) point 0)))
          (:instance lw-complex-add-disk
           (left (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) (car roots))) (lw-complex-polynomial (lw-circle-exterior-pole-polynomial (car roots) radius target (* 1/2 error)) point 0))) (radius (* 1/2 error))
           (right (lw-complex-sub (lw-polynomial-factor-log-sum (cdr roots) (lw-complex-scale radius point)) (lw-complex-polynomial (lw-circle-exterior-polynomial (cdr roots) radius target (* 1/2 error)) point 0))) (other-radius (* 1/2 error))))
    :do-not-induct t))))
