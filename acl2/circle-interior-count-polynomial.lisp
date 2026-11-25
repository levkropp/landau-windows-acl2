(in-package "ACL2")

(include-book "circle-interior-count-resolvent")
(include-book "circle-pole-split")
(include-book "polynomial-sum-coefficients")

; The conjugate of this ordinary polynomial models the weighted interior sum.

(local (defthm lw-cip-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cip-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cip-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cip-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cip-times-negative (a b) (b a)))
                 :in-theory (disable lw-cip-times-negative)))))

(local (defthm lw-cip-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cip-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cip-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cip-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cip-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cip-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cip-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cip-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cip-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cip-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cip-left-commutes)))))

(defun lw-circle-interior-rootsp (roots radius)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) (equal roots nil)
   (and (lw-complexp (car roots))
        (< (lw-complex-norm-square (car roots)) (* radius radius))
        (lw-circle-interior-rootsp (cdr roots) radius))))

(defthm lw-circle-selected-interior-rootsp
 (implies (lw-ray-pointsp roots)
  (lw-circle-interior-rootsp (lw-circle-pole-roots roots radius) radius))
 :hints (("Goal" :induct (lw-circle-pole-roots roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-pole-roots lw-circle-interior-rootsp lw-ray-pointsp endp lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cip-interior-typed
 (implies (lw-circle-interior-rootsp roots radius) (lw-ray-pointsp roots))
 :hints (("Goal" :induct (lw-circle-interior-rootsp roots radius)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-rootsp lw-ray-pointsp endp lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defun lw-circle-interior-count-term (root radius error)
 (lw-resolvent-coefficients
  (lw-circle-interior-count-ratio root radius) 0 (lw-resolvent-truncation-count (lw-circle-interior-count-ratio-cap root radius) error)))

(local (defthm lw-cip-term-data
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (lw-complex-norm-square root) (* radius radius))) (rationalp error) (< 0 error))
  (and (lw-complex-coefficientsp (lw-circle-interior-count-term root radius error))
       (equal (lw-complex-coefficient-at (lw-circle-interior-count-term root radius error) 0 0) (cons 1 0))))
 :hints (("Goal"
  :use (lw-circle-interior-count-ratio-data
        (:instance lw-resolvent-coefficients-valid (ratio (lw-circle-interior-count-ratio root radius)) (offset 0)
         (count (lw-resolvent-truncation-count (lw-circle-interior-count-ratio-cap root radius) error)))
        (:instance lw-resolvent-coefficient-nth (ratio (lw-circle-interior-count-ratio root radius)) (offset 0) (index 0)
         (count (lw-resolvent-truncation-count (lw-circle-interior-count-ratio-cap root radius) error)))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-circle-interior-count-term root radius error)) (offset 0) (target 0)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-term lw-resolvent-truncation-count-natural lw-complex-power lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cip-conjugate-difference
 (implies (and (lw-complexp a) (lw-complexp b))
  (equal (lw-complex-sub (lw-complex-conjugate a) (lw-complex-conjugate b))
         (lw-complex-conjugate (lw-complex-sub a b))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-sub lw-complex-conjugate lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cip-term-error
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (lw-complex-norm-square root) (* radius radius))) (rationalp error) (< 0 error)
               (lw-complexp point) (equal (lw-complex-norm-square point) 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-mul (lw-complex-scale radius point) (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) root)))
                   (lw-complex-conjugate (lw-complex-polynomial (lw-circle-interior-count-term root radius error) point 0))) error))
 :hints (("Goal"
  :use (lw-circle-interior-count-ratio-data lw-circle-interior-count-resolvent-identity lw-cip-term-data
        (:instance lw-complex-disk-norm-square (radius 1))
        (:instance lw-resolvent-computed-polynomial-error (ratio (lw-circle-interior-count-ratio root radius)) (radius (lw-circle-interior-count-ratio-cap root radius))
           (count (lw-resolvent-truncation-count (lw-circle-interior-count-ratio-cap root radius) error)))
        (:instance lw-resolvent-value-rational (ratio (lw-circle-interior-count-ratio root radius)))
        (:instance lw-complex-polynomial-rational (coefficients (lw-circle-interior-count-term root radius error)) (offset 0))
        (:instance lw-complex-conjugate-disk
          (point (lw-complex-sub (lw-resolvent-value (lw-circle-interior-count-ratio root radius) point)
                                 (lw-complex-polynomial (lw-circle-interior-count-term root radius error) point 0))) (radius error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-term lw-resolvent-truncation-count-natural lw-cip-conjugate-difference lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(local (defthm lw-cip-half-data
 (implies (and (rationalp error) (< 0 error))
  (and (rationalp (* 1/2 error)) (< 0 (* 1/2 error))
       (equal (+ (* 1/2 error) (* 1/2 error)) error)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))))

(defun lw-circle-interior-count-polynomial (roots radius error)
 (declare (xargs :measure (acl2-count roots)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp roots) nil
   (lw-polynomial-add (lw-circle-interior-count-term (car roots) radius (* 1/2 error)) (lw-circle-interior-count-polynomial (cdr roots) radius (* 1/2 error)))))

(local (defthm lw-cip-empty-coefficient
 (equal (lw-complex-coefficient-at nil 0 0) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficient-at endp lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-cip-length-natural
 (natp (len roots)) :rule-classes (:rewrite :type-prescription)))

(defthm lw-circle-interior-count-polynomial-data
 (implies (and (lw-circle-interior-rootsp roots radius) (rationalp radius) (< 0 radius) (rationalp error) (< 0 error))
  (and (lw-complex-coefficientsp (lw-circle-interior-count-polynomial roots radius error))
       (equal (lw-complex-coefficient-at (lw-circle-interior-count-polynomial roots radius error) 0 0) (cons (len roots) 0))))
 :hints (("Goal" :induct (lw-circle-interior-count-polynomial roots radius error)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-polynomial lw-circle-interior-rootsp lw-cip-term-data lw-polynomial-add-valid lw-polynomial-add-coefficient lw-complex-coefficientsp lw-cip-empty-coefficient lw-cip-half-data lw-cip-length-natural lw-complex-add len endp lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cip-empty-polynomial
 (equal (lw-complex-polynomial nil point 0) (cons 0 0))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-polynomial endp lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-interior-count-polynomial-error
 (implies (and (and (lw-circle-interior-rootsp roots radius) (rationalp radius) (< 0 radius) (rationalp error) (< 0 error)) (lw-complexp point) (equal (lw-complex-norm-square point) 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point)))
    (lw-complex-conjugate (lw-complex-polynomial (lw-circle-interior-count-polynomial roots radius error) point 0))) error))
 :hints (("Goal" :induct (lw-circle-interior-count-polynomial roots radius error)
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-interior-count-polynomial lw-circle-interior-rootsp lw-circle-interior-count-polynomial-data lw-cip-term-data lw-cip-half-data lw-cip-interior-typed lw-polynomial-factor-log-sum lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-complex-reciprocal-rational lw-complex-conjugate-rational lw-complex-scale-rational lw-complex-polynomial-rational lw-complex-mul-zero lw-complex-zero-disk lw-complex-sub-zero lw-polynomial-add-evaluation lw-complex-mul-distribute lw-complex-sub-add lw-complex-conjugate-add lw-cip-empty-polynomial (:executable-counterpart lw-complex-sub) (:executable-counterpart lw-complex-conjugate) (:executable-counterpart lw-complexp) endp lw-cip-left-commutes lw-cip-left-distributes lw-cip-fold-constants lw-cip-times-negative lw-cip-negative-times lw-cip-zero-times lw-cip-minus-one lw-cip-double-negative lw-cip-add-cancel lw-cip-double lw-cip-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-cip-term-error (root (car roots)) (error (* 1/2 error)))
          (:instance lw-complex-add-disk (left (lw-complex-sub (lw-complex-mul (lw-complex-scale radius point) (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) (car roots)))) (lw-complex-conjugate (lw-complex-polynomial (lw-circle-interior-count-term (car roots) radius (* 1/2 error)) point 0)))) (right (lw-complex-sub (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (cdr roots) (lw-complex-scale radius point))) (lw-complex-conjugate (lw-complex-polynomial (lw-circle-interior-count-polynomial (cdr roots) radius (* 1/2 error)) point 0))))
                      (radius (* 1/2 error)) (other-radius (* 1/2 error))))
    :do-not-induct t))))
