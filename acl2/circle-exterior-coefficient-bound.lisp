(in-package "ACL2")

(include-book "circle-exterior-coefficient-model")
(include-book "polynomial-cauchy-caps")
(include-book "polynomial-capped-coefficients")

; A sampled bound on the exterior part controls its exact coefficient.

(local (defthm lw-ceb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ceb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ceb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ceb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ceb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ceb-times-negative)))))

(local (defthm lw-ceb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ceb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ceb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ceb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ceb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ceb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ceb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ceb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ceb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ceb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ceb-left-commutes)))))

(local (defthm lw-ceb-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(defun lw-circle-exterior-sample-check (roots radius rotation count bound)
 (declare (xargs :measure (nfix count)
                 :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (zp count)
     t
   (and (lw-complex-diskp
         (lw-polynomial-factor-log-sum roots (lw-complex-scale radius (lw-complex-power rotation (- count 1)))) bound)
        (lw-circle-exterior-sample-check roots radius rotation (- count 1) bound))))

(defun lw-circle-exterior-coefficient-sample-count (roots radius target error bound)
 (let* ((model (lw-circle-exterior-polynomial roots radius target error))
        (degree (len model)))
  (lw-cauchy-coefficient-count model degree (lw-polynomial-cap-test-error model (+ bound error)))))

(defun lw-circle-exterior-coefficient-check (roots radius target error bound)
 (let ((degree (len (lw-circle-exterior-polynomial roots radius target error))))
  (lw-circle-exterior-sample-check roots radius (lw-cauchy-orbit-rotation degree)
   (lw-circle-exterior-coefficient-sample-count roots radius target error bound) bound)))

(defthm lw-circle-exterior-coefficient-sample-count-data
 (implies (and (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error)) (rationalp bound) (<= 0 bound))
  (natp (lw-circle-exterior-coefficient-sample-count roots radius target error bound)))
 :hints (("Goal"
  :use (lw-circle-exterior-polynomial-valid
        (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-circle-exterior-polynomial roots radius target error)) (cap (+ bound error))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-coefficient-sample-count lw-ceb-sum-rational lw-ceb-left-commutes lw-ceb-left-distributes lw-ceb-fold-constants lw-ceb-times-negative lw-ceb-negative-times lw-ceb-zero-times lw-ceb-minus-one lw-ceb-double-negative lw-ceb-add-cancel lw-ceb-double lw-ceb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-ceb-sample-value-bound
 (implies (and (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error)) (lw-complex-diskp point 1) (rationalp bound) (<= 0 bound)
               (lw-complex-diskp (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point)) bound))
  (lw-complex-diskp (lw-complex-polynomial (lw-circle-exterior-polynomial roots radius target error) point 0) (+ bound error)))
 :hints (("Goal"
  :use (lw-circle-exterior-polynomial-valid lw-circle-exterior-polynomial-error
        (:instance lw-complex-disk-data (radius 1))
        (:instance lw-complex-polynomial-rational (coefficients (lw-circle-exterior-polynomial roots radius target error)) (offset 0))
        (:instance lw-complex-disk-data
         (point (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point))) (radius bound))
        (:instance lw-complex-difference-symmetric
         (left (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point)))
         (right (lw-complex-polynomial (lw-circle-exterior-polynomial roots radius target error) point 0)) (radius error))
        (:instance lw-complex-difference-triangle
         (left (lw-complex-polynomial (lw-circle-exterior-polynomial roots radius target error) point 0))
         (middle (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point))) (right (cons 0 0))
         (radius error) (other-radius bound)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-ceb-left-commutes lw-ceb-left-distributes lw-ceb-fold-constants lw-ceb-times-negative lw-ceb-negative-times lw-ceb-zero-times lw-ceb-minus-one lw-ceb-double-negative lw-ceb-add-cancel lw-ceb-double lw-ceb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))

(local (defthm lw-ceb-generated-polynomial-check
 (implies (and (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error)) (lw-complex-diskp rotation 1) (natp count) (rationalp bound) (<= 0 bound)
               (lw-circle-exterior-sample-check roots radius rotation count bound))
  (lw-cauchy-boundary-check (lw-circle-exterior-polynomial roots radius target error) rotation 0 count (+ bound error)))
 :hints (("Goal" :induct (lw-circle-exterior-sample-check roots radius rotation count bound)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-sample-check lw-cauchy-boundary-check lw-ceb-left-commutes lw-ceb-left-distributes lw-ceb-fold-constants lw-ceb-times-negative lw-ceb-negative-times lw-ceb-zero-times lw-ceb-minus-one lw-ceb-double-negative lw-ceb-add-cancel lw-ceb-double lw-ceb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
          :do-not '(generalize fertilize))
 (and stable-under-simplificationp
  '(:use ((:instance lw-complex-power-disk (point rotation) (radius 1) (index (- count 1)))
          (:instance lw-ceb-sample-value-bound (point (lw-complex-power rotation (- count 1)))))
    :in-theory (union-theories
 '(fold-consts-in-+ lw-rational-power-one lw-ceb-left-commutes lw-ceb-left-distributes lw-ceb-fold-constants lw-ceb-times-negative lw-ceb-negative-times lw-ceb-zero-times lw-ceb-minus-one lw-ceb-double-negative lw-ceb-add-cancel lw-ceb-double lw-ceb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
    :do-not-induct t)))))

(defthm lw-circle-exterior-coefficient-check-sound
 (implies (and (and (lw-circle-exterior-rootsp roots radius) (rationalp radius) (< 0 radius) (natp target) (rationalp error) (< 0 error)) (rationalp bound) (<= 0 bound) (lw-circle-exterior-coefficient-check roots radius target error bound))
  (lw-complex-diskp (lw-circle-exterior-coefficient roots radius target) (+ bound error)))
 :hints (("Goal"
  :use (lw-circle-exterior-polynomial-valid lw-circle-exterior-polynomial-coefficient
        (:instance lw-polynomial-cauchy-cap-data (coefficients (lw-circle-exterior-polynomial roots radius target error)) (cap (+ bound error)))
        (:instance lw-cauchy-orbit-data (degree (len (lw-circle-exterior-polynomial roots radius target error))))
        (:instance lw-ceb-generated-polynomial-check (rotation (lw-cauchy-orbit-rotation (len (lw-circle-exterior-polynomial roots radius target error)))) (count (lw-cauchy-coefficient-count (lw-circle-exterior-polynomial roots radius target error) (len (lw-circle-exterior-polynomial roots radius target error)) (lw-polynomial-cap-test-error (lw-circle-exterior-polynomial roots radius target error) (+ bound error)))))
        (:instance lw-polynomial-cauchy-cap-check-sound (coefficients (lw-circle-exterior-polynomial roots radius target error)) (cap (+ bound error)))
        (:instance lw-polynomial-capped-coefficient-at (coefficients (lw-circle-exterior-polynomial roots radius target error)) (cap (+ bound error)) (offset 0)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-coefficient-check lw-circle-exterior-coefficient-sample-count lw-polynomial-cauchy-cap-check lw-ceb-sum-rational lw-ceb-left-commutes lw-ceb-left-distributes lw-ceb-fold-constants lw-ceb-times-negative lw-ceb-negative-times lw-ceb-zero-times lw-ceb-minus-one lw-ceb-double-negative lw-ceb-add-cancel lw-ceb-double lw-ceb-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
