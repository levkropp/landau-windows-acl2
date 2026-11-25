(in-package "ACL2")

(include-book "cauchy-extraction")

; With nonnegative real parts, the sum of the pointwise radii is twice
; the unweighted real sum. The Cauchy weights all have norm at most one.

(local (defthm lw-cnrs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cnrs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cnrs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cnrs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cnrs-times-negative (a b) (b a)))
                 :in-theory (disable lw-cnrs-times-negative)))))

(local (defthm lw-cnrs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cnrs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cnrs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cnrs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cnrs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cnrs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cnrs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cnrs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnrs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-cauchy-nonnegative-real-check (coefficients point samples)
  (declare (xargs :measure (nfix samples)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp samples) t
    (and (<= 0 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)))
         (lw-cauchy-nonnegative-real-check coefficients point (- samples 1)))))

(defun lw-cauchy-real-part-sum (coefficients point target samples)
  (declare (xargs :measure (nfix samples)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp samples) (cons 0 0)
    (lw-complex-add (lw-complex-scale (* 2 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0))) (lw-complex-conjugate (lw-complex-power (lw-complex-power point (- samples 1)) target))) (lw-cauchy-real-part-sum coefficients point target (- samples 1)))))

(local
 (defthm lw-cnrs-unit-weight-zero
   (equal (lw-complex-conjugate (lw-complex-power point 0)) (cons 1 0))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-power lw-complex-conjugate
              lw-cnrs-left-commutes lw-cnrs-left-distributes lw-cnrs-fold-constants
              lw-cnrs-times-negative lw-cnrs-negative-times lw-cnrs-zero-times
              lw-cnrs-minus-one lw-cnrs-double-negative lw-cnrs-add-cancel lw-cnrs-double lw-cnrs-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cnrs-real-part-add
   (implies (and (lw-complexp left) (lw-complexp right))
            (and (rationalp (car left)) (rationalp (car right))
                 (equal (car (lw-complex-add left right)) (+ (car left) (car right)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add
              lw-cnrs-left-commutes lw-cnrs-left-distributes lw-cnrs-fold-constants
              lw-cnrs-times-negative lw-cnrs-negative-times lw-cnrs-zero-times
              lw-cnrs-minus-one lw-cnrs-double-negative lw-cnrs-add-cancel lw-cnrs-double lw-cnrs-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cnrs-real-total-step
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (posp samples))
            (and (equal (car (lw-cauchy-evaluation-sum coefficients point 0 0 samples)) (+ (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)) (car (lw-cauchy-evaluation-sum coefficients point 0 0 (- samples 1)))))
                 (equal (* 2 (car (lw-cauchy-evaluation-sum coefficients point 0 0 samples))) (+ (* 2 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0))) (* 2 (car (lw-cauchy-evaluation-sum coefficients point 0 0 (- samples 1))))))))
   :hints (("Goal"
            :use ((:instance lw-cauchy-evaluation-sum-rational (target 0) (offset 0) (count (- samples 1)))
                  (:instance lw-complex-power-rational (index (- samples 1)))
                  (:instance lw-complex-polynomial-rational (point (lw-complex-power point (- samples 1))) (offset 0))
                  (:instance lw-cnrs-real-part-add (left (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)) (right (lw-cauchy-evaluation-sum coefficients point 0 0 (- samples 1)))))
            :expand ((lw-cauchy-evaluation-sum coefficients point 0 0 samples))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cnrs-unit-weight-zero lw-complex-mul-one
              lw-cnrs-left-commutes lw-cnrs-left-distributes lw-cnrs-fold-constants
              lw-cnrs-times-negative lw-cnrs-negative-times lw-cnrs-zero-times
              lw-cnrs-minus-one lw-cnrs-double-negative lw-cnrs-add-cancel lw-cnrs-double lw-cnrs-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrs-real-total-type
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp samples))
            (rationalp (car (lw-cauchy-evaluation-sum coefficients point 0 0 samples))))
   :hints (("Goal"
            :use ((:instance lw-cauchy-evaluation-sum-rational (target 0) (offset 0) (count samples))
                  (:instance lw-cnrs-real-part-add (left (lw-cauchy-evaluation-sum coefficients point 0 0 samples)) (right (lw-cauchy-evaluation-sum coefficients point 0 0 samples))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cnrs-left-commutes lw-cnrs-left-distributes lw-cnrs-fold-constants
              lw-cnrs-times-negative lw-cnrs-negative-times lw-cnrs-zero-times
              lw-cnrs-minus-one lw-cnrs-double-negative lw-cnrs-add-cancel lw-cnrs-double lw-cnrs-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-cauchy-real-part-sum-bound
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complex-diskp point 1)
                (natp target) (natp samples)
                (lw-cauchy-nonnegative-real-check coefficients point samples))
           (lw-complex-diskp (lw-cauchy-real-part-sum coefficients point target samples) (* 2 (car (lw-cauchy-evaluation-sum coefficients point 0 0 samples)))))
  :hints (("Goal"
           :induct (lw-cauchy-real-part-sum coefficients point target samples)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-cauchy-real-part-sum) lw-cauchy-real-part-sum
              lw-cauchy-nonnegative-real-check abs
              lw-cnrs-left-commutes lw-cnrs-left-distributes lw-cnrs-fold-constants
              lw-cnrs-times-negative lw-cnrs-negative-times lw-cnrs-zero-times
              lw-cnrs-minus-one lw-cnrs-double-negative lw-cnrs-add-cancel lw-cnrs-double lw-cnrs-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-disk-data (radius 1))
                       (:instance lw-complex-zero-disk (radius 0))
                       lw-cnrs-real-total-step
                       (:instance lw-cnrs-real-total-type (samples (- samples 1)))
                       (:instance lw-complex-power-rational (index (- samples 1)))
                       (:instance lw-complex-polynomial-rational (point (lw-complex-power point (- samples 1))) (offset 0))
                       (:instance lw-cnrs-real-part-add (left (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)) (right (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)))
                       (:instance lw-cauchy-unit-weight-bound (index (- samples 1)))
                       (:instance lw-complex-scale-disk
                         (point (lw-complex-conjugate (lw-complex-power (lw-complex-power point (- samples 1)) target))) (factor (* 2 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)))) (radius 1))
                       (:instance lw-complex-add-disk
                         (left (lw-complex-scale (* 2 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0))) (lw-complex-conjugate (lw-complex-power (lw-complex-power point (- samples 1)) target)))) (radius (* 2 (car (lw-complex-polynomial coefficients (lw-complex-power point (- samples 1)) 0)))) (right (lw-cauchy-real-part-sum coefficients point target (- samples 1)))
                         (other-radius (* 2 (car (lw-cauchy-evaluation-sum coefficients point 0 0 (- samples 1)))))))
                 :expand ((lw-cauchy-evaluation-sum coefficients point 0 0 0))
                 :do-not-induct t)))
  :rule-classes nil)
