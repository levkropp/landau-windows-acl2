(in-package "ACL2")

(include-book "complex-log-series-coefficients")
(include-book "polynomial-coefficient-maps")
(include-book "polynomial-divided-difference")

; The change in the quadrature coefficient table is one geometric row.

(local (defthm lw-clgi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clgi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clgi-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clgi-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clgi-times-negative (a b) (b a)))
                 :in-theory (disable lw-clgi-times-negative)))))

(local (defthm lw-clgi-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clgi-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clgi-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clgi-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clgi-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clgi-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clgi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clgi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clgi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-log-constant-coefficients (value count)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) nil
    (cons (cons value 0) (lw-complex-log-constant-coefficients value (- count 1)))))

(local
 (defthm lw-clgi-constant-coefficients-valid
   (implies (and (rationalp value) (natp count))
            (lw-complex-coefficientsp (lw-complex-log-constant-coefficients value count)))
   :hints (("Goal"
            :induct (lw-complex-log-constant-coefficients value count)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-constant-coefficients)
              lw-complex-log-constant-coefficients lw-complex-coefficientsp lw-complexp endp
              lw-clgi-left-commutes lw-clgi-left-distributes lw-clgi-fold-constants
              lw-clgi-times-negative lw-clgi-negative-times lw-clgi-zero-times
              lw-clgi-minus-one lw-clgi-double-negative lw-clgi-add-cancel lw-clgi-double lw-clgi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize)))))

(local
 (defthm lw-clgi-reciprocal-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(local
 (defthm lw-clgi-head-identity
   (implies (and (posp mesh) (posp cells) (posp start))
            (equal (lw-complex-sub (cons (lw-rational-monomial-grid mesh (- start 1) cells) 0) (cons (lw-rational-monomial-grid mesh (- start 1) (- cells 1)) 0))
                   (lw-complex-scale (lw-rational-power (* (- cells 1) (/ mesh)) (- start 1)) (cons (/ mesh) 0))))
   :hints (("Goal"
            :use ((:instance lw-rational-monomial-grid-rational (degree (- start 1)) (cells (- cells 1))))
            :expand ((lw-rational-monomial-grid mesh (- start 1) cells))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-sub lw-complex-scale lw-rational-power-rational lw-clgi-reciprocal-type
              lw-clgi-left-commutes lw-clgi-left-distributes lw-clgi-fold-constants
              lw-clgi-times-negative lw-clgi-negative-times lw-clgi-zero-times
              lw-clgi-minus-one lw-clgi-double-negative lw-clgi-add-cancel lw-clgi-double lw-clgi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clgi-grid-row-data
   (implies (and (posp mesh) (posp cells) (posp start) (natp count))
            (equal (lw-polynomial-difference (lw-complex-log-grid-coefficients mesh cells start count) (lw-complex-log-grid-coefficients mesh (- cells 1) start count)) (lw-polynomial-rescale (lw-complex-log-constant-coefficients (/ mesh) count) (* (- cells 1) (/ mesh)) (- start 1))))
   :hints (("Goal"
            :induct (lw-complex-log-grid-coefficients mesh cells start count)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-grid-coefficients) lw-complex-log-grid-coefficients
              lw-complex-log-constant-coefficients lw-polynomial-difference lw-polynomial-rescale endp
              lw-clgi-left-commutes lw-clgi-left-distributes lw-clgi-fold-constants
              lw-clgi-times-negative lw-clgi-negative-times lw-clgi-zero-times
              lw-clgi-minus-one lw-clgi-double-negative lw-clgi-add-cancel lw-clgi-double lw-clgi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-clgi-head-identity
                        (:instance lw-clgi-reciprocal-type (value mesh)))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-clgi-scale-identity
   (implies (and (lw-complexp point) (lw-complexp other) (rationalp value))
            (and (equal (lw-complex-mul point (lw-complex-scale value other))
                        (lw-complex-scale value (lw-complex-mul point other)))
                 (equal (lw-complex-scale value (cons 1 0)) (cons value 0))
                 (equal (lw-complex-scale value (cons 0 0)) (cons 0 0))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-mul
              lw-clgi-left-commutes lw-clgi-left-distributes lw-clgi-fold-constants
              lw-clgi-times-negative lw-clgi-negative-times lw-clgi-zero-times
              lw-clgi-minus-one lw-clgi-double-negative lw-clgi-add-cancel lw-clgi-double lw-clgi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-clgi-real-complexp
   (implies (rationalp value) (lw-complexp (cons value 0)))
   :hints (("Goal" :in-theory (enable lw-complexp)))))

(local
 (defthm lw-clgi-geometric-row-evaluation
   (implies (and (lw-complexp point) (rationalp value) (natp count))
            (equal (lw-complex-polynomial (lw-complex-log-constant-coefficients value count) point 0)
                   (lw-complex-scale value (lw-complex-geometric-sum point count))))
   :hints (("Goal"
            :induct (lw-complex-log-constant-coefficients value count)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-constant-coefficients)
              lw-complex-log-constant-coefficients lw-complex-geometric-sum
              lw-clgi-constant-coefficients-valid lw-clgi-scale-identity
              lw-complex-coefficientsp lw-clgi-real-complexp lw-complex-scale-add lw-complex-geometric-sum-rational
              lw-complex-ring-rational endp
              lw-clgi-left-commutes lw-clgi-left-distributes lw-clgi-fold-constants
              lw-clgi-times-negative lw-clgi-negative-times lw-clgi-zero-times
              lw-clgi-minus-one lw-clgi-double-negative lw-clgi-add-cancel lw-clgi-double lw-clgi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-polynomial-horner
                          (coefficients (cons (cons value 0) (lw-complex-log-constant-coefficients value (- count 1)))))
                        (:instance lw-clgi-constant-coefficients-valid (count (- count 1))))
                  :expand ((lw-complex-polynomial nil point 0))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-complex-log-grid-increment
  (implies (and (lw-complexp point) (posp mesh) (posp cells) (natp count))
           (equal (lw-complex-sub
                   (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh cells 1 count) point 1)
                   (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count) point 1))
                  (lw-complex-scale (/ mesh)
                   (lw-complex-mul point
                    (lw-complex-geometric-sum (lw-complex-scale (* (- cells 1) (/ mesh)) point) count)))))
  :hints (("Goal"
           :use ((:instance lw-complex-log-coefficients-data (start 1))
                 (:instance lw-complex-log-coefficients-data (start 1) (cells (- cells 1)))
                 (:instance lw-polynomial-difference-evaluation
                   (left (lw-complex-log-grid-coefficients mesh cells 1 count))
                   (right (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count)) (offset 1))
                 (:instance lw-clgi-grid-row-data (start 1))
                 (:instance lw-clgi-reciprocal-type (value mesh))
                 (:instance lw-clgi-constant-coefficients-valid (value (/ mesh)))
                 (:instance lw-polynomial-rescale-valid (coefficients (lw-complex-log-constant-coefficients (/ mesh) count)) (factor (* (- cells 1) (/ mesh))) (offset 0))
                 (:instance lw-complex-polynomial-offset-step
                   (coefficients (lw-polynomial-rescale (lw-complex-log-constant-coefficients (/ mesh) count) (* (- cells 1) (/ mesh)) 0)) (offset 0))
                 (:instance lw-polynomial-rescale-evaluation (coefficients (lw-complex-log-constant-coefficients (/ mesh) count)) (factor (* (- cells 1) (/ mesh))) (offset 0))
                 (:instance lw-complex-scale-rational (factor (* (- cells 1) (/ mesh))))
                 (:instance lw-clgi-geometric-row-evaluation (point (lw-complex-scale (* (- cells 1) (/ mesh)) point)) (value (/ mesh))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-clgi-scale-identity lw-complex-geometric-sum-rational
              lw-clgi-left-commutes lw-clgi-left-distributes lw-clgi-fold-constants
              lw-clgi-times-negative lw-clgi-negative-times lw-clgi-zero-times
              lw-clgi-minus-one lw-clgi-double-negative lw-clgi-add-cancel lw-clgi-double lw-clgi-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
