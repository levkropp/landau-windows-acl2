(in-package "ACL2")

(include-book "rational-monomial-quadrature")
(include-book "polynomial-difference")
(include-book "polynomial-addition")

; Integrate the finite geometric polynomial coefficient by coefficient.

(local (defthm lw-clsc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clsc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clsc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clsc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clsc-times-negative (a b) (b a)))
                 :in-theory (disable lw-clsc-times-negative)))))

(local (defthm lw-clsc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clsc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clsc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clsc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clsc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clsc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clsc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clsc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clsc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-log-series-coefficients (start count)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) nil
    (cons (cons (/ start) 0)
          (lw-complex-log-series-coefficients (+ 1 start) (- count 1)))))

(defun lw-complex-log-grid-coefficients (mesh cells start count)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp count) nil
    (cons (cons (lw-rational-monomial-grid mesh (- start 1) cells) 0)
          (lw-complex-log-grid-coefficients mesh cells (+ 1 start) (- count 1)))))

(defun lw-complex-log-series-polynomial (count)
  (cons (cons 0 0) (lw-complex-log-series-coefficients 1 count)))

(local
 (defthm lw-clsc-reciprocal-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(defthm lw-complex-log-coefficients-data
  (implies (and (posp mesh) (posp start) (natp count))
           (and (lw-complex-coefficientsp (lw-complex-log-grid-coefficients mesh cells start count))
                (lw-complex-coefficientsp (lw-complex-log-series-coefficients start count))
                (equal (len (lw-complex-log-grid-coefficients mesh cells start count)) count)
                (equal (len (lw-complex-log-series-coefficients start count)) count)))
  :hints (("Goal"
           :induct (lw-complex-log-grid-coefficients mesh cells start count)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-grid-coefficients)
              lw-complex-log-grid-coefficients lw-complex-log-series-coefficients
              lw-complex-coefficientsp lw-complexp lw-clsc-reciprocal-type
              len endp
              lw-clsc-left-commutes lw-clsc-left-distributes lw-clsc-fold-constants
              lw-clsc-times-negative lw-clsc-negative-times lw-clsc-zero-times
              lw-clsc-minus-one lw-clsc-double-negative lw-clsc-add-cancel lw-clsc-double lw-clsc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-rational-monomial-grid-rational (degree (- start 1))))
                 :do-not-induct t))))

(local
 (defthm lw-clsc-head-mass
   (implies (and (posp mesh) (posp start))
            (<= (lw-complex-l1 (lw-complex-sub (cons (lw-rational-monomial-grid mesh (- start 1) mesh) 0) (cons (/ start) 0)))
                (/ mesh)))
   :hints (("Goal"
            :use ((:instance lw-rational-monomial-grid-error (degree (- start 1)))
                  (:instance lw-rational-monomial-grid-rational (degree (- start 1)) (cells mesh)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-l1 lw-complex-sub lw-clsc-reciprocal-type abs
              lw-clsc-left-commutes lw-clsc-left-distributes lw-clsc-fold-constants
              lw-clsc-times-negative lw-clsc-negative-times lw-clsc-zero-times
              lw-clsc-minus-one lw-clsc-double-negative lw-clsc-add-cancel lw-clsc-double lw-clsc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clsc-difference-mass
   (implies (and (posp mesh) (posp start) (natp count))
            (<= (lw-complex-coefficient-mass (lw-polynomial-difference (lw-complex-log-grid-coefficients mesh mesh start count) (lw-complex-log-series-coefficients start count))) (* count (/ mesh))))
   :hints (("Goal"
            :induct (lw-complex-log-grid-coefficients mesh mesh start count)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-grid-coefficients)
              lw-complex-log-grid-coefficients lw-complex-log-series-coefficients
              lw-polynomial-difference lw-complex-coefficient-mass endp
              lw-clsc-left-commutes lw-clsc-left-distributes lw-clsc-fold-constants
              lw-clsc-times-negative lw-clsc-negative-times lw-clsc-zero-times
              lw-clsc-minus-one lw-clsc-double-negative lw-clsc-add-cancel lw-clsc-double lw-clsc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-clsc-head-mass (:instance lw-clsc-reciprocal-type (value mesh)))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-complex-log-grid-series-comparison
  (implies (and (posp mesh) (posp start) (natp count) (lw-complex-diskp point 1))
           (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh mesh start count) point start) (lw-complex-polynomial (lw-complex-log-series-coefficients start count) point start))
                             (* count (/ mesh))))
  :hints (("Goal"
           :use ((:instance lw-complex-log-coefficients-data (cells mesh))
                 (:instance lw-complex-disk-data (radius 1))
                 (:instance lw-polynomial-difference-valid (left (lw-complex-log-grid-coefficients mesh mesh start count)) (right (lw-complex-log-series-coefficients start count)))
                 (:instance lw-polynomial-difference-evaluation (left (lw-complex-log-grid-coefficients mesh mesh start count)) (right (lw-complex-log-series-coefficients start count)) (offset start))
                 (:instance lw-complex-polynomial-unit-mass-bound (coefficients (lw-polynomial-difference (lw-complex-log-grid-coefficients mesh mesh start count) (lw-complex-log-series-coefficients start count))) (offset start))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-polynomial-difference (lw-complex-log-grid-coefficients mesh mesh start count) (lw-complex-log-series-coefficients start count)) point start))
                   (radius (lw-complex-coefficient-mass (lw-polynomial-difference (lw-complex-log-grid-coefficients mesh mesh start count) (lw-complex-log-series-coefficients start count)))) (cap (* count (/ mesh))))
                 lw-clsc-difference-mass (:instance lw-clsc-reciprocal-type (value mesh)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clsc-left-commutes lw-clsc-left-distributes lw-clsc-fold-constants
              lw-clsc-times-negative lw-clsc-negative-times lw-clsc-zero-times
              lw-clsc-minus-one lw-clsc-double-negative lw-clsc-add-cancel lw-clsc-double lw-clsc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
