(in-package "ACL2")

(include-book "complex-log-grid-increment")
(include-book "complex-log-path-sum")

; Replace each exact resolvent sample by the corresponding geometric row.

(local (defthm lw-clga-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clga-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clga-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clga-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clga-times-negative (a b) (b a)))
                 :in-theory (disable lw-clga-times-negative)))))

(local (defthm lw-clga-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clga-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clga-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clga-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clga-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clga-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clga-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clga-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clga-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clga-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clga-left-commutes)))))

(local
 (defthm lw-clga-grid-times
   (implies (and (posp mesh) (posp cells) (<= cells mesh))
            (and (rationalp (/ mesh)) (< 0 (/ mesh))
                 (rationalp (* (- cells 1) (/ mesh))) (<= 0 (* (- cells 1) (/ mesh))) (<= (* (- cells 1) (/ mesh)) 1)
                 (<= (* cells (/ mesh)) 1)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value mesh))
                  (:instance inverse-of-* (x mesh))
                  (:instance lw-clga-multiply-order (a (- cells 1)) (b mesh) (factor (/ mesh)))
                  (:instance lw-clga-multiply-order (a cells) (b mesh) (factor (/ mesh)))
                  (:instance lw-clga-multiply-order (a 0) (b (- cells 1)) (factor (/ mesh))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clga-scaled-product-difference
   (implies (and (lw-complexp point) (lw-complexp exact) (lw-complexp approximate)
                 (rationalp step))
            (equal (lw-complex-sub (lw-complex-scale step (lw-complex-mul exact point))
                                   (lw-complex-scale step (lw-complex-mul point approximate)))
                   (lw-complex-scale step (lw-complex-mul (lw-complex-sub exact approximate) point))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-mul lw-complex-sub
              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clga-grid-cell
   (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                 (posp mesh) (posp cells) (<= cells mesh) (natp count))
            (lw-complex-diskp
             (lw-complex-sub (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh))
                             (lw-complex-sub (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh cells 1 count) point 1) (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count) point 1))) (* (/ mesh) ratio (* (/ (- 1 ratio)) (lw-rational-power ratio count)))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius ratio))
                  lw-clga-grid-times lw-complex-log-grid-increment
                  (:instance lw-clga-multiply-order (a (* (- cells 1) (/ mesh))) (b 1) (factor ratio))
                  (:instance lw-complex-scale-disk (factor (* (- cells 1) (/ mesh))) (radius ratio))
                  (:instance lw-complex-scale-rational (factor (* (- cells 1) (/ mesh))))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale (* (- cells 1) (/ mesh)) point)) (radius (* (* (- cells 1) (/ mesh)) ratio)) (cap ratio))
                  (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-scale (* (- cells 1) (/ mesh)) point)))
                  (:instance lw-complex-reciprocal-rational (point (lw-complex-log-segment-factor point (* (- cells 1) (/ mesh)))))
                  (:instance lw-complex-geometric-sum-rational (point (lw-complex-scale (* (- cells 1) (/ mesh)) point)))
                  (:instance lw-complex-geometric-remainder-bound (point (lw-complex-scale (* (- cells 1) (/ mesh)) point)) (radius ratio))
                  (:instance lw-complex-mul-disk (left (lw-complex-sub (lw-complex-reciprocal (lw-complex-log-segment-factor point (* (- cells 1) (/ mesh)))) (lw-complex-geometric-sum (lw-complex-scale (* (- cells 1) (/ mesh)) point) count))) (right point) (radius (* (/ (- 1 ratio)) (lw-rational-power ratio count))) (other-radius ratio))
                  (:instance lw-complex-scale-disk (point (lw-complex-mul (lw-complex-sub (lw-complex-reciprocal (lw-complex-log-segment-factor point (* (- cells 1) (/ mesh)))) (lw-complex-geometric-sum (lw-complex-scale (* (- cells 1) (/ mesh)) point) count)) point)) (factor (/ mesh)) (radius (* ratio (* (/ (- 1 ratio)) (lw-rational-power ratio count)))))
                  (:instance lw-clga-scaled-product-difference (exact (lw-complex-reciprocal (lw-complex-log-segment-factor point (* (- cells 1) (/ mesh))))) (approximate (lw-complex-geometric-sum (lw-complex-scale (* (- cells 1) (/ mesh)) point) count)) (step (/ mesh))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-relative-increment lw-complex-log-segment-factor abs
              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clga-zero-grid
   (implies (and (posp mesh) (posp start) (natp count) (lw-complexp point))
            (equal (lw-complex-polynomial
                    (lw-complex-log-grid-coefficients mesh 0 start count) point start)
                   (cons 0 0)))
   :hints (("Goal"
            :induct (lw-complex-log-grid-coefficients mesh 0 start count)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-grid-coefficients)
              lw-complex-log-grid-coefficients lw-rational-monomial-grid
              lw-complex-polynomial lw-complex-power-rational
              lw-complex-mul-zero lw-complex-add-zero endp
              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize)))))

(local
 (defthm lw-clga-path-scalar-step
   (implies (and (rationalp current) (rationalp previous) (rationalp relative)
                 (rationalp path) (rationalp cap) (posp cells)
                 (<= (abs (- relative (- current previous))) cap)
                 (<= (abs (- path previous)) (* (- cells 1) cap)))
            (<= (abs (- (+ relative path) current)) (* cells cap)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clga-real-data
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
            (and (rationalp (car a)) (rationalp (car b)) (rationalp (car c))
                 (equal (car (lw-complex-sub a (lw-complex-sub b c)))
                        (- (car a) (- (car b) (car c))))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub
              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clga-reciprocal-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(defthm lw-complex-log-grid-path-comparison
  (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                (posp mesh) (natp cells) (<= cells mesh) (natp count))
           (<= (abs (- (lw-complex-log-path-sum point mesh cells) (car (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh cells 1 count) point 1))))
               (* cells (* (/ mesh) ratio (* (/ (- 1 ratio)) (lw-rational-power ratio count))))))
  :hints (("Goal"
           :induct (lw-complex-log-path-sum point mesh cells)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-path-sum) lw-complex-log-path-sum
              lw-clga-zero-grid car-cons (:executable-counterpart abs)
              lw-clga-left-commutes lw-clga-left-distributes lw-clga-fold-constants
              lw-clga-times-negative lw-clga-negative-times lw-clga-zero-times
              lw-clga-minus-one lw-clga-double-negative lw-clga-add-cancel lw-clga-double lw-clga-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-disk-data (radius ratio))
                       lw-clga-grid-times lw-clga-grid-cell
                       (:instance lw-complex-log-relative-increment-disk
                         (time (* (- cells 1) (/ mesh))) (step (/ mesh)))
                       (:instance lw-complex-disk-data
                         (point (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh)))
                         (radius (* (/ mesh) ratio (/ (- 1 ratio)))))
                       (:instance lw-complex-log-path-sum-rational (cells (- cells 1)))
                       (:instance lw-rational-power-rational (base ratio) (exponent count))
                       (:instance lw-clga-reciprocal-type (value (- 1 ratio)))
                       (:instance lw-complex-disk-coordinates
                         (point (lw-complex-sub (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh)) (lw-complex-sub (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh cells 1 count) point 1) (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count) point 1))))
                         (radius (* (/ mesh) ratio (* (/ (- 1 ratio)) (lw-rational-power ratio count)))))
                       (:instance lw-complex-log-coefficients-data (start 1))
                       (:instance lw-complex-log-coefficients-data (start 1) (cells (- cells 1)))
                       (:instance lw-complex-polynomial-rational (coefficients (lw-complex-log-grid-coefficients mesh cells 1 count)) (offset 1))
                       (:instance lw-complex-polynomial-rational (coefficients (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count)) (offset 1))
                       (:instance lw-clga-real-data (a (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh))) (b (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh cells 1 count) point 1)) (c (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count) point 1)))
                       (:instance lw-clga-path-scalar-step (current (car (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh cells 1 count) point 1))) (previous (car (lw-complex-polynomial (lw-complex-log-grid-coefficients mesh (- cells 1) 1 count) point 1))) (relative (car (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh))))
                         (path (lw-complex-log-path-sum point mesh (- cells 1))) (cap (* (/ mesh) ratio (* (/ (- 1 ratio)) (lw-rational-power ratio count))))))
                 :do-not-induct t)))
  :rule-classes nil)
