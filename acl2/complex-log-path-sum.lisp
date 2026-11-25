(in-package "ACL2")

(include-book "complex-log-relative-cell")

; Sum the relative increments along a uniform rational subdivision.

(local (defthm lw-clps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clps-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clps-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clps-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clps-times-negative (a b) (b a)))
                 :in-theory (disable lw-clps-times-negative)))))

(local (defthm lw-clps-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clps-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clps-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clps-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clps-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clps-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clps-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clps-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clps-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clps-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clps-left-commutes)))))

(defun lw-complex-log-path-sum (point mesh cells)
  (declare (xargs :measure (nfix cells)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp cells)
      0
    (+ (car (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh))) (lw-complex-log-path-sum point mesh (- cells 1)))))

(local
 (defthm lw-clps-real-part-type
   (implies (lw-complexp point) (rationalp (car point)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-clps-signed-log-one
   (equal (car (lw-signed-log-bounds 1 error)) 0)
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-signed-log-bounds
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-clps-reciprocal-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(local
 (defthm lw-clps-relative-real-rational
   (implies (and (lw-complexp point) (rationalp time) (rationalp step))
            (rationalp (car (lw-complex-log-relative-increment point time step))))
   :hints (("Goal"
            :use ((:instance lw-complex-operations-rational (left point) (right point) (factor time))
                  (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-scale time point)))
                  (:instance lw-complex-reciprocal-rational (point (lw-complex-log-segment-factor point time)))
                  (:instance lw-complex-operations-rational
                    (left (lw-complex-reciprocal (lw-complex-log-segment-factor point time))) (right point) (factor step))
                  (:instance lw-complex-scale-rational
                    (point (lw-complex-mul (lw-complex-reciprocal (lw-complex-log-segment-factor point time)) point)) (factor step))
                  (:instance lw-clps-real-part-type (point (lw-complex-log-relative-increment point time step))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-segment-factor lw-complex-log-relative-increment
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-log-path-sum-rational
   (implies (and (lw-complexp point) (posp mesh) (natp cells))
            (rationalp (lw-complex-log-path-sum point mesh cells)))
   :hints (("Goal" :induct (lw-complex-log-path-sum point mesh cells)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-path-sum) lw-complex-log-path-sum
              lw-clps-reciprocal-type
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-clps-reciprocal-type (value mesh))
                        (:instance lw-clps-relative-real-rational
                          (time (* (- cells 1) (/ mesh))) (step (/ mesh))))
                  :do-not-induct t))))

(local
 (defthm lw-clps-start-norm
   (implies (lw-complexp point)
            (equal (lw-complex-norm-square (lw-complex-log-segment-factor point 0)) 1))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-segment-factor lw-complex-scale lw-complex-sub lw-complex-norm-square lw-complexp
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-clps-mesh-data
   (implies (and (posp mesh) (posp cells) (<= cells mesh))
            (and (rationalp (/ mesh)) (< 0 (/ mesh))
                 (rationalp (* cells (/ mesh))) (rationalp (* (- cells 1) (/ mesh)))
                 (<= 0 (* (- cells 1) (/ mesh))) (<= (* cells (/ mesh)) 1)
                 (equal (+ (* (- cells 1) (/ mesh)) (/ mesh)) (* cells (/ mesh)))))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value mesh))
                  (:instance inverse-of-* (x mesh))
                  (:instance lw-clps-multiply-order (a cells) (b mesh) (factor (/ mesh)))
                  (:instance lw-clps-multiply-order (a 0) (b (- cells 1)) (factor (/ mesh))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clps-add-cell-budget
   (implies (and (rationalp upper) (rationalp lower) (rationalp cell)
                 (rationalp previous) (rationalp cost) (posp cells)
                 (<= (abs (+ (- upper lower) (* 2 cell))) cost)
                 (<= (abs (+ lower (* 2 previous))) (* (- cells 1) cost)))
            (<= (abs (+ upper (* 2 (+ cell previous)))) (* cells cost)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clps-path-value-rational
   (implies (and (lw-complex-diskp point ratio) (< ratio 1) (rationalp time)
                 (<= 0 time) (<= time 1) (rationalp error) (< 0 error))
            (rationalp (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-log-segment-factor point time)) error))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius ratio))
                  (:instance lw-complex-scale-rational (factor time))
                  (:instance lw-clps-multiply-order (a time) (b 1) (factor ratio))
                  (:instance lw-complex-scale-disk (factor time) (radius ratio))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale time point))
                    (radius (* time ratio)) (cap ratio))
                  (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-scale time point)))
                  (:instance lw-complex-norm-square-valid (point (lw-complex-scale time point)))
                  (:instance lw-complex-norm-square-valid (point (lw-complex-log-segment-factor point time)))
                  (:instance lw-complex-one-minus-norm-lower (point (lw-complex-scale time point)) (radius ratio))
                  (:instance lw-clps-positive-product (a (- 1 ratio)) (b (- 1 ratio)))
                  (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-complex-log-segment-factor point time)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-segment-factor lw-intervalp abs
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-log-path-sum-bound
  (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                (posp mesh) (natp cells) (<= cells mesh)
                (<= (* (/ mesh) ratio (/ (- 1 ratio))) 1/4) (rationalp error) (< 0 error))
           (<= (abs (+ (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-log-segment-factor point (* cells (/ mesh)))) error)) (* 2 (lw-complex-log-path-sum point mesh cells))))
               (* cells (+ (* 4 error) (* 19 (* (/ mesh) ratio (/ (- 1 ratio))) (* (/ mesh) ratio (/ (- 1 ratio))))))))
  :hints (("Goal"
           :induct (lw-complex-log-path-sum point mesh cells)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-complex-log-path-sum) lw-complex-log-path-sum
              lw-clps-signed-log-one lw-clps-start-norm (:executable-counterpart abs)
              lw-clps-left-commutes lw-clps-left-distributes lw-clps-fold-constants
              lw-clps-times-negative lw-clps-negative-times lw-clps-zero-times
              lw-clps-minus-one lw-clps-double-negative lw-clps-add-cancel lw-clps-double lw-clps-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-clps-mesh-data
                       (:instance lw-complex-disk-data (radius ratio))
                       (:instance lw-clps-reciprocal-type (value (- 1 ratio)))
                       (:instance lw-clps-relative-real-rational
                         (time (* (- cells 1) (/ mesh))) (step (/ mesh)))
                       (:instance lw-complex-log-path-sum-rational (cells (- cells 1)))
                       (:instance lw-complex-log-relative-cell (time (* (- cells 1) (/ mesh))) (step (/ mesh)))
                       (:instance lw-clps-path-value-rational (time (* (- cells 1) (/ mesh))))
                       (:instance lw-clps-path-value-rational (time (* cells (/ mesh))))
                       (:instance lw-clps-add-cell-budget
                         (upper (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-log-segment-factor point (* cells (/ mesh)))) error))) (lower (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-log-segment-factor point (* (- cells 1) (/ mesh)))) error)))
                         (cell (car (lw-complex-log-relative-increment point (* (- cells 1) (/ mesh)) (/ mesh)))) (previous (lw-complex-log-path-sum point mesh (- cells 1))) (cost (+ (* 4 error) (* 19 (* (/ mesh) ratio (/ (- 1 ratio))) (* (/ mesh) ratio (/ (- 1 ratio))))))))
                 :do-not-induct t)))
  :rule-classes nil)
