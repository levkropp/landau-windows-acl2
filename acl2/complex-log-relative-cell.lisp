(in-package "ACL2")

(include-book "complex-log-unit-increment")
(include-book "signed-log-multiplication")
(include-book "cauchy-polynomials")

; Compare consecutive logarithm samples along t -> 1-t*z by
; factoring their quotient exactly.

(local (defthm lw-clrc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clrc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clrc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clrc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clrc-times-negative (a b) (b a)))
                 :in-theory (disable lw-clrc-times-negative)))))

(local (defthm lw-clrc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clrc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clrc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clrc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clrc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clrc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clrc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clrc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clrc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-log-segment-factor (point time)
  (lw-complex-sub (cons 1 0) (lw-complex-scale time point)))

(defun lw-complex-log-relative-increment (point time step)
  (lw-complex-scale step
    (lw-complex-mul (lw-complex-reciprocal (lw-complex-log-segment-factor point time)) point)))

(local
 (defthm lw-clrc-zero-norm
   (equal (lw-complex-norm-square (cons 0 0)) 0)
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-norm-square
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-clrc-factor-data
   (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                 (rationalp time) (<= 0 time) (<= time 1))
            (and (lw-complexp (lw-complex-log-segment-factor point time))
                 (not (equal (lw-complex-log-segment-factor point time) (cons 0 0)))
                 (rationalp (lw-complex-norm-square (lw-complex-log-segment-factor point time))) (< 0 (lw-complex-norm-square (lw-complex-log-segment-factor point time)))
                 (lw-complex-diskp (lw-complex-reciprocal (lw-complex-log-segment-factor point time)) (/ (- 1 ratio)))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius ratio))
                  (:instance lw-complex-scale-disk (factor time) (radius ratio))
                  (:instance lw-clrc-multiply-order (a time) (b 1) (factor ratio))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale time point)) (radius (* time ratio)) (cap ratio))
                  (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-scale time point)))
                  (:instance lw-complex-scale-rational (factor time))
                  (:instance lw-complex-norm-square-valid (point (lw-complex-log-segment-factor point time)))
                  (:instance lw-complex-one-minus-norm-lower (point (lw-complex-scale time point)) (radius ratio))
                  (:instance lw-clrc-positive-product (a (- 1 ratio)) (b (- 1 ratio)))
                  (:instance lw-complex-resolvent-bound (point (lw-complex-scale time point)) (radius ratio)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-segment-factor lw-clrc-zero-norm abs
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-log-relative-increment-disk
   (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                 (rationalp time) (<= 0 time) (rationalp step) (<= 0 step)
                 (<= (+ time step) 1))
            (lw-complex-diskp (lw-complex-log-relative-increment point time step) (* step ratio (/ (- 1 ratio)))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius ratio)) lw-clrc-factor-data
                  (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (lw-complex-log-segment-factor point time))) (right point)
                    (radius (/ (- 1 ratio))) (other-radius ratio))
                  (:instance lw-complex-scale-disk (point (lw-complex-mul (lw-complex-reciprocal (lw-complex-log-segment-factor point time)) point))
                    (factor step) (radius (* (/ (- 1 ratio)) ratio))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-relative-increment abs
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil)

(local
 (defthm lw-clrc-linear-subtraction
   (implies (and (lw-complexp point) (rationalp time) (rationalp step))
            (equal (lw-complex-sub (lw-complex-log-segment-factor point time) (lw-complex-scale step point))
                   (lw-complex-log-segment-factor point (+ time step))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-segment-factor lw-complexp lw-complex-scale lw-complex-sub
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-clrc-mul-scale-right
   (implies (and (lw-complexp a) (lw-complexp b) (rationalp step))
            (equal (lw-complex-mul a (lw-complex-scale step b))
                   (lw-complex-scale step (lw-complex-mul a b))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-mul
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-clrc-exact-relative-factor
   (implies (and (lw-complexp point) (rationalp time) (rationalp step)
                 (lw-complexp (lw-complex-log-segment-factor point time))
                 (not (equal (lw-complex-log-segment-factor point time) (cons 0 0))))
            (equal (lw-complex-mul (lw-complex-log-segment-factor point time) (lw-complex-sub (cons 1 0) (lw-complex-log-relative-increment point time step))) (lw-complex-log-segment-factor point (+ time step))))
   :hints (("Goal"
            :use ((:instance lw-complex-reciprocal-inverse (point (lw-complex-log-segment-factor point time)))
                  (:instance lw-complex-mul-associative
                    (left (lw-complex-log-segment-factor point time)) (middle (lw-complex-reciprocal (lw-complex-log-segment-factor point time))) (right point))
                  (:instance lw-complex-mul-subtract (a (lw-complex-log-segment-factor point time)) (b (cons 1 0)) (c (lw-complex-log-relative-increment point time step))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-relative-increment lw-clrc-linear-subtraction lw-clrc-mul-scale-right
              lw-complex-reciprocal-rational lw-complex-mul-one lw-complex-ring-rational lw-complex-scale-rational
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-log-relative-cell
  (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                 (rationalp time) (<= 0 time) (rationalp step) (<= 0 step)
                 (<= (+ time step) 1)
                (<= (* step ratio (/ (- 1 ratio))) 1/4) (rationalp error) (< 0 error))
           (<= (abs (+ (- (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-log-segment-factor point (+ time step))) error)) (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-log-segment-factor point time)) error))) (* 2 (car (lw-complex-log-relative-increment point time step)))))
               (+ (* 4 error) (* 19 (* step ratio (/ (- 1 ratio))) (* step ratio (/ (- 1 ratio)))))))
  :hints (("Goal"
           :use ((:instance lw-complex-disk-data (radius ratio))
                 lw-clrc-factor-data (:instance lw-clrc-factor-data (time (+ time step)))
                 lw-complex-log-relative-increment-disk lw-clrc-exact-relative-factor
                 (:instance lw-complex-disk-data (point (lw-complex-log-relative-increment point time step)) (radius (* step ratio (/ (- 1 ratio)))))
                 (:instance lw-complex-ring-rational (left (cons 1 0)) (right (lw-complex-log-relative-increment point time step)))
                 (:instance lw-complex-norm-square-valid (point (lw-complex-sub (cons 1 0) (lw-complex-log-relative-increment point time step))))
                 (:instance lw-complex-norm-square-product (left (lw-complex-log-segment-factor point time)) (right (lw-complex-sub (cons 1 0) (lw-complex-log-relative-increment point time step))))
                 (:instance lw-complex-log-unit-increment (point (lw-complex-log-relative-increment point time step)) (radius (* step ratio (/ (- 1 ratio)))))
                 (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-complex-log-segment-factor point time))))
                 (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-complex-sub (cons 1 0) (lw-complex-log-relative-increment point time step)))))
                 (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-complex-log-segment-factor point (+ time step)))))
                 (:instance lw-signed-log-lower-multiplication
                   (left (lw-complex-norm-square (lw-complex-log-segment-factor point time))) (right (lw-complex-norm-square (lw-complex-sub (cons 1 0) (lw-complex-log-relative-increment point time step))))
                   (left-error error) (right-error error) (product-error error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp lw-complexp abs
              lw-clrc-left-commutes lw-clrc-left-distributes lw-clrc-fold-constants
              lw-clrc-times-negative lw-clrc-negative-times lw-clrc-zero-times
              lw-clrc-minus-one lw-clrc-double-negative lw-clrc-add-cancel lw-clrc-double lw-clrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
