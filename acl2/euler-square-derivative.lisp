(in-package "ACL2")

(include-book "euler-positive-polynomial-stability")
(include-book "euler-uniform-derivative-bounds")
(include-book "polynomial-affine-derivatives")

; A single strict inner disk contains the whole square.

(local (defthm lw-esd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-esd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-esd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-esd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-esd-times-negative (a b) (b a)))
                 :in-theory (disable lw-esd-times-negative)))))

(local (defthm lw-esd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-esd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-esd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-esd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-esd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-esd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-esd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-esd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-esd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-esd-left-commutes)))))

(defun lw-euler-square-inner-radius (anchor side)
 (- (lw-positive-square-center-rate anchor side) (* 3/4 (car anchor))))
(defun lw-euler-square-derivative-request (anchor error)
 (* 2 error (/ (car anchor))))
(defun lw-euler-square-derivative-cap (anchor side)
 (+ 2 (lw-euler-uniform-derivative-cap (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side))))

(local (defthm lw-esd-inner-budget
 (implies (and (rationalp rate) (rationalp real) (< 0 real)
               (rationalp width) (<= 0 width)
               (<= (+ (* real real) (* width width)) (* rate real)))
  (and (<= 0 (- rate (* 3/4 real)))
       (<= (+ (* (- rate real) (- rate real)) (* 1/4 width width))
           (* (- rate (* 3/4 real)) (- rate (* 3/4 real))))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(defthm lw-euler-square-inner-radius-data
 (implies (lw-positive-squarep anchor side)
  (and (rationalp (lw-euler-square-inner-radius anchor side)) (<= 0 (lw-euler-square-inner-radius anchor side)) (< (lw-euler-square-inner-radius anchor side) (lw-positive-square-disk-radius anchor side))
       (equal (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) (* 1/4 (car anchor)))
       (<= (+ (* (- (lw-positive-square-center-rate anchor side) (car anchor)) (- (lw-positive-square-center-rate anchor side) (car anchor))) (* 1/4 side side)) (* (lw-euler-square-inner-radius anchor side) (lw-euler-square-inner-radius anchor side)))))
 :hints (("Goal"
  :use (lw-positive-square-disk-data
        (:instance lw-reciprocal-positive (value (car anchor)))
        (:instance lw-esd-inverse-factor (divisor (car anchor)) (coefficient (* side side)))
        (:instance lw-esd-inner-budget (rate (lw-positive-square-center-rate anchor side)) (real (car anchor)) (width side)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-positive-squarep lw-complexp lw-euler-square-inner-radius lw-positive-square-center-rate lw-positive-square-disk-radius lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-esd-square-interval
 (implies (and (rationalp value) (rationalp cap) (<= 0 cap) (<= (- cap) value) (<= value cap))
  (<= (* value value) (* cap cap)))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(defthm lw-euler-square-offset-in-inner-disk
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point))
  (lw-complex-diskp (lw-positive-square-offset anchor side point) (lw-euler-square-inner-radius anchor side)))
 :hints (("Goal"
  :use (lw-euler-square-inner-radius-data lw-positive-square-disk-data
        (:instance lw-esd-square-interval (value (- (car point) (lw-positive-square-center-rate anchor side))) (cap (- (lw-positive-square-center-rate anchor side) (car anchor))))
        (:instance lw-esd-square-interval (value (- (cdr point) (lw-positive-square-center-height anchor side))) (cap (* 1/2 side)))
        (:instance lw-complex-disk-norm-square (point (lw-positive-square-offset anchor side point)) (radius (lw-euler-square-inner-radius anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-positive-squarep lw-square-containsp lw-positive-square-offset lw-positive-square-center lw-positive-square-center-height lw-complexp lw-complex-sub lw-complex-norm-square lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-square-derivative-request-data
 (implies (and (lw-positive-squarep anchor side) (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-square-derivative-request anchor error)) (< 0 (lw-euler-square-derivative-request anchor error)) (equal (* 1/2 (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) (lw-euler-square-derivative-request anchor error)) (* 1/4 error))
       (implies (<= error (* 1/2 (car anchor))) (<= (lw-euler-square-derivative-request anchor error) 1))))
 :hints (("Goal"
  :use (lw-euler-square-inner-radius-data
        (:instance lw-reciprocal-positive (value (car anchor)))
        (:instance lw-esd-inverse-factor (divisor (car anchor)) (coefficient 1))
        (:instance lw-esd-positive-product (a error) (b (/ (car anchor))))
        (:instance lw-esd-multiply-order (a (* 2 error)) (b (car anchor)) (factor (/ (car anchor)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-positive-squarep lw-complexp lw-euler-square-derivative-request lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)))

(defthm lw-euler-square-polynomial-derivative-identity
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point) (natp target) (rationalp error) (< 0 error)) (equal (lw-complex-polynomial-derivative (lw-euler-positive-square-model anchor side target error) point) (lw-complex-polynomial (lw-euler-uniform-derivative-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side) target (lw-euler-square-derivative-request anchor error)) (lw-positive-square-offset anchor side point) 0)))
 :hints (("Goal"
  :use (lw-positive-square-disk-data lw-euler-square-inner-radius-data lw-euler-square-derivative-request-data
        lw-positive-square-point-data lw-positive-square-coordinate-recovery lw-positive-square-affine-point
        (:instance lw-euler-uniform-polynomial-valid (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (radius (lw-positive-square-disk-radius anchor side)) (error (* 1/4 error)))
        (:instance lw-polynomial-affine-derivative
          (coefficients (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) target (* 1/4 error))) (center (lw-positive-square-translation anchor side)) (slope (cons 1 0)))
        (:instance lw-complex-polynomial-derivative-rational (coefficients (lw-euler-uniform-polynomial (lw-positive-square-center-rate anchor side) (lw-positive-square-center-height anchor side) (lw-positive-square-disk-radius anchor side) target (* 1/4 error))) (point (lw-positive-square-offset anchor side point)))
        (:instance lw-euler-uniform-derivative-polynomial-evaluation
          (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (outer-radius (lw-positive-square-disk-radius anchor side)) (inner-radius (lw-euler-square-inner-radius anchor side))
          (error (lw-euler-square-derivative-request anchor error)) (center (lw-positive-square-offset anchor side point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-positive-square-model lw-complex-mul-one (:executable-counterpart lw-complexp) lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-square-derivative-cap-data
 (implies (lw-positive-squarep anchor side)
  (and (rationalp (lw-euler-square-derivative-cap anchor side)) (< 0 (lw-euler-square-derivative-cap anchor side))))
 :hints (("Goal"
  :use (lw-positive-square-disk-data lw-euler-square-inner-radius-data
        (:instance lw-euler-uniform-derivative-cap-valid (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (outer-radius (lw-positive-square-disk-radius anchor side)) (inner-radius (lw-euler-square-inner-radius anchor side))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-square-derivative-cap lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-model-derivative-bound
 (implies (and (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point) (natp target) (rationalp error) (< 0 error)) (<= error (* 1/2 (car anchor)))) (lw-complex-diskp (lw-complex-polynomial-derivative (lw-euler-positive-square-model anchor side target error) point) (lw-euler-square-derivative-cap anchor side)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-derivative-identity lw-positive-square-disk-data
        lw-euler-square-inner-radius-data lw-euler-square-derivative-request-data lw-euler-square-offset-in-inner-disk
        (:instance lw-complex-euler-uniform-derivative-polynomial-cap
          (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (outer-radius (lw-positive-square-disk-radius anchor side)) (inner-radius (lw-euler-square-inner-radius anchor side))
          (error (lw-euler-square-derivative-request anchor error)) (center (lw-positive-square-offset anchor side point))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-euler-square-derivative-cap lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-square-model-native-derivative-error
 (implies (and (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point) (natp target) (rationalp error) (< 0 error)) (rationalp derivative-error) (< 0 derivative-error))
   (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial-derivative (lw-euler-positive-square-model anchor side target error) point) (lw-complex-euler-local-coefficient-value (car point) (cdr point) (- (lw-positive-square-disk-radius anchor side) (lw-euler-square-inner-radius anchor side)) 1 derivative-error)) (+ (* 1/2 (lw-euler-square-derivative-request anchor error)) derivative-error)))
 :hints (("Goal"
  :use (lw-euler-square-polynomial-derivative-identity lw-positive-square-disk-data
        lw-euler-square-inner-radius-data lw-euler-square-derivative-request-data
        lw-euler-square-offset-in-inner-disk lw-positive-square-point-data lw-positive-square-coordinate-recovery
        (:instance lw-complex-euler-uniform-derivative-local-comparison
          (rate (lw-positive-square-center-rate anchor side)) (height (lw-positive-square-center-height anchor side)) (outer-radius (lw-positive-square-disk-radius anchor side)) (inner-radius (lw-euler-square-inner-radius anchor side))
          (error (lw-euler-square-derivative-request anchor error)) (center (lw-positive-square-offset anchor side point)) (coefficient-error derivative-error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-esd-left-commutes lw-esd-left-distributes lw-esd-fold-constants lw-esd-times-negative lw-esd-negative-times lw-esd-zero-times lw-esd-minus-one lw-esd-double-negative lw-esd-add-cancel lw-esd-double lw-esd-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
