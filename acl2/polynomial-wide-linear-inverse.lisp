(in-package "ACL2")

(include-book "circle-exterior-pole-polynomial")
(include-book "polynomial-coefficient-maps")
(include-book "complex-exp")

(defun lw-polynomial-wide-linear-inverse (rate radius target error)
  (lw-polynomial-rescale
   (lw-circle-exterior-pole-polynomial (cons (- rate) 0) radius target error) (/ (- radius)) 0))

(local (defthm lw-pwli-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pwli-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pwli-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pwli-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pwli-times-negative (a b) (b a)))
                 :in-theory (disable lw-pwli-times-negative)))))

(local (defthm lw-pwli-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pwli-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pwli-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pwli-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pwli-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pwli-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pwli-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pwli-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pwli-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pwli-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pwli-left-commutes)))))

(local
 (defthm lw-pwli-square-order
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-pwli-multiply-order (factor a))
                  (:instance lw-pwli-multiply-order (factor b)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-pwli-square-nonnegative
   (implies (rationalp value) (<= 0 (* value value)))
   :hints (("Goal" :cases ((< value 0))
                   :use ((:instance lw-pwli-multiply-order (a 0) (b value) (factor value))
                         (:instance lw-pwli-multiply-order (a 0) (b (- value)) (factor (- value))))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-pwli-denominator-gap
   (implies (and (rationalp rate) (rationalp radius) (< 0 radius) (< radius rate)
                (lw-complex-diskp point radius))
            (<= (* (- rate radius) (- rate radius))
                (lw-complex-norm-square (lw-complex-sub (cons rate 0) point))))
   :hints (("Goal"
            :use (lw-complex-disk-data lw-complex-disk-coordinates
                  (:instance lw-pwli-square-order (a (- rate radius)) (b (- rate (car point))))
                  (:instance lw-pwli-square-nonnegative (value (cdr point))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-norm-square lw-complexp lw-complex-sub abs
              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-pwli-scale-opposite
   (implies (and (rationalp radius) (< 0 radius))
            (equal (* radius (/ (- radius))) -1))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x (- radius))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive
              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-pwli-reflected-shift
   (implies (and (rationalp rate) (lw-complexp point))
            (and (equal (lw-complex-sub (lw-complex-scale -1 point) (cons (- rate) 0))
                        (lw-complex-sub (cons rate 0) point))
                 (lw-complexp (lw-complex-sub (cons rate 0) point))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub lw-complex-scale
              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-pwli-disc-geometry
   (implies (and (rationalp rate) (rationalp radius) (< 0 radius) (< radius rate)
                (lw-complex-diskp point radius))
            (and (lw-complexp (cons (- rate) 0))
                 (< (* radius radius) (lw-complex-norm-square (cons (- rate) 0)))
                 (lw-complex-diskp (lw-complex-scale (/ (- radius)) point) 1)
                 (equal (lw-complex-sub (lw-complex-scale radius (lw-complex-scale (/ (- radius)) point)) (cons (- rate) 0)) (lw-complex-sub (cons rate 0) point))
                 (lw-complexp (lw-complex-sub (cons rate 0) point))))
   :hints (("Goal"
            :use (lw-complex-disk-data
                  (:instance lw-complex-scale-disk (factor (/ (- radius))))
                  (:instance lw-complex-scale-compose (left radius) (right (/ (- radius))))
                  lw-pwli-scale-opposite lw-pwli-reflected-shift
                  (:instance lw-pwli-square-order (a radius) (b rate))
                  (:instance lw-pwli-multiply-order (a radius) (b rate) (factor rate))
                  (:instance lw-pwli-positive-product (a rate) (b (- rate radius)))
                  (:instance lw-pwli-positive-product (a radius) (b (- rate radius))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              abs lw-reciprocal-positive
              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; Approximate 1/(rate-z) on any strict inner disk, including radii
; arbitrarily close to rate. The polynomial has a computed tail request.
(defthm lw-polynomial-wide-linear-inverse-data
  (implies (and (rationalp rate) (rationalp radius) (< 0 radius) (< radius rate)
                (lw-complex-diskp point radius)
                (natp target) (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-polynomial-wide-linear-inverse rate radius target error))
                (lw-complex-diskp (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (cons rate 0) point)) (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate radius target error) point 0)) error)
                (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate radius target error) point 0) (+ (/ (- rate radius)) error))))
  :hints (("Goal"
           :use (lw-pwli-disc-geometry lw-pwli-denominator-gap
                 (:instance lw-circle-exterior-pole-polynomial-valid (root (cons (- rate) 0)))
                 (:instance lw-circle-exterior-pole-polynomial-error (root (cons (- rate) 0)) (point (lw-complex-scale (/ (- radius)) point)))
                 (:instance lw-polynomial-rescale-valid (coefficients (lw-circle-exterior-pole-polynomial (cons (- rate) 0) radius target error)) (factor (/ (- radius))) (offset 0))
                 (:instance lw-polynomial-rescale-evaluation (coefficients (lw-circle-exterior-pole-polynomial (cons (- rate) 0) radius target error)) (factor (/ (- radius))) (offset 0))
                 (:instance lw-complex-disk-data (radius radius))
                 (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-sub (cons rate 0) point)) (lower (- rate radius)))
                 (:instance lw-complex-reciprocal-rational (point (lw-complex-sub (cons rate 0) point)))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-wide-linear-inverse rate radius target error)) (offset 0))
                 (:instance lw-complex-difference-symmetric (left (lw-complex-reciprocal (lw-complex-sub (cons rate 0) point))) (right (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate radius target error) point 0)) (radius error))
                 (:instance lw-complex-difference-triangle (left (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate radius target error) point 0)) (middle (lw-complex-reciprocal (lw-complex-sub (cons rate 0) point)))
                   (right (cons 0 0)) (radius error) (other-radius (/ (- rate radius)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-wide-linear-inverse lw-complex-sub-zero
              lw-pwli-left-commutes lw-pwli-left-distributes lw-pwli-fold-constants
              lw-pwli-times-negative lw-pwli-negative-times lw-pwli-zero-times
              lw-pwli-minus-one lw-pwli-double-negative lw-pwli-add-cancel lw-pwli-double lw-pwli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
