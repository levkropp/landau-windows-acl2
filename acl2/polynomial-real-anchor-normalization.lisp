(in-package "ACL2")

(include-book "polynomial-divided-difference")
(include-book "polynomial-maps")
(include-book "polynomial-geometric-bounds")

(defun lw-polynomial-real-anchor-numerator (coefficients rate)
  (let ((anchor (cons (- rate 1) 0)))
    (lw-polynomial-add-constant
     (lw-complex-add (cons 1 0) (lw-complex-polynomial coefficients anchor 0))
     (lw-polynomial-divided-difference coefficients anchor))))

(defun lw-polynomial-real-anchor-cap (rate radius cap)
  (+ 1 cap (/ (* 2 cap) (- radius (- rate 1)))))

(local (defthm lw-pran-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pran-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pran-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pran-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pran-times-negative (a b) (b a)))
                 :in-theory (disable lw-pran-times-negative)))))

(local (defthm lw-pran-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pran-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pran-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pran-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pran-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pran-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pran-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-pran-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pran-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pran-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-pran-left-commutes)))))

(local
 (defthm lw-pran-cons-equal
   (equal (equal (cons a b) (cons c d))
          (and (equal a c) (equal b d)))))

(local
 (defthm lw-pran-ring-identity
   (implies (and (lw-complexp point) (rationalp rate)
                 (lw-complexp anchor-value) (lw-complexp difference)
                 (lw-complexp value)
                 (equal (lw-complex-sub value anchor-value)
                        (lw-complex-mul (lw-complex-sub point (cons (- rate 1) 0)) difference)))
            (let ((s (lw-complex-sub (cons rate 0) point)))
              (equal
               (lw-complex-mul (lw-complex-sub s (cons 1 0))
                 (lw-complex-add (lw-complex-add (cons 1 0) anchor-value) difference))
               (lw-complex-sub
                (lw-complex-add (lw-complex-sub s (cons 1 0)) (lw-complex-mul s anchor-value))
                value))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-pran-cons-equal
              lw-pran-left-commutes lw-pran-left-distributes lw-pran-fold-constants
              lw-pran-times-negative lw-pran-negative-times lw-pran-zero-times
              lw-pran-minus-one lw-pran-double-negative lw-pran-add-cancel lw-pran-double lw-pran-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; Replace gamma by the same polynomial's value at s=1. The
; cancellation at s=1 then holds exactly at every polynomial request.
(defthm lw-polynomial-real-anchor-numerator-identity
  (implies (and (rationalp rate) (lw-complexp point) (lw-complex-coefficientsp coefficients))
           (let ((s (lw-complex-sub (cons rate 0) point)))
             (and (lw-complex-coefficientsp (lw-polynomial-real-anchor-numerator coefficients rate))
                  (equal (lw-complex-mul (lw-complex-sub s (cons 1 0))
                            (lw-complex-polynomial (lw-polynomial-real-anchor-numerator coefficients rate) point 0))
                         (lw-complex-sub
                          (lw-complex-add (lw-complex-sub s (cons 1 0)) (lw-complex-mul s (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0)))
                          (lw-complex-polynomial coefficients point 0))))))
  :hints (("Goal"
           :use ((:instance lw-polynomial-divided-difference-valid (anchor (cons (- rate 1) 0)))
                 (:instance lw-polynomial-divided-difference-identity (anchor (cons (- rate 1) 0)))
                 (:instance lw-polynomial-add-constant-valid (constant (lw-complex-add (cons 1 0) (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0))) (coefficients (lw-polynomial-divided-difference coefficients (cons (- rate 1) 0))))
                 (:instance lw-polynomial-add-constant-evaluation (constant (lw-complex-add (cons 1 0) (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0))) (coefficients (lw-polynomial-divided-difference coefficients (cons (- rate 1) 0))))
                 (:instance lw-pran-ring-identity
                   (anchor-value (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0)) (difference (lw-complex-polynomial (lw-polynomial-divided-difference coefficients (cons (- rate 1) 0)) point 0)) (value (lw-complex-polynomial coefficients point 0))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-real-anchor-numerator
              lw-complex-polynomial-rational lw-complex-ring-rational lw-complexp
              lw-pran-left-commutes lw-pran-left-distributes lw-pran-fold-constants
              lw-pran-times-negative lw-pran-negative-times lw-pran-zero-times
              lw-pran-minus-one lw-pran-double-negative lw-pran-add-cancel lw-pran-double lw-pran-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-pran-real-offset-gap
   (implies (and (lw-complexp point) (rationalp radius) (< 0 radius)
                 (equal (lw-complex-norm-square point) (* radius radius))
                 (rationalp offset) (<= 0 offset) (< offset radius))
            (<= (* (- radius offset) (- radius offset))
                (lw-complex-norm-square (lw-complex-sub point (cons offset 0)))))
   :hints (("Goal"
            :use (lw-complex-disk-norm-square lw-complex-disk-coordinates
                  (:instance lw-pran-multiply-order
                    (a (car point)) (b radius) (factor (* 2 offset))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-norm-square lw-complex-sub lw-complexp abs
              lw-pran-left-commutes lw-pran-left-distributes lw-pran-fold-constants
              lw-pran-times-negative lw-pran-negative-times lw-pran-zero-times
              lw-pran-minus-one lw-pran-double-negative lw-pran-add-cancel lw-pran-double lw-pran-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-pran-cancelled-quotient-cap
   (implies (and (lw-complexp left) (lw-complexp right) (lw-complexp factor)
                 (lw-complexp quotient)
                 (rationalp gap) (< 0 gap)
                 (<= (* gap gap) (lw-complex-norm-square factor))
                 (lw-complex-diskp left cap) (lw-complex-diskp right cap)
                 (equal (lw-complex-sub left right) (lw-complex-mul factor quotient)))
            (lw-complex-diskp quotient (/ (* 2 cap) gap)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point left) (radius cap))
                  (:instance lw-complex-norm-lower-nonzero (point factor) (lower gap))
                  (:instance lw-complex-reciprocal-cancel-product (a factor) (b quotient))
                  (:instance lw-complex-reciprocal-disk-bound (point factor) (lower gap))
                  (:instance lw-complex-sub-disk (radius cap) (other-radius cap))
                  (:instance lw-complex-mul-disk
                    (left (lw-complex-reciprocal factor)) (radius (/ gap))
                    (right (lw-complex-sub left right)) (other-radius (+ cap cap))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive
              lw-pran-left-commutes lw-pran-left-distributes lw-pran-fold-constants
              lw-pran-times-negative lw-pran-negative-times lw-pran-zero-times
              lw-pran-minus-one lw-pran-double-negative lw-pran-add-cancel lw-pran-double lw-pran-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-polynomial-real-anchor-numerator-bound
  (implies (and (rationalp rate) (<= 1 rate)
                (rationalp radius) (< (- rate 1) radius)
                (lw-complexp point) (equal (lw-complex-norm-square point) (* radius radius))
                (lw-complex-coefficientsp coefficients)
                (lw-complex-diskp (lw-complex-polynomial coefficients point 0) cap) (lw-complex-diskp (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0) cap))
           (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-real-anchor-numerator coefficients rate) point 0) (lw-polynomial-real-anchor-cap rate radius cap)))
  :hints (("Goal"
           :use ((:instance lw-pran-real-offset-gap (offset (- rate 1)))
                 (:instance lw-polynomial-divided-difference-valid (anchor (cons (- rate 1) 0)))
                 (:instance lw-polynomial-divided-difference-identity (anchor (cons (- rate 1) 0)))
                 (:instance lw-polynomial-add-constant-evaluation
                   (constant (lw-complex-add (cons 1 0) (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0))) (coefficients (lw-polynomial-divided-difference coefficients (cons (- rate 1) 0))))
                 (:instance lw-pran-cancelled-quotient-cap
                   (left (lw-complex-polynomial coefficients point 0)) (right (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0))
                   (factor (lw-complex-sub point (cons (- rate 1) 0))) (quotient (lw-complex-polynomial (lw-polynomial-divided-difference coefficients (cons (- rate 1) 0)) point 0)) (gap (- radius (- rate 1))))
                 (:instance lw-complex-add-disk
                   (left (cons 1 0)) (right (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0)) (radius 1) (other-radius cap))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-add (cons 1 0) (lw-complex-polynomial coefficients (cons (- rate 1) 0) 0))) (right (lw-complex-polynomial (lw-polynomial-divided-difference coefficients (cons (- rate 1) 0)) point 0))
                   (radius (+ 1 cap)) (other-radius (/ (* 2 cap) (- radius (- rate 1))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-real-anchor-numerator lw-polynomial-real-anchor-cap
              lw-complex-polynomial-rational lw-complex-ring-rational
              (:executable-counterpart lw-complex-diskp) lw-complexp
              lw-pran-left-commutes lw-pran-left-distributes lw-pran-fold-constants
              lw-pran-times-negative lw-pran-negative-times lw-pran-zero-times
              lw-pran-minus-one lw-pran-double-negative lw-pran-add-cancel lw-pran-double lw-pran-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
