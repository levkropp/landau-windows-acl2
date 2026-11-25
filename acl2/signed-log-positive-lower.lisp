(in-package "ACL2")

(include-book "signed-log-bounds")
(include-book "log-growth")
(include-book "rpow-continuity")

; A fixed lower bound on the signed logarithm gives an explicit
; positive floor for the rational argument.

(local (defthm lw-slpl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-slpl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-slpl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-slpl-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-slpl-times-negative (a b) (b a)))
                 :in-theory (disable lw-slpl-times-negative)))))

(local (defthm lw-slpl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-slpl-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-slpl-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-slpl-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-slpl-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-slpl-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-slpl-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-slpl-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slpl-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slpl-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-slpl-left-commutes)))))

(defun lw-signed-log-lower-steps (budget)
  (+ 2 (lw-precision-fuel (* 2 budget) 1)))

(defun lw-signed-log-value-lower (budget)
  (/ (lw-rational-power 2 (+ 1 (lw-signed-log-lower-steps budget)))))

(defthm lw-signed-log-lower-envelope
  (implies (and (rationalp value) (< 0 value)
                (rationalp error) (< 0 error))
           (<= (- 1 (+ (/ value) error))
               (car (lw-signed-log-bounds value error))))
  :hints (("Goal" :use (lw-signed-log-bounds-data lw-signed-log-bounds-unit-envelopes)
                  :in-theory (union-theories
            '(fold-consts-in-+
              lw-intervalp
              lw-slpl-left-commutes lw-slpl-left-distributes lw-slpl-fold-constants
              lw-slpl-times-negative lw-slpl-negative-times lw-slpl-zero-times
              lw-slpl-minus-one lw-slpl-double-negative lw-slpl-add-cancel lw-slpl-double lw-slpl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-slpl-fuel-natural
   (natp (lw-precision-fuel width epsilon))
   :hints (("Goal" :in-theory (enable lw-precision-fuel)))
   :rule-classes (:type-prescription)))

(local
 (defthm lw-slpl-steps-data
   (implies (and (rationalp budget) (<= 0 budget))
            (and (natp (lw-signed-log-lower-steps budget)) (< (* 2 budget) (lw-signed-log-lower-steps budget))))
   :hints (("Goal"
            :use ((:instance lw-precision-fuel-adequate (width (* 2 budget)) (epsilon 1)))
            :in-theory (union-theories
            '(fold-consts-in-+
              lw-signed-log-lower-steps (:type-prescription lw-slpl-fuel-natural)
              lw-slpl-left-commutes lw-slpl-left-distributes lw-slpl-fold-constants
              lw-slpl-times-negative lw-slpl-negative-times lw-slpl-zero-times
              lw-slpl-minus-one lw-slpl-double-negative lw-slpl-add-cancel lw-slpl-double lw-slpl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-slpl-inverse-involution
   (implies (and (rationalp value) (< 0 value))
            (equal (/ (/ value)) value))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x value))
                  (:instance inverse-of-* (x (/ value)))
                  (:instance lw-reciprocal-positive))
            :in-theory (union-theories
            '(fold-consts-in-+

              lw-slpl-left-commutes lw-slpl-left-distributes lw-slpl-fold-constants
              lw-slpl-times-negative lw-slpl-negative-times lw-slpl-zero-times
              lw-slpl-minus-one lw-slpl-double-negative lw-slpl-add-cancel lw-slpl-double lw-slpl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp t))))

(defthm lw-signed-log-value-lower-bound
  (implies (and (rationalp value) (< 0 value)
                (rationalp budget) (<= 0 budget)
                (rationalp error) (< 0 error) (<= error 1)
                (<= (- budget) (car (lw-signed-log-bounds value error))))
           (and (rationalp (lw-signed-log-value-lower budget)) (< 0 (lw-signed-log-value-lower budget))
                (< (lw-signed-log-value-lower budget) value)))
  :hints (("Goal"
           :use (lw-slpl-steps-data
                 (:instance lw-rational-power-strict-base (left 1) (right 2) (exponent (+ 1 (lw-signed-log-lower-steps budget))))
                 (:instance lw-rational-power-at-least-one (base 2) (exponent (+ 1 (lw-signed-log-lower-steps budget))))
                 (:instance lw-reciprocal-positive (value (lw-rational-power 2 (+ 1 (lw-signed-log-lower-steps budget)))))
                 (:instance lw-reciprocal-antitone (left value) (right (lw-signed-log-value-lower budget)))
                 (:instance lw-reciprocal-antitone (left 1) (right (lw-rational-power 2 (+ 1 (lw-signed-log-lower-steps budget)))))
                 (:instance lw-log-bounds-dyadic-growth (value (/ value)) (epsilon error) (steps (lw-signed-log-lower-steps budget)))
                 (:instance lw-log-bounds-interval (value (/ value)) (epsilon error)))
           :in-theory (union-theories
            '(fold-consts-in-+
              lw-signed-log-value-lower lw-signed-log-bounds lw-rational-power-rational
              lw-rational-power-one lw-slpl-inverse-involution lw-intervalp
              lw-slpl-left-commutes lw-slpl-left-distributes lw-slpl-fold-constants
              lw-slpl-times-negative lw-slpl-negative-times lw-slpl-zero-times
              lw-slpl-minus-one lw-slpl-double-negative lw-slpl-add-cancel lw-slpl-double lw-slpl-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
