(in-package "ACL2")

(include-book "circle-interior-pole-power-sums")
(include-book "polynomial-exponential-decay")
(include-book "kernel-tilts")

(defun lw-circle-pole-tail-minimum-order (inner clearance count mass fraction)
  (lw-polynomial-decay-index (/ inner clearance) (- count 1) (+ 3 count)
    (* 8 (lw-rational-power 3 (- count 1)) (/ count) mass inner)
    fraction))

(local (defthm lw-cpt-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cpt-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cpt-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cpt-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cpt-times-negative (a b) (b a)))
                 :in-theory (disable lw-cpt-times-negative)))))

(local (defthm lw-cpt-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cpt-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cpt-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cpt-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cpt-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cpt-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cpt-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cpt-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cpt-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cpt-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cpt-left-commutes)))))

(local
 (defthm lw-cpt-scale-identity
   (implies (and (rationalp inner) (rationalp clearance) (< 0 clearance)
                 (natp order))
            (equal (* (lw-rational-power (/ clearance) order) (lw-rational-power inner (+ 1 order))) (* inner (lw-rational-power (/ inner clearance) order))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-add-exponents
                    (base inner) (left 1) (right order))
                  (:instance lw-rational-power-product
                    (left inner) (right (/ clearance)) (exponent order)))
            :expand ((lw-rational-power inner 1) (lw-rational-power inner 0))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power-rational
              lw-cpt-left-commutes lw-cpt-left-distributes lw-cpt-fold-constants
              lw-cpt-times-negative lw-cpt-negative-times lw-cpt-zero-times
              lw-cpt-minus-one lw-cpt-double-negative lw-cpt-add-cancel lw-cpt-double lw-cpt-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cpt-normalization
   (implies (and (posp count) (natp start))
            (let ((scale (* (* 8 (lw-rational-power 3 (- count 1)) (/ count)) (lw-rational-power (+ 3 count start) (- count 1)))))
              (and (rationalp scale) (< 0 scale)
                   (rationalp (lw-circle-interior-pole-count-cap count (+ 2 start))) (< 0 (lw-circle-interior-pole-count-cap count (+ 2 start)))
                   (equal (* scale (lw-circle-interior-pole-count-cap count (+ 2 start))) 1))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-at-least-one
                    (base 3) (exponent (- count 1)))
                  (:instance lw-rational-power-at-least-one
                    (base (+ 3 count start)) (exponent (- count 1)))
                  (:instance lw-rational-power-product
                    (left 3) (right (+ 3 count start)) (exponent (- count 1)))
                  (:instance lw-cpt-positive-product (a (lw-rational-power 3 (- count 1))) (b (lw-rational-power (+ 3 count start) (- count 1))))
                  (:instance inverse-of-* (x count))
                  (:instance inverse-of-* (x (* (lw-rational-power 3 (- count 1)) (lw-rational-power (+ 3 count start) (- count 1)))))
                  (:instance lw-cpt-positive-product (a (* 8 (/ count))) (b (* (lw-rational-power 3 (- count 1)) (lw-rational-power (+ 3 count start) (- count 1)))))
                  (:instance lw-cpt-positive-product (a (* 1/8 count)) (b (/ (* (lw-rational-power 3 (- count 1)) (lw-rational-power (+ 3 count start) (- count 1)))))))
            :in-theory
            (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-interior-pole-count-cap lw-power-domination-factor nfix
              lw-rational-power-rational lw-reciprocal-positive
              lw-cpt-left-commutes lw-cpt-left-distributes lw-cpt-fold-constants
              lw-cpt-times-negative lw-cpt-negative-times lw-cpt-zero-times
              lw-cpt-minus-one lw-cpt-double-negative lw-cpt-add-cancel lw-cpt-double lw-cpt-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cpt-multiply-strict
   (implies (and (rationalp a) (rationalp b) (< a b)
                 (rationalp factor) (< 0 factor))
            (< (* a factor) (* b factor)))
   :hints (("Goal" :in-theory (theory 'ground-zero) :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-cpt-ratio-data
   (implies (and (rationalp inner) (< 0 inner)
                 (rationalp clearance) (< inner clearance))
            (and (rationalp (/ inner clearance))
                 (< 0 (/ inner clearance)) (< (/ inner clearance) 1)))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x clearance))
                  (:instance lw-cpt-positive-product (a inner) (b (/ clearance)))
                  (:instance lw-cpt-multiply-strict (a inner) (b clearance) (factor (/ clearance))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive
              lw-cpt-left-commutes lw-cpt-left-distributes lw-cpt-fold-constants
              lw-cpt-times-negative lw-cpt-negative-times lw-cpt-zero-times
              lw-cpt-minus-one lw-cpt-double-negative lw-cpt-add-cancel lw-cpt-double lw-cpt-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local (defthm lw-cpt-right-one (equal (* value 1) (fix value))))

(local
 (defthm lw-cpt-inverse-unique
   (implies (and (rationalp scale) (rationalp bound) (< 0 scale)
                 (equal (* scale bound) 1))
            (equal bound (/ scale)))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x scale))
                  (:instance associativity-of-* (x (/ scale)) (y scale) (z bound))
                  (:instance commutativity-of-* (x (/ scale)) (y scale)))
            :in-theory (disable inverse-of-* associativity-of-*
                                commutativity-of-* lw-cpt-left-commutes
                                lw-cpt-left-distributes distributivity)))
   :rule-classes nil))

(local
 (defthm lw-cpt-solve-scaled-budget
   (implies (and (rationalp tail) (rationalp scale) (< 0 scale)
                 (rationalp size) (rationalp bound) (< 0 size)
                 (rationalp fraction) (equal (* scale bound) 1)
                 (<= (* scale (* tail size)) fraction))
            (<= tail (* fraction bound (/ size))))
   :hints (("Goal"
            :use (lw-cpt-inverse-unique
                  (:instance lw-cpt-multiply-order
                    (a (* scale (* tail size))) (b fraction) (factor (/ scale)))
                  (:instance lw-cpt-inverse-factor (divisor scale) (coefficient (* tail size)))
                  (:instance lw-positive-division-lower-bound
                    (numerator (* fraction bound)) (divisor size) (bound tail)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive
              lw-cpt-left-commutes lw-cpt-left-distributes lw-cpt-fold-constants
              lw-cpt-times-negative lw-cpt-negative-times lw-cpt-zero-times
              lw-cpt-minus-one lw-cpt-double-negative lw-cpt-add-cancel lw-cpt-double lw-cpt-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; At any order after the start of the search block, a geometric tail at a
; strictly larger radius consumes at most the chosen fraction of the bound.
(defthm lw-circle-pole-tail-computed-budget
  (implies (and (posp count) (natp start) (natp order) (<= start order)
                (rationalp inner) (< 0 inner) (rationalp clearance) (< inner clearance)
                (rationalp mass) (<= 0 mass) (rationalp fraction) (< 0 fraction)
                (<= (lw-circle-pole-tail-minimum-order inner clearance count mass fraction) start))
           (<= (* mass (lw-rational-power (/ clearance) order))
               (* fraction (lw-circle-interior-pole-count-cap count (+ 2 start)) (/ (lw-rational-power inner (+ 1 order))))))
  :hints (("Goal"
           :use (lw-cpt-normalization lw-cpt-ratio-data lw-cpt-scale-identity
                 (:instance lw-polynomial-exponential-computed-decay
                   (ratio (/ inner clearance)) (degree (- count 1)) (offset (+ 3 count))
                   (mass (* (* 8 (lw-rational-power 3 (- count 1)) (/ count)) mass inner)) (tolerance fraction) (index start))
                 (:instance lw-rational-power-contractive-exponent (base (/ inner clearance))
                   (small start) (large order))
                 (:instance lw-rational-power-positive (base inner) (exponent (+ 1 order)))
                 (:instance lw-rational-power-at-least-one (base (+ 3 count start)) (exponent (- count 1)))
                 (:instance lw-rational-power-at-least-one (base 3) (exponent (- count 1)))
                 (:instance lw-cpt-multiply-order
                   (a (lw-rational-power (/ inner clearance) order)) (b (lw-rational-power (/ inner clearance) start)) (factor (* (* (* 8 (lw-rational-power 3 (- count 1)) (/ count)) mass inner) (lw-rational-power (+ 3 count start) (- count 1)))))
                 (:instance lw-cpt-solve-scaled-budget
                   (tail (* mass (lw-rational-power (/ clearance) order))) (scale (* (* 8 (lw-rational-power 3 (- count 1)) (/ count)) (lw-rational-power (+ 3 count start) (- count 1))))
                   (size (lw-rational-power inner (+ 1 order))) (bound (lw-circle-interior-pole-count-cap count (+ 2 start)))))
           :in-theory
           (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pole-tail-minimum-order lw-rational-power-rational
              lw-reciprocal-positive
              lw-cpt-left-commutes lw-cpt-left-distributes lw-cpt-fold-constants
              lw-cpt-times-negative lw-cpt-negative-times lw-cpt-zero-times
              lw-cpt-minus-one lw-cpt-double-negative lw-cpt-add-cancel lw-cpt-double lw-cpt-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
