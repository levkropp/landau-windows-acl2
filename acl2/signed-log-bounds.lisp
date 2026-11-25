(in-package "ACL2")

(include-book "log-cell-bounds")

; Reflect the positive logarithm enclosure for arguments below one.

(local (defthm lw-slb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-slb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-slb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-slb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-slb-times-negative (a b) (b a)))
                 :in-theory (disable lw-slb-times-negative)))))

(local (defthm lw-slb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-slb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-slb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-slb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-slb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-slb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-slb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-slb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-slb-left-commutes)))))

(defun lw-signed-log-bounds (value error)
  (if (< value 1)
      (let ((reflected (lw-log-bounds (/ value) error)))
        (cons (- (cdr reflected)) (- (car reflected))))
    (if (equal value 1)
        (cons 0 0)
      (lw-log-bounds value error))))

(local
 (defthm lw-slb-inverse-above-one
   (implies (and (rationalp value) (< 0 value) (< value 1))
            (and (rationalp (/ value)) (< 1 (/ value))))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive)
                  (:instance inverse-of-* (x value))
                  (:instance lw-slb-positive-product (a (- 1 value)) (b (/ value))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(defthm lw-signed-log-bounds-data
  (implies (and (rationalp value) (< 0 value)
                (rationalp error) (< 0 error))
           (let ((bounds (lw-signed-log-bounds value error)))
             (and (lw-intervalp bounds)
                  (<= (- (cdr bounds) (car bounds)) error))))
  :hints (("Goal"
           :use (lw-slb-inverse-above-one
                 (:instance lw-log-bounds-interval (epsilon error))
                 (:instance lw-log-bounds-interval (value (/ value)) (epsilon error))
                 (:instance lw-log-bounds-width (epsilon error))
                 (:instance lw-log-bounds-width (value (/ value)) (epsilon error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-signed-log-bounds lw-intervalp
              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-slb-inverse-involution
   (implies (and (rationalp value) (< 0 value)) (equal (/ (/ value)) value))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x value))
                  (:instance inverse-of-* (x (/ value)))
                  (:instance lw-reciprocal-positive))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))))

(defthm lw-signed-log-bounds-unit-envelopes
  (implies (and (rationalp value) (< 0 value)
                (rationalp error) (< 0 error))
           (let ((bounds (lw-signed-log-bounds value error)))
             (and (<= (- 1 (/ value)) (cdr bounds))
                  (<= (car bounds) (- value 1)))))
  :hints (("Goal"
           :use (lw-slb-inverse-above-one
                 lw-log-bounds-unit-envelopes
                 (:instance lw-log-bounds-unit-envelopes (value (/ value)))
                 (:instance lw-log-bounds-interval (epsilon error))
                 (:instance lw-log-bounds-interval (value (/ value)) (epsilon error))
                 (:instance inverse-of-* (x value)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-signed-log-bounds lw-intervalp lw-slb-inverse-involution
              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-signed-log-lower-linear-error
  (implies (and (rationalp value) (< 0 value)
                (rationalp error) (< 0 error))
           (<= (abs (- (car (lw-signed-log-bounds value error)) (- value 1)))
               (+ error (/ (* (- value 1) (- value 1)) value))))
  :hints (("Goal"
           :use (lw-signed-log-bounds-data lw-signed-log-bounds-unit-envelopes
                 (:instance inverse-of-* (x value))
                 (:instance lw-slb-inverse-factor (divisor value) (coefficient value)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp abs
              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-signed-log-bounds-overlap
  (implies (and (rationalp value) (< 0 value)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-signed-log-bounds value left-error))
               (cdr (lw-signed-log-bounds value right-error))))
  :hints (("Goal"
           :use (lw-slb-inverse-above-one lw-log-bounds-overlap
                 (:instance lw-log-bounds-overlap (value (/ value))
                   (left-error right-error) (right-error left-error))
                 (:instance lw-log-bounds-interval (value (/ value)) (epsilon right-error))
                 (:instance lw-log-bounds-interval (value (/ value)) (epsilon left-error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-signed-log-bounds lw-intervalp
              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-signed-log-bounds-reciprocal
  (implies (and (rationalp value) (< 0 value)
                (rationalp error) (< 0 error))
           (and (equal (car (lw-signed-log-bounds (/ value) error))
                       (- (cdr (lw-signed-log-bounds value error))))
                (equal (cdr (lw-signed-log-bounds (/ value) error))
                       (- (car (lw-signed-log-bounds value error))))))
  :hints (("Goal"
           :use (lw-slb-inverse-above-one
                 (:instance lw-reciprocal-positive)
                 (:instance lw-slb-positive-product (a (- value 1)) (b (/ value)))
                 (:instance lw-log-bounds-interval (value (/ value)) (epsilon error))
                 (:instance inverse-of-* (x value)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-signed-log-bounds lw-slb-inverse-involution lw-intervalp
              lw-slb-left-commutes lw-slb-left-distributes lw-slb-fold-constants
              lw-slb-times-negative lw-slb-negative-times lw-slb-zero-times
              lw-slb-minus-one lw-slb-double-negative lw-slb-add-cancel lw-slb-double lw-slb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
