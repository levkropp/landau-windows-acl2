(in-package "ACL2")

(include-book "signed-log-positive-lower")

; A coarse squared value cap gives a nonnegative boundary real part.
; An interior upper bound for that real part then gives a positive floor.

(local (defthm lw-crhb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crhb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crhb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crhb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crhb-times-negative (a b) (b a)))
                 :in-theory (disable lw-crhb-times-negative)))))

(local (defthm lw-crhb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crhb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crhb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crhb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crhb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crhb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crhb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crhb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crhb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-log-offset (center-lower boundary-cap)
  (+ 2 boundary-cap (/ center-lower)))

(defun lw-circle-reflected-log-interior-variation (center-lower boundary-cap inner)
  (* inner (/ (- 1 inner)) (+ 4 (* 2 (lw-circle-reflected-log-offset center-lower boundary-cap)))))

(defun lw-circle-reflected-square-lower (center-lower boundary-cap inner)
  (lw-signed-log-value-lower (+ 1 (/ center-lower) (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner))))

(defthm lw-circle-reflected-log-offset-positive
  (implies (and (rationalp center-lower) (< 0 center-lower)
                (rationalp boundary-cap) (<= 0 boundary-cap))
           (and (rationalp (lw-circle-reflected-log-offset center-lower boundary-cap)) (< 0 (lw-circle-reflected-log-offset center-lower boundary-cap))))
  :hints (("Goal" :use ((:instance lw-reciprocal-positive (value center-lower)))
                  :in-theory (union-theories
            '(fold-consts-in-+
              lw-circle-reflected-log-offset
              lw-crhb-left-commutes lw-crhb-left-distributes lw-crhb-fold-constants
              lw-crhb-times-negative lw-crhb-negative-times lw-crhb-zero-times
              lw-crhb-minus-one lw-crhb-double-negative lw-crhb-add-cancel lw-crhb-double lw-crhb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t))
  :rule-classes nil)

(defthm lw-circle-reflected-log-boundary-positive
  (implies (and (rationalp center-lower) (< 0 center-lower)
                (rationalp boundary-cap) (<= 0 boundary-cap)
                (rationalp center) (<= center-lower center)
                (rationalp value) (< 0 value)
                (rationalp error) (< 0 error) (<= error 1)
                (rationalp real-part)
                (<= (abs (+ (- (car (lw-signed-log-bounds value error)) (car (lw-signed-log-bounds center error))) (- real-part (lw-circle-reflected-log-offset center-lower boundary-cap)))) 1)
                (<= value boundary-cap))
           (<= 0 real-part))
  :hints (("Goal"
           :use ((:instance lw-signed-log-lower-envelope (value center))
                 (:instance lw-signed-log-bounds-unit-envelopes)
                 (:instance lw-signed-log-bounds-data (value center))
                 (:instance lw-signed-log-bounds-data)
                 (:instance lw-reciprocal-antitone (left center-lower) (right center)))
           :in-theory (union-theories
            '(fold-consts-in-+
              lw-circle-reflected-log-offset lw-intervalp abs
              lw-crhb-left-commutes lw-crhb-left-distributes lw-crhb-fold-constants
              lw-crhb-times-negative lw-crhb-negative-times lw-crhb-zero-times
              lw-crhb-minus-one lw-crhb-double-negative lw-crhb-add-cancel lw-crhb-double lw-crhb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-crhb-variation-data
   (implies (and (rationalp center-lower) (< 0 center-lower)
                 (rationalp boundary-cap) (<= 0 boundary-cap)
                 (rationalp inner) (<= 0 inner) (< inner 1))
            (and (rationalp (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner)) (<= 0 (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner))))
   :hints (("Goal"
            :use (lw-circle-reflected-log-offset-positive
                  (:instance lw-reciprocal-positive (value (- 1 inner)))
                  (:instance lw-crhb-multiply-order (a 0) (b inner) (factor (/ (- 1 inner))))
                  (:instance lw-crhb-multiply-order (a 0) (b (+ 4 (* 2 (lw-circle-reflected-log-offset center-lower boundary-cap)))) (factor (* inner (/ (- 1 inner))))))
            :in-theory (union-theories
            '(fold-consts-in-+
              lw-circle-reflected-log-interior-variation
              lw-crhb-left-commutes lw-crhb-left-distributes lw-crhb-fold-constants
              lw-crhb-times-negative lw-crhb-negative-times lw-crhb-zero-times
              lw-crhb-minus-one lw-crhb-double-negative lw-crhb-add-cancel lw-crhb-double lw-crhb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-square-lower-from-log
  (implies (and (rationalp center-lower) (< 0 center-lower)
                (rationalp boundary-cap) (<= 0 boundary-cap)
                (rationalp center) (<= center-lower center)
                (rationalp value) (< 0 value)
                (rationalp error) (< 0 error) (<= error 1)
                (rationalp real-part)
                (<= (abs (+ (- (car (lw-signed-log-bounds value error)) (car (lw-signed-log-bounds center error))) (- real-part (lw-circle-reflected-log-offset center-lower boundary-cap)))) 1)
                (rationalp inner) (<= 0 inner) (< inner 1)
                (<= real-part (+ (lw-circle-reflected-log-offset center-lower boundary-cap) (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner))))
           (let ((lower (lw-circle-reflected-square-lower center-lower boundary-cap inner)))
             (and (rationalp lower) (< 0 lower) (< lower value))))
  :hints (("Goal"
           :use (lw-circle-reflected-log-offset-positive lw-crhb-variation-data
                 (:instance lw-reciprocal-positive (value center-lower))
                 (:instance lw-signed-log-lower-envelope (value center))
                 (:instance lw-signed-log-bounds-data (value center))
                 (:instance lw-signed-log-bounds-data)
                 (:instance lw-reciprocal-antitone (left center-lower) (right center))
                 (:instance lw-signed-log-value-lower-bound (budget (+ 1 (/ center-lower) (lw-circle-reflected-log-interior-variation center-lower boundary-cap inner)))))
           :in-theory (union-theories
            '(fold-consts-in-+
              lw-circle-reflected-square-lower lw-intervalp abs
              lw-crhb-left-commutes lw-crhb-left-distributes lw-crhb-fold-constants
              lw-crhb-times-negative lw-crhb-negative-times lw-crhb-zero-times
              lw-crhb-minus-one lw-crhb-double-negative lw-crhb-add-cancel lw-crhb-double lw-crhb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
