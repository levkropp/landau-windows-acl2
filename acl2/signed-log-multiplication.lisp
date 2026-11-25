(in-package "ACL2")

(include-book "signed-log-bounds")
(include-book "log-multiplication")

; Reciprocals transport logarithm products across the cutoff at one.
; The input and output precisions remain independent.

(local (defthm lw-slm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-slm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-slm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-slm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-slm-times-negative (a b) (b a)))
                 :in-theory (disable lw-slm-times-negative)))))

(local (defthm lw-slm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-slm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-slm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-slm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-slm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-slm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-slm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-slm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-slm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-slm-left-commutes)))))

(local
 (defthm lw-slm-positive-overlap
   (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right)
                 (rationalp left-error) (< 0 left-error)
                 (rationalp right-error) (< 0 right-error)
                 (rationalp product-error) (< 0 product-error)
                 (<= 1 left) (<= 1 right))
            (and (<= (car (lw-signed-log-bounds (* left right) product-error)) (+ (cdr (lw-signed-log-bounds left left-error)) (cdr (lw-signed-log-bounds right right-error))))
                 (<= (+ (car (lw-signed-log-bounds left left-error)) (car (lw-signed-log-bounds right right-error))) (cdr (lw-signed-log-bounds (* left right) product-error)))))
   :hints (("Goal"
            :use (lw-log-bounds-product-overlap
                  (:instance lw-slm-multiply-order (a 1) (b left) (factor right))
                  (:instance lw-log-bounds-overlap (value left) (right-error product-error))
                  (:instance lw-log-bounds-overlap (value left) (left-error product-error) (right-error left-error))
                  (:instance lw-log-bounds-overlap (value right) (left-error right-error) (right-error product-error))
                  (:instance lw-log-bounds-overlap (value right) (left-error product-error))
                  (:instance lw-log-bounds-interval (value left) (epsilon left-error))
                  (:instance lw-log-bounds-interval (value left) (epsilon product-error))
                  (:instance lw-log-bounds-interval (value right) (epsilon right-error))
                  (:instance lw-log-bounds-interval (value right) (epsilon product-error)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-signed-log-bounds lw-intervalp
              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-slm-reciprocal-above-one
   (implies (and (rationalp value) (< 0 value) (<= value 1))
            (<= 1 (/ value)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-antitone (left value) (right 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-slm-cancel-equality
   (implies (and (rationalp factor) (< 0 factor) (rationalp a) (rationalp b)
                 (equal (* factor a) (* factor b)))
            (equal a b))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-slm-inverse-product
   (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
            (and (equal (/ (* a b)) (* (/ a) (/ b)))
                 (equal (* (* a b) (/ b)) a)
                 (equal (* a (/ (* a b))) (/ b))))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
                  (:instance inverse-of-* (x (* a b)))
                  (:instance lw-slm-positive-product)
                  (:instance lw-slm-cancel-equality
                    (factor (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-slm-below-overlap
   (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right)
                 (rationalp left-error) (< 0 left-error)
                 (rationalp right-error) (< 0 right-error)
                 (rationalp product-error) (< 0 product-error)
                 (<= left 1) (<= right 1))
            (and (<= (car (lw-signed-log-bounds (* left right) product-error)) (+ (cdr (lw-signed-log-bounds left left-error)) (cdr (lw-signed-log-bounds right right-error))))
                 (<= (+ (car (lw-signed-log-bounds left left-error)) (car (lw-signed-log-bounds right right-error))) (cdr (lw-signed-log-bounds (* left right) product-error)))))
   :hints (("Goal"
            :use ((:instance lw-slm-inverse-product (a left) (b right))
                  (:instance lw-slm-reciprocal-above-one (value left))
                  (:instance lw-slm-reciprocal-above-one (value right))
                  (:instance lw-slm-positive-product (a left) (b right))
                  (:instance lw-reciprocal-positive (value left))
                  (:instance lw-reciprocal-positive (value right))
                  (:instance lw-signed-log-bounds-data (value left) (error left-error))
                  (:instance lw-signed-log-bounds-data (value right) (error right-error))
                  (:instance lw-signed-log-bounds-data (value (* left right)) (error product-error))
                  (:instance lw-signed-log-bounds-reciprocal (value left) (error left-error))
                  (:instance lw-signed-log-bounds-reciprocal (value right) (error right-error))
                  (:instance lw-signed-log-bounds-reciprocal (value (* left right)) (error product-error))
                  (:instance lw-slm-positive-overlap (left (/ left)) (right (/ right))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp
              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-slm-mixed-overlap
   (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right)
                 (rationalp left-error) (< 0 left-error)
                 (rationalp right-error) (< 0 right-error)
                 (rationalp product-error) (< 0 product-error)
                 (<= 1 left) (<= right 1))
            (and (<= (car (lw-signed-log-bounds (* left right) product-error)) (+ (cdr (lw-signed-log-bounds left left-error)) (cdr (lw-signed-log-bounds right right-error))))
                 (<= (+ (car (lw-signed-log-bounds left left-error)) (car (lw-signed-log-bounds right right-error))) (cdr (lw-signed-log-bounds (* left right) product-error)))))
   :hints (("Goal"
            :cases ((<= 1 (* left right)))
            :use ((:instance lw-slm-positive-product (a left) (b right))
                  (:instance lw-slm-inverse-product (a left) (b right))
                  (:instance lw-slm-reciprocal-above-one (value right))
                  (:instance lw-slm-reciprocal-above-one (value (* left right)))
                  (:instance lw-reciprocal-positive (value right))
                  (:instance lw-reciprocal-positive (value (* left right)))
                  (:instance lw-signed-log-bounds-data (value left) (error left-error))
                  (:instance lw-signed-log-bounds-data (value right) (error right-error))
                  (:instance lw-signed-log-bounds-data (value (* left right)) (error product-error))
                  (:instance lw-signed-log-bounds-reciprocal (value right) (error right-error))
                  (:instance lw-signed-log-bounds-reciprocal (value (* left right)) (error product-error))
                  (:instance lw-slm-positive-overlap
                    (left (* left right)) (left-error product-error) (right (/ right))
                    (product-error left-error))
                  (:instance lw-slm-positive-overlap
                    (right (/ (* left right))) (right-error product-error)
                    (product-error right-error)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp
              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-signed-log-product-overlap
  (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right)
                 (rationalp left-error) (< 0 left-error)
                 (rationalp right-error) (< 0 right-error)
                 (rationalp product-error) (< 0 product-error))
           (and (<= (car (lw-signed-log-bounds (* left right) product-error)) (+ (cdr (lw-signed-log-bounds left left-error)) (cdr (lw-signed-log-bounds right right-error))))
                 (<= (+ (car (lw-signed-log-bounds left left-error)) (car (lw-signed-log-bounds right right-error))) (cdr (lw-signed-log-bounds (* left right) product-error)))))
  :hints (("Goal"
           :use (lw-slm-positive-overlap lw-slm-below-overlap lw-slm-mixed-overlap
                 (:instance lw-slm-mixed-overlap (left right) (right left)
                   (left-error right-error) (right-error left-error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-signed-log-lower-multiplication
  (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right)
                 (rationalp left-error) (< 0 left-error)
                 (rationalp right-error) (< 0 right-error)
                 (rationalp product-error) (< 0 product-error))
           (<= (abs (- (+ (car (lw-signed-log-bounds left left-error)) (car (lw-signed-log-bounds right right-error))) (car (lw-signed-log-bounds (* left right) product-error))))
               (+ left-error right-error product-error)))
  :hints (("Goal"
           :use (lw-signed-log-product-overlap
                 (:instance lw-slm-positive-product (a left) (b right))
                 (:instance lw-signed-log-bounds-data (value left) (error left-error))
                  (:instance lw-signed-log-bounds-data (value right) (error right-error))
                  (:instance lw-signed-log-bounds-data (value (* left right)) (error product-error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp abs
              lw-slm-left-commutes lw-slm-left-distributes lw-slm-fold-constants
              lw-slm-times-negative lw-slm-negative-times lw-slm-zero-times
              lw-slm-minus-one lw-slm-double-negative lw-slm-add-cancel lw-slm-double lw-slm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
