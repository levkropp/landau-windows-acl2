(in-package "ACL2")

(include-book "signed-log-bounds")
(include-book "complex-geometric")

; The squared modulus of 1-z has a real logarithm. Its first-order
; increment is -2*Re(z), with a rational error on a small disk.

(local (defthm lw-clui-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clui-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clui-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clui-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clui-times-negative (a b) (b a)))
                 :in-theory (disable lw-clui-times-negative)))))

(local (defthm lw-clui-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clui-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clui-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clui-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clui-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clui-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clui-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clui-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clui-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clui-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clui-left-commutes)))))

(local
 (defthm lw-clui-norm-expansion
   (implies (lw-complexp point)
            (equal (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))
                   (+ 1 (* -2 (car point)) (lw-complex-norm-square point))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub lw-complex-norm-square
              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-clui-small-square
   (implies (and (rationalp delta) (rationalp cap) (<= (abs delta) cap))
            (and (<= 0 (* delta delta)) (<= (* delta delta) (* cap cap))))
   :hints (("Goal"
            :use ((:instance lw-clui-multiply-order (a 0) (b (abs delta)) (factor (abs delta)))
                  (:instance lw-clui-multiply-order (a (abs delta)) (b cap) (factor (abs delta)))
                  (:instance lw-clui-multiply-order (a (abs delta)) (b cap) (factor cap)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-clui-square-over-norm
   (implies (and (rationalp norm) (<= 1/2 norm)
                 (rationalp part) (<= 0 part)
                 (rationalp cap-square) (<= part cap-square))
            (<= (/ part norm) (* 2 cap-square)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-antitone (left 1/2) (right norm))
                  (:instance lw-clui-multiply-order (a (/ norm)) (b 2) (factor part))
                  (:instance lw-clui-multiply-order (a part) (b cap-square) (factor 2)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-clui-ratio-increment
   (implies (and (rationalp radius) (<= 0 radius) (<= radius 1/4)
                 (rationalp real) (<= (abs real) radius)
                 (rationalp square) (<= 0 square) (<= square (* radius radius))
                 (rationalp norm) (equal norm (+ 1 (* -2 real) square)))
            (<= (abs (- norm 1)) (* 3 radius)))
   :hints (("Goal"
            :use ((:instance lw-clui-multiply-order (a radius) (b 1) (factor radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-clui-scalar-bound
   (implies (and (rationalp radius) (<= 0 radius) (<= radius 1/4)
                 (rationalp real) (<= (abs real) radius)
                 (rationalp square) (<= 0 square) (<= square (* radius radius))
                 (rationalp norm) (<= 1/2 norm)
                 (equal norm (+ 1 (* -2 real) square)))
            (<= (/ (* (- norm 1) (- norm 1)) norm) (* 18 radius radius)))
   :hints (("Goal"
            :use (lw-clui-ratio-increment
                  (:instance lw-clui-small-square (delta (- norm 1)) (cap (* 3 radius)))
                  (:instance lw-clui-square-over-norm
                    (part (* (- norm 1) (- norm 1))) (cap-square (* 9 radius radius))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-clui-unit-gap
   (implies (and (rationalp radius) (<= 0 radius) (<= radius 1/4))
            (<= 1/2 (* (- 1 radius) (- 1 radius))))
   :hints (("Goal"
            :use ((:instance lw-clui-multiply-order (a 0) (b radius) (factor radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-log-unit-increment
  (implies (and (lw-complex-diskp point radius) (<= radius 1/4)
                (rationalp error) (< 0 error))
           (let* ((norm (lw-complex-norm-square (lw-complex-sub (cons 1 0) point)))
                  (logarithm (car (lw-signed-log-bounds norm error))))
             (and (<= 1/2 norm)
                  (<= (abs (+ logarithm (* 2 (car point))))
                      (+ error (* 19 radius radius))))))
  :hints (("Goal"
           :use (lw-complex-disk-data lw-complex-disk-norm-square lw-complex-disk-coordinates
                 lw-complex-one-minus-norm-lower lw-clui-unit-gap
                 (:instance lw-complex-norm-square-valid)
                 (:instance lw-complex-ring-rational (left (cons 1 0)) (right point))
                 (:instance lw-complex-norm-square-valid (point (lw-complex-sub (cons 1 0) point)))
                 (:instance lw-clui-scalar-bound (real (car point)) (square (lw-complex-norm-square point)) (norm (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
                 (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
                 (:instance lw-signed-log-lower-linear-error (value (lw-complex-norm-square (lw-complex-sub (cons 1 0) point)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-clui-norm-expansion lw-complexp lw-intervalp abs
              lw-clui-left-commutes lw-clui-left-distributes lw-clui-fold-constants
              lw-clui-times-negative lw-clui-negative-times lw-clui-zero-times
              lw-clui-minus-one lw-clui-double-negative lw-clui-add-cancel lw-clui-double lw-clui-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t
           :nonlinearp nil))
  :rule-classes nil)
