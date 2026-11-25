(in-package "ACL2")

(include-book "mellin-quadratic-normalization")

(local (defthm lw-ccn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ccn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ccn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ccn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ccn-times-negative (a b) (b a)))
                 :in-theory (disable lw-ccn-times-negative)))))

(local (defthm lw-ccn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ccn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ccn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ccn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ccn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ccn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ccn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local
 (defthm lw-ccn-subtraction
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
            (equal (lw-complex-sub a (lw-complex-sub b c))
                   (lw-complex-sub (lw-complex-add a c) b)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub lw-complex-add
              lw-ccn-left-commutes lw-ccn-left-distributes lw-ccn-fold-constants
              lw-ccn-times-negative lw-ccn-negative-times lw-ccn-zero-times
              lw-ccn-minus-one lw-ccn-double-negative lw-ccn-add-cancel lw-ccn-double lw-ccn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-ccn-zero-scale
   (equal (lw-complex-scale 0 point) (cons 0 0))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-scale
              lw-ccn-left-commutes lw-ccn-left-distributes lw-ccn-fold-constants
              lw-ccn-times-negative lw-ccn-negative-times lw-ccn-zero-times
              lw-ccn-minus-one lw-ccn-double-negative lw-ccn-add-cancel lw-ccn-double lw-ccn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(defthm lw-complex-normalized-euler-cleared
  (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp anchor)
                (not (equal point (cons 0 0)))
                (not (equal (lw-complex-add (cons 1 0) point) (cons 0 0))))
           (equal (lw-complex-mul (lw-complex-mul (lw-complex-add (cons 1 0) point) point) (lw-complex-normalized-euler point value anchor))
                  (lw-complex-sub (lw-complex-add point (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor)) value)))
  :hints (("Goal"
           :use ((:instance lw-complex-local-normalization-times-quadratic
                   (anchor (cons 1 0)) (value (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))) (gamma 0))
                 (:instance lw-complex-local-normalization-normalized
                   (anchor (cons 1 0)) (value (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))) (gamma 0))
                 (:instance lw-complex-sub-zero (point (lw-complex-sub value (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))))
                 (:instance lw-ccn-subtraction (a point) (b value) (c (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-normalized-euler lw-complex-ring-rational
              lw-complex-add-zero lw-complex-sub-zero lw-ccn-zero-scale
              lw-complex-mul-zero (:executable-counterpart lw-complex-sub)
              lw-ccn-left-commutes lw-ccn-left-distributes lw-ccn-fold-constants
              lw-ccn-times-negative lw-ccn-negative-times lw-ccn-zero-times
              lw-ccn-minus-one lw-ccn-double-negative lw-ccn-add-cancel lw-ccn-double lw-ccn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ccn-four-factors
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
            (equal (lw-complex-mul (lw-complex-mul a b) (lw-complex-mul c d))
                   (lw-complex-mul a (lw-complex-mul d (lw-complex-mul b c)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-mul
              lw-ccn-left-commutes lw-ccn-left-distributes lw-ccn-fold-constants
              lw-ccn-times-negative lw-ccn-negative-times lw-ccn-zero-times
              lw-ccn-minus-one lw-ccn-double-negative lw-ccn-add-cancel lw-ccn-double lw-ccn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-ccn-cancel-first
   (implies (and (lw-complexp point) (lw-complexp s) (not (equal s (cons 0 0)))
                 (lw-complexp numerator))
            (equal (lw-complex-mul (lw-complex-mul s point)
                                  (lw-complex-mul numerator (lw-complex-reciprocal s)))
                   (lw-complex-mul point numerator)))
   :hints (("Goal"
            :use ((:instance lw-complex-reciprocal-cancel-product
                    (a s) (b (lw-complex-mul point numerator)))
                  (:instance lw-ccn-four-factors
                    (a s) (b point) (c numerator) (d (lw-complex-reciprocal s))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-ring-rational lw-complex-reciprocal-rational
              lw-ccn-left-commutes lw-ccn-left-distributes lw-ccn-fold-constants
              lw-ccn-times-negative lw-ccn-negative-times lw-ccn-zero-times
              lw-ccn-minus-one lw-ccn-double-negative lw-ccn-add-cancel lw-ccn-double lw-ccn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-normalized-euler-cancelled
  (implies (and (lw-complexp point) (lw-complexp value) (lw-complexp anchor)
                (not (equal point (cons 0 0)))
                (not (equal (lw-complex-add (cons 1 0) point) (cons 0 0)))
                (lw-complexp numerator)
                (equal (lw-complex-mul point numerator)
                       (lw-complex-sub (lw-complex-add point (lw-complex-mul (lw-complex-add (cons 1 0) point) anchor)) value)))
           (equal (lw-complex-normalized-euler point value anchor) (lw-complex-mul numerator (lw-complex-reciprocal (lw-complex-add (cons 1 0) point)))))
  :hints (("Goal"
           :use (lw-complex-normalized-euler-cleared lw-complex-normalized-euler-rational
                 (:instance lw-ccn-cancel-first (s (lw-complex-add (cons 1 0) point)))
                 (:instance lw-complex-product-nonzero (a (lw-complex-add (cons 1 0) point)) (b point))
                 (:instance lw-complex-reciprocal-cancel-product (a (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) (b (lw-complex-normalized-euler point value anchor)))
                 (:instance lw-complex-reciprocal-cancel-product (a (lw-complex-mul (lw-complex-add (cons 1 0) point) point)) (b (lw-complex-mul numerator (lw-complex-reciprocal (lw-complex-add (cons 1 0) point))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-ring-rational lw-complex-reciprocal-rational
              lw-ccn-left-commutes lw-ccn-left-distributes lw-ccn-fold-constants
              lw-ccn-times-negative lw-ccn-negative-times lw-ccn-zero-times
              lw-ccn-minus-one lw-ccn-double-negative lw-ccn-add-cancel lw-ccn-double lw-ccn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
