(in-package "ACL2")

(include-book "circle-reflected-boundary-budget")

; With no inner factors, the original polynomial inherits the Harnack floor.

(local (defthm lw-cnif-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cnif-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cnif-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cnif-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cnif-times-negative (a b) (b a)))
                 :in-theory (disable lw-cnif-times-negative)))))

(local (defthm lw-cnif-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cnif-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cnif-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cnif-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cnif-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cnif-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cnif-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cnif-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnif-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnif-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cnif-left-commutes)))))

(defthm lw-circle-inner-factor-count-natural
   (natp (lw-circle-inner-factor-count roots cutoff-square))
   :hints (("Goal"
            :induct (lw-circle-inner-factor-count roots cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-inner-factor-count endp
              lw-cnif-left-commutes lw-cnif-left-distributes lw-cnif-fold-constants
              lw-cnif-times-negative lw-cnif-negative-times lw-cnif-zero-times
              lw-cnif-minus-one lw-cnif-double-negative lw-cnif-add-cancel lw-cnif-double lw-cnif-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
  :rule-classes (:rewrite :type-prescription))

(local
 (defthm lw-cnif-no-reflections
   (implies (equal (lw-circle-inner-factor-count roots cutoff-square) 0)
            (equal (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
                   (lw-polynomial-factor-coefficients roots leading)))
   :hints (("Goal"
            :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-polynomial lw-polynomial-factor-coefficients
               lw-circle-inner-factor-count lw-circle-inner-factor-count-natural endp
              lw-cnif-left-commutes lw-cnif-left-distributes lw-cnif-fold-constants
              lw-cnif-times-negative lw-cnif-negative-times lw-cnif-zero-times
              lw-cnif-minus-one lw-cnif-double-negative lw-cnif-add-cancel lw-cnif-double lw-cnif-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(defthm lw-circle-no-inner-factors-lower
  (implies
   (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
        (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
        (equal (lw-circle-inner-factor-count roots cutoff-square) 0)
        (rationalp scale) (< 0 scale) (< (* scale scale) cutoff-square)
        (rationalp cap) (<= 0 cap)
        (lw-circle-factor-boundary-check roots leading cutoff-square cap)
        (rationalp center-lower) (< 0 center-lower)
        (<= center-lower (lw-complex-norm-square
                           (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0)))
        (lw-complex-diskp point inner) (< inner 1))
   (let ((bound (lw-circle-reflected-square-lower center-lower
                  (lw-circle-reflected-boundary-square-cap cap scale) inner)))
     (and (rationalp bound) (< 0 bound)
          (< bound (lw-complex-norm-square
                    (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading)
                                           (lw-complex-scale scale point) 0))))))
  :hints (("Goal"
           :use (lw-cnif-no-reflections lw-circle-reflected-lower-from-original-boundary)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-value-square
              lw-cnif-left-commutes lw-cnif-left-distributes lw-cnif-fold-constants
              lw-cnif-times-negative lw-cnif-negative-times lw-cnif-zero-times
              lw-cnif-minus-one lw-cnif-double-negative lw-cnif-add-cancel lw-cnif-double lw-cnif-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
