(in-package "ACL2")

(include-book "circle-pole-split")
(include-book "polynomial-factor-coefficients")

; The first retained interior factor gives an exact zero of the model.

(local (defthm lw-cifp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cifp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cifp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cifp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cifp-times-negative (a b) (b a)))
                 :in-theory (disable lw-cifp-times-negative)))))

(local (defthm lw-cifp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cifp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cifp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cifp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cifp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cifp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cifp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cifp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cifp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cifp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cifp-left-commutes)))))

(local (deftheory lw-cifp-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-cifp-left-commutes lw-cifp-left-distributes lw-cifp-fold-constants
              lw-cifp-times-negative lw-cifp-negative-times lw-cifp-zero-times
              lw-cifp-minus-one lw-cifp-double-negative lw-cifp-add-cancel lw-cifp-double lw-cifp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-circle-first-interior-factor-disk
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (consp (lw-circle-pole-roots roots radius)))
           (and (lw-complexp (car (lw-circle-pole-roots roots radius)))
                (lw-complex-diskp (car (lw-circle-pole-roots roots radius)) radius)))
  :hints (("Goal"
           :induct (lw-circle-pole-roots roots radius)
           :in-theory (union-theories '(lw-circle-pole-roots lw-ray-pointsp endp) (theory 'lw-cifp-arithmetic)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-disk-norm-square (point (car roots)))))))
  :rule-classes nil)

(local
 (defthm lw-cifp-mul-zero
   (and (equal (lw-complex-mul (cons 0 0) point) (cons 0 0))
        (equal (lw-complex-mul point (cons 0 0)) (cons 0 0)))
   :hints (("Goal" :in-theory (union-theories '(lw-complex-mul) (theory 'lw-cifp-arithmetic))))))

(local
 (defthm lw-cifp-first-interior-product-zero
   (implies (and (lw-ray-pointsp roots) (consp (lw-circle-pole-roots roots radius)))
            (equal (lw-polynomial-linear-factor-value roots leading (car (lw-circle-pole-roots roots radius))) (cons 0 0)))
   :hints (("Goal"
            :induct (lw-circle-pole-roots roots radius)
            :in-theory (union-theories '(lw-circle-pole-roots lw-ray-pointsp endp lw-polynomial-linear-factor-value
               lw-cifp-mul-zero) (theory 'lw-cifp-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-sub-zero (point (car roots))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-circle-first-interior-factor-zero
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (rationalp radius) (< 0 radius) (consp (lw-circle-pole-roots roots radius)))
           (equal (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading)
                                         (car (lw-circle-pole-roots roots radius)) 0)
                  (cons 0 0)))
  :hints (("Goal"
           :use (lw-circle-first-interior-factor-disk lw-cifp-first-interior-product-zero
                 (:instance lw-polynomial-factor-coefficients-evaluation (point (car (lw-circle-pole-roots roots radius)))))
           :in-theory (theory 'lw-cifp-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
