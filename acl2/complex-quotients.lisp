(in-package "ACL2")

(include-book "pole-resolvents")
(include-book "complex-exp-multiply")

; Quantitative division for constructing logarithmic-derivative models.
; Both denominator clearances are checked numerically; neither a quotient
; approximation nor a coefficient identity is assumed.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-conjugate lw-complex-norm-square
                 lw-complex-reciprocal lw-complex-power lw-rational-power
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract)))

(local (defthm lw-cq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(defun lw-complex-quotient (numerator denominator)
  (lw-complex-mul numerator (lw-complex-reciprocal denominator)))

(defthm lw-complex-quotient-rational
  (implies (and (lw-complexp numerator) (lw-complexp denominator))
           (lw-complexp (lw-complex-quotient numerator denominator))))

(local (defthm lw-cq-difference-times-left
         (implies (and (lw-complexp a) (lw-complexp b)
                       (not (equal a (cons 0 0))) (not (equal b (cons 0 0))))
                  (equal
                   (lw-complex-mul a
                     (lw-complex-sub (lw-complex-reciprocal a) (lw-complex-reciprocal b)))
                   (lw-complex-mul (lw-complex-sub b a) (lw-complex-reciprocal b))))
         :hints (("Goal"
                  :use ((:instance lw-complex-mul-subtract (b (lw-complex-reciprocal a))
                                  (c (lw-complex-reciprocal b)))
                        (:instance lw-complex-mul-subtract
                          (a (lw-complex-reciprocal b)) (b b) (c a))
                        (:instance lw-complex-mul-commutative (left a)
                          (right (lw-complex-reciprocal b)))
                        (:instance lw-complex-mul-commutative
                          (left (lw-complex-sub b a)) (right (lw-complex-reciprocal b))))
                  :in-theory (disable lw-complex-mul-distribute)))))

(defthm lw-complex-reciprocal-difference
  (implies (and (lw-complexp a) (lw-complexp b)
                (not (equal a (cons 0 0))) (not (equal b (cons 0 0))))
           (equal
            (lw-complex-sub (lw-complex-reciprocal a) (lw-complex-reciprocal b))
            (lw-complex-mul (lw-complex-reciprocal a)
              (lw-complex-mul (lw-complex-sub b a) (lw-complex-reciprocal b)))))
  :hints (("Goal"
           :use (lw-cq-difference-times-left
                 (:instance lw-complex-linear-solve
                   (b (lw-complex-sub (lw-complex-reciprocal a) (lw-complex-reciprocal b)))
                   (c (lw-complex-mul (lw-complex-sub b a) (lw-complex-reciprocal b)))))
           :in-theory (disable lw-cq-difference-times-left))))

(local (in-theory (disable lw-complex-reciprocal-difference)))

(defthm lw-complex-reciprocal-difference-bound
  (implies (and (lw-complexp a) (lw-complexp b)
                (rationalp left-clearance) (< 0 left-clearance)
                (<= (* left-clearance left-clearance) (lw-complex-norm-square a))
                (rationalp right-clearance) (< 0 right-clearance)
                (<= (* right-clearance right-clearance) (lw-complex-norm-square b))
                (lw-complex-diskp (lw-complex-sub a b) error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-reciprocal a) (lw-complex-reciprocal b))
            (* (/ left-clearance) (/ right-clearance) error)))
  :hints (("Goal"
           :use (lw-complex-reciprocal-difference
                 (:instance lw-complex-reciprocal-disk-bound (point a) (lower left-clearance))
                 (:instance lw-complex-reciprocal-disk-bound (point b) (lower right-clearance))
                 (:instance lw-complex-difference-symmetric (left a) (right b) (radius error))
                 (:instance lw-complex-mul-disk
                   (left (lw-complex-sub b a)) (radius error)
                   (right (lw-complex-reciprocal b)) (other-radius (/ right-clearance)))
                 (:instance lw-complex-mul-disk
                   (left (lw-complex-reciprocal a)) (radius (/ left-clearance))
                   (right (lw-complex-mul (lw-complex-sub b a) (lw-complex-reciprocal b)))
                   (other-radius (* error (/ right-clearance)))))
           :in-theory (disable lw-complex-mul-disk lw-complex-reciprocal-disk-bound))))

(defthm lw-complex-quotient-difference-bound
  (implies (and (lw-complexp numerator) (lw-complexp denominator)
                (lw-complexp approximate-numerator) (lw-complexp approximate-denominator)
                (rationalp left-clearance) (< 0 left-clearance)
                (<= (* left-clearance left-clearance) (lw-complex-norm-square denominator))
                (rationalp right-clearance) (< 0 right-clearance)
                (<= (* right-clearance right-clearance)
                    (lw-complex-norm-square approximate-denominator))
                (lw-complex-diskp approximate-numerator numerator-cap)
                (lw-complex-diskp (lw-complex-sub numerator approximate-numerator) numerator-error)
                (lw-complex-diskp (lw-complex-sub denominator approximate-denominator)
                                 denominator-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-quotient numerator denominator)
                            (lw-complex-quotient approximate-numerator approximate-denominator))
            (+ (* (/ left-clearance) numerator-error)
               (* numerator-cap (/ left-clearance) (/ right-clearance) denominator-error))))
  :hints (("Goal"
           :use ((:instance lw-complex-reciprocal-disk-bound
                   (point denominator) (lower left-clearance))
                 (:instance lw-complex-reciprocal-difference-bound
                   (a denominator) (b approximate-denominator) (error denominator-error))
                 (:instance lw-complex-mul-difference-bound
                   (a numerator) (b (lw-complex-reciprocal denominator))
                   (c approximate-numerator) (d (lw-complex-reciprocal approximate-denominator))
                   (right-cap (/ left-clearance)) (left-cap numerator-cap)
                   (left-error numerator-error)
                   (right-error (* (/ left-clearance) (/ right-clearance) denominator-error))))
           :in-theory (disable lw-complex-reciprocal-disk-bound
                               lw-complex-reciprocal-difference-bound
                               lw-complex-mul-difference-bound))))

(local (in-theory (disable lw-complex-quotient)))

(defun lw-complex-quotient-gain (left-clearance right-clearance numerator-cap)
  (+ (/ left-clearance) (* numerator-cap (/ left-clearance) (/ right-clearance))))

(defun lw-complex-quotient-precision (left-clearance right-clearance numerator-cap error)
  (/ error (* 2 (+ 1 (lw-complex-quotient-gain left-clearance right-clearance numerator-cap)))))

(local (defthm lw-cq-scaled-precision
         (implies (and (rationalp gain) (<= 0 gain) (rationalp error) (< 0 error))
                  (and (< 0 (/ error (* 2 (+ 1 gain))))
                       (<= (* gain (/ error (* 2 (+ 1 gain)))) (* 1/2 error))))
         :hints (("Goal"
                  :use ((:instance lw-positive-division-bound (numerator (* gain error))
                          (divisor (* 2 (+ 1 gain))) (bound (* 1/2 error))))
                  :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-quotient-precision-adequate
  (implies (and (rationalp left-clearance) (< 0 left-clearance)
                (rationalp right-clearance) (< 0 right-clearance)
                (rationalp numerator-cap) (<= 0 numerator-cap)
                (rationalp error) (< 0 error))
           (and
            (rationalp (lw-complex-quotient-precision
                         left-clearance right-clearance numerator-cap error))
            (< 0 (lw-complex-quotient-precision
                   left-clearance right-clearance numerator-cap error))
            (<= (* (lw-complex-quotient-gain left-clearance right-clearance numerator-cap)
                   (lw-complex-quotient-precision
                     left-clearance right-clearance numerator-cap error)) (* 1/2 error))))
  :hints (("Goal"
           :use ((:instance lw-cq-scaled-precision
                   (gain (lw-complex-quotient-gain
                           left-clearance right-clearance numerator-cap))))
           :nonlinearp t)))

(defthm lw-complex-quotient-computed-error
  (implies
   (and (lw-complexp numerator) (lw-complexp denominator)
        (lw-complexp approximate-numerator) (lw-complexp approximate-denominator)
        (rationalp left-clearance) (< 0 left-clearance)
        (<= (* left-clearance left-clearance) (lw-complex-norm-square denominator))
        (rationalp right-clearance) (< 0 right-clearance)
        (<= (* right-clearance right-clearance) (lw-complex-norm-square approximate-denominator))
        (lw-complex-diskp approximate-numerator numerator-cap)
        (rationalp error) (< 0 error)
        (lw-complex-diskp (lw-complex-sub numerator approximate-numerator)
          (lw-complex-quotient-precision left-clearance right-clearance numerator-cap error))
        (lw-complex-diskp (lw-complex-sub denominator approximate-denominator)
          (lw-complex-quotient-precision left-clearance right-clearance numerator-cap error)))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-quotient numerator denominator)
                    (lw-complex-quotient approximate-numerator approximate-denominator)) error))
  :hints (("Goal"
           :use (lw-complex-quotient-precision-adequate
                 (:instance lw-complex-quotient-difference-bound
                   (numerator-error (lw-complex-quotient-precision
                                      left-clearance right-clearance numerator-cap error))
                   (denominator-error (lw-complex-quotient-precision
                                        left-clearance right-clearance numerator-cap error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-quotient numerator denominator)
                           (lw-complex-quotient approximate-numerator approximate-denominator)))
                   (radius (* (lw-complex-quotient-gain
                                left-clearance right-clearance numerator-cap)
                              (lw-complex-quotient-precision
                                left-clearance right-clearance numerator-cap error)))
                   (cap error)))
           :in-theory (disable lw-complex-quotient-precision lw-complex-quotient-difference-bound
                               lw-complex-quotient-precision-adequate)
           :nonlinearp t :do-not-induct t)))

(defthm lw-complex-quotient-product-rule
  (implies (and (lw-complexp p) (lw-complexp h) (lw-complexp dp) (lw-complexp dh)
                (not (equal p (cons 0 0))) (not (equal h (cons 0 0))))
           (equal
            (lw-complex-quotient
              (lw-complex-add (lw-complex-mul dp h) (lw-complex-mul p dh)) (lw-complex-mul p h))
            (lw-complex-add (lw-complex-quotient dp p) (lw-complex-quotient dh h))))
  :hints (("Goal"
           :use ((:instance lw-complex-reciprocal-product (a p) (b h)))
           :in-theory (enable lw-complex-quotient lw-complex-mul-add-left
                              lw-complex-mul-commutative lw-complex-mul-left-commutes
                              lw-complex-reciprocal-product)
           :do-not-induct t)))

(defthm lw-complex-factor-log-derivative-bound
  (implies
   (and (lw-complexp value) (lw-complexp derivative)
        (lw-complexp p) (lw-complexp h) (lw-complexp dp) (lw-complexp dh)
        (not (equal p (cons 0 0))) (not (equal h (cons 0 0)))
        (rationalp left-clearance) (< 0 left-clearance)
        (<= (* left-clearance left-clearance) (lw-complex-norm-square value))
        (rationalp right-clearance) (< 0 right-clearance)
        (<= (* right-clearance right-clearance)
            (lw-complex-norm-square (lw-complex-mul p h)))
        (lw-complex-diskp (lw-complex-add (lw-complex-mul dp h) (lw-complex-mul p dh))
                         numerator-cap)
        (lw-complex-diskp
          (lw-complex-sub derivative
            (lw-complex-add (lw-complex-mul dp h) (lw-complex-mul p dh))) derivative-error)
        (lw-complex-diskp (lw-complex-sub value (lw-complex-mul p h)) value-error))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-quotient derivative value)
      (lw-complex-add (lw-complex-quotient dp p) (lw-complex-quotient dh h)))
    (+ (* (/ left-clearance) derivative-error)
       (* numerator-cap (/ left-clearance) (/ right-clearance) value-error))))
  :hints (("Goal"
           :use ((:instance lw-complex-quotient-difference-bound
                   (numerator derivative) (denominator value)
                   (approximate-numerator
                     (lw-complex-add (lw-complex-mul dp h) (lw-complex-mul p dh)))
                   (approximate-denominator (lw-complex-mul p h))
                   (numerator-error derivative-error) (denominator-error value-error))
                 lw-complex-quotient-product-rule)
           :in-theory (disable lw-complex-quotient-difference-bound
                               lw-complex-quotient-product-rule)
           :do-not-induct t)))
