(in-package "ACL2")

(include-book "complex-exp-dyadic-moment-grid")

(include-book "complex-laplace-shifted")

; Exact finite boundary identities. Keeping the upper evaluation at
; max(end,cutpoint) also handles every cutpoint beyond the interval.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-reciprocal lw-complex-quotient lw-complex-diskp lw-diskp
          lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-moment-primitive
          lw-complex-exp-clipped-primitive lw-complex-exp-clipped-moment-primitive
          lw-complex-exp-clipped-primitive-endpoint lw-complex-exp-clipped-moment-primitive-endpoint
          lw-complex-laplace-point lw-complex-mul-commutative lw-complex-mul-left-commutes
          lw-complex-mul-subtract lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-ceb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ceb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ceb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ceb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ceb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))
(local (defthm lw-ceb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ceb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ceb-times-negative)))))

(defun lw-complex-exp-boundary (point value error)
 (lw-complex-scale -1
  (lw-complex-quotient (lw-complex-exp-value (lw-complex-scale value point) error) point)))

(defun lw-complex-exp-moment-boundary (point value error)
 (let ((boundary (lw-complex-exp-boundary point value error)))
  (lw-complex-sub (lw-complex-scale value boundary) (lw-complex-quotient boundary point))))

(local (in-theory (disable lw-complex-exp-boundary lw-complex-exp-moment-boundary)))

(defthm lw-complex-exp-boundaries-rational
 (implies (and (lw-complexp point) (rationalp value) (rationalp error) (< 0 error))
  (and (lw-complexp (lw-complex-exp-boundary point value error))
       (lw-complexp (lw-complex-exp-moment-boundary point value error))))
 :hints (("Goal"
   :use ((:instance lw-complex-exp-value-rational (point (lw-complex-scale value point)))
         lw-complex-reciprocal-rational)
   :in-theory (e/d (lw-complex-exp-boundary lw-complex-exp-moment-boundary lw-complex-quotient
                   lw-complexp lw-complex-sub lw-complex-scale lw-complex-mul)
                  (lw-complex-exp-value-rational lw-complex-reciprocal-rational))
   :do-not-induct t)))

(defthm lw-complex-exp-primitive-boundaries
 (equal
  (lw-complex-exp-primitive-value point start end error)
  (lw-complex-sub (lw-complex-exp-boundary point start error) (lw-complex-exp-boundary point end error)))
 :hints (("Goal"
   :in-theory (enable lw-complex-exp-primitive-value lw-complex-exp-boundary lw-complex-quotient
                      lw-complex-sub lw-complex-scale lw-complex-mul)
   :do-not-induct t)))

(defthm lw-complex-exp-moment-primitive-boundaries
 (equal
  (lw-complex-exp-moment-primitive point start end error)
  (lw-complex-sub (lw-complex-exp-moment-boundary point start error)
                  (lw-complex-exp-moment-boundary point end error)))
 :hints (("Goal"
   :in-theory (enable lw-complex-exp-primitive-value lw-complex-exp-moment-primitive
                      lw-complex-exp-boundary lw-complex-exp-moment-boundary lw-complex-quotient
                      lw-complex-sub lw-complex-scale lw-complex-mul)
   :do-not-induct t)))

(defthm lw-complex-exp-clipped-primitive-boundaries
 (equal
  (lw-complex-exp-clipped-primitive point start end cutpoint error)
  (lw-complex-sub
   (lw-complex-exp-boundary point (max start cutpoint) error)
   (lw-complex-exp-boundary point (max end cutpoint) error)))
 :hints (("Goal" :in-theory (enable lw-complex-exp-clipped-primitive) :do-not-induct t)))

(defthm lw-complex-exp-clipped-moment-primitive-boundaries
 (equal
  (lw-complex-exp-clipped-moment-primitive point start end cutpoint error)
  (lw-complex-sub
   (lw-complex-exp-moment-boundary point (max start cutpoint) error)
   (lw-complex-exp-moment-boundary point (max end cutpoint) error)))
 :hints (("Goal" :in-theory (enable lw-complex-exp-clipped-moment-primitive) :do-not-induct t)))

(defthm lw-complex-exp-laplace-boundary
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
  (equal
   (lw-complex-exp-boundary (lw-complex-laplace-point rate height) value error)
   (lw-complex-mul
    (lw-complex-exp-value (lw-complex-scale value (lw-complex-laplace-point rate height)) error)
    (lw-complex-reciprocal (cons rate height)))))
 :hints (("Goal" :use (lw-complex-laplace-point-data)
   :in-theory (e/d (lw-complex-exp-boundary lw-complex-quotient)
     (lw-complex-laplace-point-data lw-complex-mul-commutative lw-complex-mul-left-commutes))
   :nonlinearp t :do-not-induct t)))

(defthm lw-complex-exp-boundaries-at-zero
 (implies (and (lw-complexp point) (rationalp error) (< 0 error))
  (and
   (equal (lw-complex-exp-boundary point 0 error) (lw-complex-scale -1 (lw-complex-reciprocal point)))
   (equal (lw-complex-exp-moment-boundary point 0 error)
          (lw-complex-mul (lw-complex-reciprocal point) (lw-complex-reciprocal point)))))
 :hints (("Goal"
   :use (lw-complex-reciprocal-rational lw-complex-exp-value-zero)
   :in-theory (e/d (lw-complex-exp-boundary lw-complex-exp-moment-boundary lw-complex-quotient
                   lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale)
     (lw-complex-reciprocal-rational lw-complex-exp-value-zero lw-complex-exp-laplace-boundary))
   :do-not-induct t)))

(defthm lw-complex-exp-laplace-moment-boundary
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
  (equal
   (lw-complex-exp-moment-boundary (lw-complex-laplace-point rate height) value error)
   (lw-complex-mul
    (lw-complex-exp-value (lw-complex-scale value (lw-complex-laplace-point rate height)) error)
    (lw-complex-add
     (lw-complex-scale value (lw-complex-reciprocal (cons rate height)))
     (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                     (lw-complex-reciprocal (cons rate height)))))))
 :hints (("Goal"
   :use (lw-complex-laplace-point-data
         (:instance lw-complex-reciprocal-rational (point (lw-complex-laplace-point rate height)))
         (:instance lw-complex-reciprocal-rational (point (cons rate height)))
         (:instance lw-complex-exp-value-rational
          (point (lw-complex-scale value (lw-complex-laplace-point rate height)))))
   :in-theory (e/d (lw-complex-exp-boundary lw-complex-exp-moment-boundary lw-complex-quotient
                   lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale lw-complex-laplace-point)
     (lw-complex-laplace-point-data lw-complex-reciprocal-rational lw-complex-exp-value-rational
      lw-complex-exp-laplace-boundary))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-laplace-boundaries-at-zero
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (rationalp error) (< 0 error))
  (and
   (equal (lw-complex-exp-boundary (lw-complex-laplace-point rate height) 0 error)
          (lw-complex-reciprocal (cons rate height)))
   (equal (lw-complex-exp-moment-boundary (lw-complex-laplace-point rate height) 0 error)
          (lw-complex-mul (lw-complex-reciprocal (cons rate height))
                          (lw-complex-reciprocal (cons rate height))))))
 :hints (("Goal"
   :use (lw-complex-laplace-point-data
         (:instance lw-complex-reciprocal-rational (point (cons rate height)))
         lw-complex-exp-value-zero
         (:instance lw-complex-exp-laplace-boundary (value 0))
         (:instance lw-complex-exp-laplace-moment-boundary (value 0)))
   :in-theory (e/d (lw-complexp lw-complex-add lw-complex-mul lw-complex-scale)
     (lw-complex-laplace-point-data lw-complex-reciprocal-rational lw-complex-exp-value-zero
      lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary lw-complex-exp-boundaries-at-zero))
   :do-not-induct t)))


