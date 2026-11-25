(in-package "ACL2")

(include-book "mangoldt-divisor-sum")
(include-book "log-multiplication")

; The finite divisor identity with explicit rational evaluation error.
; It uses the actual trial-divisor sum, rather than a supplied prime
; factorization or a symbolic logarithm.

(local (in-theory (disable lw-primep lw-prime-factors lw-divides
                          lw-log-bounds lw-log-rectangles lw-log-count
                          lw-factor-product lw-factor-log-sum lw-mangoldt-divisor-sum)))

(local (defthm lw-mdl-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mdl-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mdl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mdl-log-rational
 (implies (and (rationalp value) (<= 1 value) (rationalp error) (< 0 error))
  (rationalp (car (lw-log-bounds value error))))
 :hints (("Goal" :use ((:instance lw-log-bounds-interval (epsilon error)))
                 :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval))))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-mdl-prime-bound
 (implies (lw-primep value) (and (integerp value) (<= 2 value)))
 :hints (("Goal" :use (lw-primep-lower-bound) :in-theory (disable lw-primep-lower-bound)))
 :rule-classes :forward-chaining))

(local (defthm lw-mdl-zero-step
 (equal (lw-log-rectangles start 0 count) (cons 0 0))
 :hints (("Goal" :induct (lw-log-rectangles start 0 count)
                 :in-theory (enable lw-log-rectangles)))))

(local (defthm lw-mdl-log-one
 (equal (lw-log-bounds 1 error) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-log-bounds)))))

(local (defthm lw-mdl-product-two
 (implies (and (lw-prime-listp items) (consp items)) (<= 2 (lw-factor-product items)))
 :hints (("Goal"
  :use ((:instance lw-prime-list-product-positive (items (cdr items)))
        (:instance lw-primep-lower-bound (value (car items))))
  :expand ((lw-factor-product items))
  :in-theory (disable lw-prime-list-product-positive lw-primep-lower-bound)
  :nonlinearp t :do-not-induct t))))

(defthm lw-factor-log-sum-rational
 (implies (and (lw-prime-listp items) (rationalp error) (< 0 error))
  (rationalp (lw-factor-log-sum items error)))
 :hints (("Goal" :induct (lw-factor-log-sum items error)
                 :in-theory (enable lw-factor-log-sum)))
 :rule-classes (:rewrite :type-prescription))

(local (defun lw-mdl-log-induct (items error product-error)
 (if (consp items) (lw-mdl-log-induct (cdr items) error error) product-error)))

(defthm lw-factor-log-sum-product-error
 (implies (and (lw-prime-listp items) (rationalp error) (< 0 error)
               (rationalp product-error) (< 0 product-error))
  (<= (abs (- (lw-factor-log-sum items error)
              (car (lw-log-bounds (lw-factor-product items) product-error))))
      (+ (* 3 (len items) error) product-error)))
 :hints (("Goal"
  :induct (lw-mdl-log-induct items error product-error)
  :in-theory (enable lw-factor-log-sum lw-factor-product))
  (and stable-under-simplificationp
   '(:use ((:instance lw-mdl-product-two (items (cdr items)))
           (:instance lw-prime-list-product-positive (items (cdr items)))
           (:instance lw-log-lower-multiplication
            (left (car items)) (right (lw-factor-product (cdr items)))
            (left-error error) (right-error error))
           (:instance lw-log-lower-cauchy
            (value (car items)) (left-error error) (right-error product-error)))
     :in-theory (disable lw-factor-log-sum lw-factor-product lw-mdl-product-two
                         lw-prime-list-product-positive lw-log-lower-multiplication lw-log-lower-cauchy)
     :nonlinearp nil :do-not-induct t))))

(defthm lw-mangoldt-divisor-log-error
 (implies (and (posp value) (rationalp error) (< 0 error)
               (rationalp log-error) (< 0 log-error))
  (<= (abs (- (lw-mangoldt-divisor-sum value value error)
              (car (lw-log-bounds value log-error))))
      (+ (* 3 (len (lw-prime-factors value)) error) log-error)))
 :hints (("Goal"
  :use ((:instance lw-factor-log-sum-product-error
         (items (lw-prime-factors value)) (product-error log-error))
        lw-mangoldt-divisor-factor-sum)
  :in-theory (disable lw-factor-log-sum-product-error lw-mangoldt-divisor-factor-sum)
  :do-not-induct t)))

(defun lw-mangoldt-divisor-precision (value error)
 (* error (/ (* 2 (+ 1 (* 3 (len (lw-prime-factors value))))))))

(local (defthm lw-mdl-precision-algebra
 (implies (and (natp count) (rationalp error) (< 0 error))
  (let ((request (* error (/ (* 2 (+ 1 (* 3 count)))))))
   (and (rationalp request) (< 0 request) (<= (* 3 count request) (* 1/2 error)))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x (* 2 (+ 1 (* 3 count)))) )
        (:instance lw-reciprocal-positive (value (* 2 (+ 1 (* 3 count))))))
  :in-theory (disable inverse-of-* lw-reciprocal-positive)
  :nonlinearp t :do-not-induct t))))

(defthm lw-mangoldt-divisor-precision-positive
 (implies (and (rationalp error) (< 0 error))
  (and (rationalp (lw-mangoldt-divisor-precision value error))
       (< 0 (lw-mangoldt-divisor-precision value error))))
 :hints (("Goal" :use ((:instance lw-mdl-precision-algebra (count (len (lw-prime-factors value)))))))
 :rule-classes (:rewrite :type-prescription))

(defthm lw-mangoldt-divisor-log-computed-error
 (implies (and (posp value) (rationalp error) (< 0 error))
  (<= (abs (- (lw-mangoldt-divisor-sum value value (lw-mangoldt-divisor-precision value error))
              (car (lw-log-bounds value (* 1/2 error)))))
      error))
 :hints (("Goal"
  :use ((:instance lw-mangoldt-divisor-log-error
         (error (lw-mangoldt-divisor-precision value error)) (log-error (* 1/2 error)))
        (:instance lw-mdl-precision-algebra (count (len (lw-prime-factors value)))))
  :in-theory (disable lw-mangoldt-divisor-log-error)
  :do-not-induct t)))

