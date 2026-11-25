(in-package "ACL2")

(include-book "complex-exp-boundaries")

(include-book "complex-laplace-moment")

; A height-independent tail bound for both Laplace boundary components.
; Coarse clearance one suffices when the real rate exceeds one.

(local (in-theory
 (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
          lw-complex-reciprocal lw-complex-quotient lw-complex-diskp lw-diskp
          lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-moment-primitive
          lw-complex-exp-clipped-primitive lw-complex-exp-clipped-moment-primitive
          lw-complex-exp-clipped-primitive-endpoint lw-complex-exp-clipped-moment-primitive-endpoint
          lw-complex-laplace-point lw-complex-mul-commutative lw-complex-mul-left-commutes
          lw-complex-mul-subtract lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-cbd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cbd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cbd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cbd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cbd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cbd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cbd-times-negative (a b) (b a)))
                 :in-theory (disable lw-cbd-times-negative)))))

(local (in-theory (disable lw-complex-exp-boundary lw-complex-exp-moment-boundary
 lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary
 lw-complex-norm-square)))

(local (defthm lw-cbd-square-nonnegative
 (implies (rationalp a) (<= 0 (* a a)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cbd-scale-point
 (implies (and (rationalp value) (rationalp rate) (rationalp height))
  (equal (lw-complex-scale value (lw-complex-laplace-point rate height))
         (cons (- (* rate value)) (- (* height value)))))
 :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-cbd-reciprocal-unit
 (implies (and (rationalp rate) (< 1 rate) (rationalp height))
  (lw-complex-diskp (lw-complex-reciprocal (cons rate height)) 1))
 :hints (("Goal"
  :use ((:instance lw-complex-reciprocal-disk-bound (point (cons rate height)) (lower 1))
        (:instance lw-cbd-square-nonnegative (a height)))
  :in-theory (e/d (lw-complexp lw-complex-norm-square) (lw-complex-reciprocal-disk-bound))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defun lw-complex-boundary-decay-radius (value error)
 (+ (* 8 (/ value)) (* 2 (+ 1 value) error)))

(local (in-theory (disable lw-complex-boundary-decay-radius)))

(local (defthm lw-cbd-quadratic-budget
 (implies (and (rationalp rate) (< 1 rate) (rationalp value) (<= 1 value))
  (<= (* (+ 1 value) (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value))))) (* 8 (/ value))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound
         (numerator (+ 1 value))
         (divisor (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value))))
         (bound (* 8 (/ value))))
        (:instance inverse-of-* (x value)))
  :in-theory (disable inverse-of-*) :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-cbd-radius-data
 (implies (and (rationalp rate) (< 1 rate) (rationalp value) (<= 1 value)
               (rationalp error) (< 0 error))
  (and (rationalp (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error))) (<= 0 (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error))) (rationalp (lw-complex-boundary-decay-radius value error)) (<= 0 (lw-complex-boundary-decay-radius value error))
       (<= (* (+ 1 value) (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error))) (lw-complex-boundary-decay-radius value error))))
 :hints (("Goal"
  :use (lw-cbd-quadratic-budget)
  :in-theory (enable lw-complex-boundary-decay-radius)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-exp-laplace-boundaries-decay
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp value) (<= 1 value)
       (rationalp error) (< 0 error))
  (and (lw-complex-diskp (lw-complex-exp-boundary (lw-complex-laplace-point rate height) value error) (lw-complex-boundary-decay-radius value error))
       (lw-complex-diskp (lw-complex-exp-moment-boundary (lw-complex-laplace-point rate height) value error) (lw-complex-boundary-decay-radius value error))))
 :hints (("Goal"
  :use (lw-cbd-reciprocal-unit lw-cbd-radius-data
        lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary
        (:instance lw-complex-exp-damped-quadratic-decay (value (* rate value)) (angle (- (* height value))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-reciprocal (cons rate height))) (radius 1) (cap (+ 1 value)))
        (:instance lw-complex-scale-disk (point (lw-complex-reciprocal (cons rate height))) (radius 1) (factor value))
        (:instance lw-complex-mul-disk (left (lw-complex-reciprocal (cons rate height))) (right (lw-complex-reciprocal (cons rate height))) (radius 1) (other-radius 1))
        (:instance lw-complex-add-disk
         (left (lw-complex-scale value (lw-complex-reciprocal (cons rate height)))) (right (lw-complex-mul (lw-complex-reciprocal (cons rate height)) (lw-complex-reciprocal (cons rate height))))
         (radius value) (other-radius 1))
        (:instance lw-complex-mul-disk (left (lw-complex-exp-value (lw-complex-scale value (lw-complex-laplace-point rate height)) error)) (right (lw-complex-reciprocal (cons rate height))) (radius (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error))) (other-radius (+ 1 value)))
        (:instance lw-complex-mul-disk (left (lw-complex-exp-value (lw-complex-scale value (lw-complex-laplace-point rate height)) error)) (right (lw-complex-add (lw-complex-scale value (lw-complex-reciprocal (cons rate height))) (lw-complex-mul (lw-complex-reciprocal (cons rate height)) (lw-complex-reciprocal (cons rate height))))) (radius (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error))) (other-radius (+ 1 value)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-mul (lw-complex-exp-value (lw-complex-scale value (lw-complex-laplace-point rate height)) error) (lw-complex-reciprocal (cons rate height))))
         (radius (* (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error)) (+ 1 value))) (cap (lw-complex-boundary-decay-radius value error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-mul (lw-complex-exp-value (lw-complex-scale value (lw-complex-laplace-point rate height)) error) (lw-complex-add (lw-complex-scale value (lw-complex-reciprocal (cons rate height))) (lw-complex-mul (lw-complex-reciprocal (cons rate height)) (lw-complex-reciprocal (cons rate height))))))
         (radius (* (+ (/ (* (+ 1 (* 1/2 rate value)) (+ 1 (* 1/2 rate value)))) (* 2 error)) (+ 1 value))) (cap (lw-complex-boundary-decay-radius value error))))
  :in-theory (disable lw-complex-exp-laplace-boundary lw-complex-exp-laplace-moment-boundary
                      lw-complex-exp-damped-quadratic-decay lw-complex-scale-disk
                      lw-complex-add-disk lw-complex-mul-disk lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t)))
