(in-package "ACL2")

(include-book "complex-damped-product")

(include-book "complex-exp-increment")

(include-book "complex-laplace-basis")

; Uniform spatial transport in the closed negative half-plane.
; Small increments use the damped product law; large ones use unit caps.
; The roundoff factor is fixed, independent of the base point and height.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-exp-value lw-complex-exp-cap lw-complex-l1
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-lipschitz-cap
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-disk-enlarge lw-disk-enlarge lw-disk-gap-error lw-complex-norm-square
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract
                 lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-dct-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-dct-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dct-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-dct-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-dct-times-negative (a b) (b a)))
                         :in-theory (disable lw-dct-times-negative)))))

(local (defthm lw-dct-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-dct-double
         (equal (+ a a) (* 2 a))
         :hints (("Goal" :cases ((acl2-numberp a))))))

(local (defthm lw-dct-add-double
         (equal (+ a (+ a b)) (+ (* 2 a) b))
         :hints (("Goal" :cases ((acl2-numberp a))))))

(local (defthm lw-dct-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (in-theory (disable lw-complex-damped-product lw-complex-damped-product-bound
 lw-complex-exp-uniform-cap lw-complex-laplace-point)))

(local (defthm lw-dct-multiply-order
 (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
  (<= (* a factor) (* b factor)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-dct-unit-cap
 (<= (lw-complex-exp-uniform-cap 1) 8)
 :hints (("Goal" :in-theory (enable (:executable-counterpart lw-complex-exp-uniform-cap))))
 :rule-classes nil))

(local (defthm lw-dct-small-cap
 (implies (and (lw-complexp left) (<= (lw-complex-l1 left) 1))
  (<= (lw-complex-exp-cap left) 8))
 :hints (("Goal"
  :use (lw-dct-unit-cap (:instance lw-complex-exp-cap-uniform (point left) (argument-cap 1)))
  :in-theory (disable lw-complex-exp-cap-uniform) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dct-expm1-telescope
 (implies (lw-complexp point)
  (equal (lw-complex-sub a (cons 1 0))
   (lw-complex-add (lw-complex-sub a (lw-complex-add (cons 1 0) point)) point)))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))
 :rule-classes nil))

(local (defthm lw-dct-expm1
 (implies
  (and (lw-complexp point) (<= (lw-complex-l1 point) 1) (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-value point error) (cons 1 0))
                   (+ (* 2 (lw-complex-l1 point)) error)))
 :hints (("Goal"
  :use (lw-complex-l1-bound
        (:instance lw-complex-exp-first-order-error (radius (lw-complex-l1 point)))
        (:instance lw-dct-expm1-telescope (a (lw-complex-exp-value point error)))
        (:instance lw-dct-multiply-order (a (lw-complex-l1 point)) (b 1) (factor (lw-complex-l1 point)))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub (lw-complex-exp-value point error) (lw-complex-add (cons 1 0) point)))
         (right point)
         (radius (+ (* (lw-complex-l1 point) (lw-complex-l1 point)) error))
         (other-radius (lw-complex-l1 point)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-exp-value point error) (cons 1 0)))
         (radius (+ (* (lw-complex-l1 point) (lw-complex-l1 point)) error (lw-complex-l1 point)))
         (cap (+ (* 2 (lw-complex-l1 point)) error))))
  :in-theory (disable lw-complex-l1-bound lw-complex-exp-first-order-error lw-complex-add-disk)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dct-three-comparisons
         (implies
          (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (lw-complex-diskp (lw-complex-sub a b) first)
               (lw-complex-diskp (lw-complex-sub b c) second)
               (lw-complex-diskp (lw-complex-sub c d) third))
          (lw-complex-diskp (lw-complex-sub a d) (+ first second third)))
         :hints (("Goal"
                  :use ((:instance lw-complex-difference-triangle
                          (left a) (middle b) (right c) (radius first) (other-radius second))
                        (:instance lw-complex-difference-triangle
                          (left a) (middle c) (right d) (radius (+ first second)) (other-radius third)))
                  :in-theory (disable lw-complex-difference-triangle) :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-dct-sum-complex
         (implies (and (lw-complexp left) (rationalp value) (rationalp angle))
                  (lw-complexp (lw-complex-add left (cons (- value) angle))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(local (defthm lw-dct-product-minus-unit
 (implies (lw-complexp b)
  (equal (lw-complex-sub (lw-complex-mul a b) b)
         (lw-complex-mul (lw-complex-sub a (cons 1 0)) b)))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-mul)))))

(local (defthm lw-dct-small-increment-transport
 (implies
  (and (lw-complexp left) (<= (lw-complex-l1 left) 1) (rationalp value) (<= 0 value) (rationalp angle)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) left-error) (lw-complex-exp-value (cons (- value) angle) right-error)) (+ (* 2 (lw-complex-l1 left)) (* 32 (+ left-error right-error)))))
 :hints (("Goal"
  :use (lw-dct-small-cap lw-dct-sum-complex
        (:instance lw-complex-l1-bound (point left))
        (:instance lw-complex-exp-value-rational (point left) (error (+ left-error right-error)))
        (:instance lw-complex-exp-value-rational (point (lw-complex-add left (cons (- value) angle))) (error left-error))
        (:instance lw-complex-exp-value-rational (point (cons (- value) angle)) (error right-error))
        (:instance lw-complex-damped-product-rational (left-error (+ left-error right-error)) (negative-error (+ left-error right-error)) (phase-error (+ left-error right-error)))
        (:instance lw-damped-phase-sample-unit (negative-error (+ left-error right-error)) (phase-error (+ left-error right-error)))
        (:instance lw-complex-damped-product-agreement
         (left-error (+ left-error right-error)) (negative-error (+ left-error right-error)) (phase-error (+ left-error right-error)) (complex-error left-error))
        (:instance lw-complex-difference-symmetric (left (lw-complex-damped-product left value angle (+ left-error right-error) (+ left-error right-error) (+ left-error right-error))) (right (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) left-error)) (radius (lw-complex-damped-product-bound left (+ left-error right-error) (+ left-error right-error) (+ left-error right-error) left-error)))
        (:instance lw-dct-expm1 (point left) (error (+ left-error right-error)))
        (:instance lw-complex-mul-disk (left (lw-complex-sub (lw-complex-exp-value left (+ left-error right-error)) (cons 1 0))) (right (lw-damped-phase-sample value angle (+ left-error right-error) (+ left-error right-error)))
         (radius (+ (* 2 (lw-complex-l1 left)) (+ left-error right-error))) (other-radius 1))
        (:instance lw-complex-exp-kernel-agreement (negative-error (+ left-error right-error)) (phase-error (+ left-error right-error)) (complex-error right-error))
        (:instance lw-dct-three-comparisons (a (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) left-error)) (b (lw-complex-damped-product left value angle (+ left-error right-error) (+ left-error right-error) (+ left-error right-error))) (c (lw-damped-phase-sample value angle (+ left-error right-error) (+ left-error right-error))) (d (lw-complex-exp-value (cons (- value) angle) right-error))
         (first (lw-complex-damped-product-bound left (+ left-error right-error) (+ left-error right-error) (+ left-error right-error) left-error)) (second (+ (* 2 (lw-complex-l1 left)) (+ left-error right-error))) (third (+ (+ left-error right-error) (+ left-error right-error) right-error)))
        (:instance lw-dct-multiply-order
         (a (lw-complex-exp-cap left)) (b 8) (factor (+ (+ left-error right-error) (+ left-error right-error))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-exp-value (lw-complex-add left (cons (- value) angle)) left-error) (lw-complex-exp-value (cons (- value) angle) right-error))) (radius (+ (lw-complex-damped-product-bound left (+ left-error right-error) (+ left-error right-error) (+ left-error right-error) left-error) (+ (* 2 (lw-complex-l1 left)) (+ left-error right-error)) (+ (+ left-error right-error) (+ left-error right-error) right-error))) (cap (+ (* 2 (lw-complex-l1 left)) (* 32 (+ left-error right-error))))))
  :in-theory (e/d (lw-complex-damped-product lw-complex-damped-product-bound)
    (lw-complex-l1-bound lw-complex-exp-value-rational lw-complex-damped-product-rational
     lw-damped-phase-sample-unit lw-complex-damped-product-agreement lw-complex-mul-disk
     lw-complex-exp-kernel-agreement lw-complex-disk-enlarge))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-dct-increment-form
 (implies
  (and (rationalp left-value) (rationalp right-value) (rationalp left-angle) (rationalp right-angle))
  (and (lw-complexp (cons (- (- left-value right-value)) (- left-angle right-angle)))
       (equal (lw-complex-add (cons (- (- left-value right-value)) (- left-angle right-angle)) (cons (- right-value) right-angle)) (cons (- left-value) left-angle))
       (equal (lw-complex-l1 (cons (- (- left-value right-value)) (- left-angle right-angle))) (+ (abs (- left-value right-value)) (abs (- left-angle right-angle))))))
 :hints (("Goal" :cases ((<= left-value right-value))
                 :in-theory (enable lw-complexp lw-complex-add lw-complex-l1 abs)))
 :rule-classes nil))

(defthm lw-complex-exp-damped-spatial-cauchy
 (implies
  (and (rationalp left-value) (<= 0 left-value) (rationalp right-value) (<= 0 right-value)
       (rationalp left-angle) (rationalp right-angle)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-value (cons (- left-value) left-angle) left-error)
                   (lw-complex-exp-value (cons (- right-value) right-angle) right-error)) (+ (* 2 (+ (abs (- left-value right-value)) (abs (- left-angle right-angle)))) (* 32 (+ left-error right-error)))))
 :hints (("Goal"
  :cases ((<= (+ (abs (- left-value right-value)) (abs (- left-angle right-angle))) 1))
  :use (lw-dct-increment-form
        (:instance lw-dct-small-increment-transport
         (left (cons (- (- left-value right-value)) (- left-angle right-angle))) (value right-value) (angle right-angle))
        (:instance lw-complex-exp-damped-cap (value left-value) (angle left-angle) (error left-error))
        (:instance lw-complex-exp-damped-cap (value right-value) (angle right-angle) (error right-error))
        (:instance lw-complex-sub-disk
         (left (lw-complex-exp-value (cons (- left-value) left-angle) left-error))
         (right (lw-complex-exp-value (cons (- right-value) right-angle) right-error))
         (radius (+ 1 left-error)) (other-radius (+ 1 right-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-exp-value (cons (- left-value) left-angle) left-error)
                   (lw-complex-exp-value (cons (- right-value) right-angle) right-error)))
         (radius (+ (+ 1 left-error) (+ 1 right-error))) (cap (+ (* 2 (+ (abs (- left-value right-value)) (abs (- left-angle right-angle)))) (* 32 (+ left-error right-error))))))
  :in-theory (disable lw-complex-exp-damped-cap lw-complex-sub-disk)
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-dct-scale-laplace
 (implies (and (rationalp rate) (rationalp height) (rationalp value))
  (equal (lw-complex-scale value (lw-complex-laplace-point rate height)) (cons (- (* rate value)) (- (* height value)))))
 :hints (("Goal" :in-theory (enable lw-complex-scale lw-complex-laplace-point)))))

(local (defthm lw-dct-laplace-distance
 (implies
  (and (rationalp rate) (<= 0 rate) (rationalp height) (rationalp left) (rationalp right))
  (equal (+ (abs (- (* rate left) (* rate right))) (abs (- (- (* height left)) (- (* height right)))))
         (* (+ rate (abs height)) (abs (- left right)))))
 :hints (("Goal" :cases ((<= left right) (<= 0 height)) :in-theory (enable abs) :nonlinearp t))
 :rule-classes nil))

(defthm lw-complex-laplace-spatial-cauchy
 (implies
  (and (rationalp rate) (<= 0 rate) (rationalp height)
       (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-exp-value (lw-complex-scale left (lw-complex-laplace-point rate height)) left-error)
                   (lw-complex-exp-value (lw-complex-scale right (lw-complex-laplace-point rate height)) right-error)) (+ (* 2 (+ rate (abs height)) (abs (- left right))) (* 32 (+ left-error right-error)))))
 :hints (("Goal"
  :use (lw-dct-laplace-distance
        (:instance lw-complex-exp-damped-spatial-cauchy
         (left-value (* rate left)) (right-value (* rate right))
         (left-angle (- (* height left))) (right-angle (- (* height right))))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-exp-value (lw-complex-scale left (lw-complex-laplace-point rate height)) left-error)
                   (lw-complex-exp-value (lw-complex-scale right (lw-complex-laplace-point rate height)) right-error))) (radius (+ (* 2 (+ (abs (- (* rate left) (* rate right))) (abs (- (- (* height left)) (- (* height right)))))) (* 32 (+ left-error right-error)))) (cap (+ (* 2 (+ rate (abs height)) (abs (- left right))) (* 32 (+ left-error right-error))))))
  :in-theory (disable lw-complex-exp-damped-spatial-cauchy)
  :nonlinearp t :do-not-induct t)))
