(in-package "ACL2")

(include-book "kernel-bounds")
(include-book "exp-continuity")

(local (in-theory
        (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-neg-bounds
                 lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap lw-exp-neg-bounds-overlap
                 lw-exp-lipschitz-cap lw-exp-lipschitz-cap-valid
                 lw-exp-neg-bounds-valid lw-exp-neg-bounds-transport
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-kernel-weight-bounds-valid lw-kernel-weight-bounds-width lw-kernel-weight-bounds-overlap)))

(local (defthm lw-kc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-kc-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kc-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))
         :hints (("Goal" :use ((:instance lw-kc-times-negative (a b) (b a)))
                         :in-theory (disable lw-kc-times-negative)))))
(local (defthm lw-kc-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kc-times-zero (equal (* 0 a) 0)))
(local (defthm lw-kc-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-kc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-kc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c))
                  (<= (* a c) (* b c)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-kc-abs-scale
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (<= 0 factor))
                  (equal (abs (- (* factor a) (* factor b))) (* factor (abs (- a b)))))
         :hints (("Goal" :cases ((<= a b)) :nonlinearp t))))
(local (defthm lw-kc-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))

; All factorial-normalized polynomial factors and their finite slopes are
; bounded by a single coarse exponential band, independent of the index.
(defthm lw-exp-term-le-sum
  (implies (and (rationalp value) (<= 0 value) (natp index))
           (<= (lw-exp-term value index) (lw-exp-sum value index)))
  :hints (("Goal" :cases ((zp index)) :expand ((lw-exp-sum value index))
                  :use ((:instance lw-exp-sum-at-least-one (index (- index 1))))
                  :in-theory (disable lw-exp-sum-at-least-one))))

(defthm lw-exp-term-uniform-bound
  (implies (and (rationalp cap) (<= 0 cap) (natp index))
           (<= (lw-exp-term cap index) (lw-exp-lipschitz-cap cap)))
  :hints (("Goal" :use ((:instance lw-exp-term-le-sum (value cap)) lw-exp-sum-uniform-bound)
                  :in-theory (disable lw-exp-term-le-sum lw-exp-sum-uniform-bound))))

(defthm lw-exp-term-spatial-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap) (natp index))
           (<= (abs (- (lw-exp-term left index) (lw-exp-term right index)))
               (* (lw-exp-lipschitz-cap cap) (abs (- left right)))))
  :hints (("Goal" :cases ((<= left right) (zp index))
                  :use (lw-exp-lipschitz-cap-valid lw-exp-term-lipschitz-ordered
                        (:instance lw-exp-term-lipschitz-ordered (left right) (right left))
                        lw-exp-term-monotone (:instance lw-exp-term-monotone (left right) (right left))
                        (:instance lw-exp-term-uniform-bound (index (nfix (- index 1)))))
                  :in-theory (disable lw-exp-term-lipschitz-ordered lw-exp-term-monotone lw-exp-term-uniform-bound)
                  :nonlinearp t)))

(defun lw-kernel-spatial-cap (cap step) (* step (lw-exp-lipschitz-cap cap)))
(defun lw-kernel-spatial-slope (cap sigma step)
  (* (lw-kernel-spatial-cap cap step) (+ 1 (* sigma (lw-exp-lipschitz-cap (* sigma cap))))))

(defthm lw-kernel-spatial-parameters
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step))
           (and (rationalp (lw-kernel-spatial-cap cap step)) (<= 0 (lw-kernel-spatial-cap cap step))
                (rationalp (lw-kernel-spatial-slope cap sigma step))
                (<= 0 (lw-kernel-spatial-slope cap sigma step))))
  :hints (("Goal" :use (lw-exp-lipschitz-cap-valid
                        (:instance lw-exp-lipschitz-cap-valid (cap (* sigma cap))))
                  :nonlinearp t)))

(defthm lw-kernel-weight-scale-spatial-cap
  (implies (and (rationalp value) (rationalp cap) (<= 0 value) (<= value cap)
                (rationalp step) (<= 0 step) (natp index))
           (<= (lw-kernel-weight-scale value index step) (lw-kernel-spatial-cap cap step)))
  :hints (("Goal" :use ((:instance lw-exp-term-monotone (left value) (right cap)) lw-exp-term-uniform-bound)
                  :in-theory (e/d (lw-kernel-weight-scale) (lw-exp-term-monotone lw-exp-term-uniform-bound))
                  :nonlinearp t)))

(defthm lw-kernel-weight-scale-spatial-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp step) (<= 0 step) (natp index))
           (<= (abs (- (lw-kernel-weight-scale left index step) (lw-kernel-weight-scale right index step)))
               (* (lw-kernel-spatial-cap cap step) (abs (- left right)))))
  :hints (("Goal" :use (lw-exp-term-spatial-bound lw-exp-lipschitz-cap-valid
                        (:instance lw-kc-multiply-order
                          (a (abs (- (lw-exp-term left index) (lw-exp-term right index))))
                          (b (* (lw-exp-lipschitz-cap cap) (abs (- left right)))) (c step)))
                  :in-theory (e/d (lw-kernel-weight-scale) (lw-exp-term-spatial-bound)))))

(local
 (defthm lw-kc-product-transport
   (implies (and (rationalp a) (rationalp b) (rationalp top) (<= 0 a) (<= 0 b) (<= b top)
                 (rationalp x) (rationalp y) (<= 0 x) (<= x 1)
                 (rationalp scale-error) (<= (abs (- a b)) scale-error)
                 (rationalp exp-error) (<= 0 exp-error) (<= (- x y) exp-error))
            (<= (- (* a x) (* b y)) (+ scale-error (* top exp-error))))
   :hints (("Goal" :use ((:instance lw-kc-multiply-order (a (- a b)) (b (abs (- a b))) (c x))
                         (:instance lw-kc-multiply-order (a x) (b 1) (c (abs (- a b))))
                         (:instance lw-kc-multiply-order (a (- x y)) (b exp-error) (c b))
                         (:instance lw-kc-multiply-order (a b) (b top) (c exp-error)))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-kernel-weight-bounds-spatial-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp step) (<= 0 step) (natp index))
           (<= (- (car (lw-kernel-weight-bounds left sigma index step left-error))
                  (cdr (lw-kernel-weight-bounds right sigma index step right-error)))
               (* (lw-kernel-spatial-slope cap sigma step) (abs (- left right)))))
  :hints (("Goal"
           :use (lw-kernel-weight-scale-spatial-bound
                 (:instance lw-kernel-weight-scale-spatial-cap (value right))
                 (:instance lw-kernel-weight-scale-nonnegative (value left))
                 (:instance lw-kernel-weight-scale-nonnegative (value right))
                 lw-exp-lipschitz-cap-valid
                 (:instance lw-exp-lipschitz-cap-valid (cap (* sigma cap)))
                 (:instance lw-exp-neg-bounds-valid (value (* sigma left))
                   (epsilon (lw-kernel-weight-precision left index step left-error)))
                 (:instance lw-exp-neg-bounds-valid (value (* sigma right))
                   (epsilon (lw-kernel-weight-precision right index step right-error)))
                 (:instance lw-exp-neg-bounds-transport
                   (left (* sigma left)) (right (* sigma right)) (cap (* sigma cap))
                   (left-error (lw-kernel-weight-precision left index step left-error))
                   (right-error (lw-kernel-weight-precision right index step right-error)))
                 (:instance lw-kc-product-transport
                   (a (lw-kernel-weight-scale left index step)) (b (lw-kernel-weight-scale right index step))
                   (top (lw-kernel-spatial-cap cap step))
                   (x (car (lw-exp-neg-bounds (* sigma left) (lw-kernel-weight-precision left index step left-error))))
                   (y (cdr (lw-exp-neg-bounds (* sigma right) (lw-kernel-weight-precision right index step right-error))))
                   (scale-error (* (lw-kernel-spatial-cap cap step) (abs (- left right))))
                   (exp-error (* (lw-exp-lipschitz-cap (* sigma cap)) sigma (abs (- left right))))))
           :in-theory (e/d (lw-kernel-weight-bounds)
                           (lw-kernel-weight-scale-spatial-bound lw-kernel-weight-scale-spatial-cap
                            lw-kernel-weight-scale-nonnegative))
           :nonlinearp t)))

(defthm lw-kernel-weight-lower-spatial-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-kernel-weight-bounds left sigma index step left-error))
                        (car (lw-kernel-weight-bounds right sigma index step right-error))))
               (+ (* (lw-kernel-spatial-slope cap sigma step) (abs (- left right))) left-error right-error)))
  :hints (("Goal" :use (lw-kernel-spatial-parameters lw-kernel-weight-bounds-spatial-transport
                        (:instance lw-kernel-weight-bounds-spatial-transport
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-kernel-weight-bounds-width (value left) (error left-error))
                        (:instance lw-kernel-weight-bounds-width (value right) (error right-error))
                        (:instance lw-kernel-weight-bounds-valid (value left) (error left-error))
                        (:instance lw-kernel-weight-bounds-valid (value right) (error right-error)))
                  :in-theory (disable lw-kernel-spatial-cap lw-kernel-spatial-slope
                                      lw-kernel-spatial-parameters lw-kernel-weight-bounds-spatial-transport))))

(assert-event
 (and (equal (lw-kernel-spatial-cap 0 1/10) 1/10)
      (<= (- (car (lw-kernel-weight-bounds 1/2 2 3 1/10 1/100))
             (cdr (lw-kernel-weight-bounds 2/3 2 3 1/10 1/50)))
          (* (lw-kernel-spatial-slope 1 2 1/10) 1/6))))
