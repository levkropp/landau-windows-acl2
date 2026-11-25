(in-package "ACL2")

(include-book "complex-exp-product")

; Quantitative multiplication for the computed complex exponential.
; One computed common Taylor order pays for all three evaluations.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cem-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cem-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cem-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cem-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cem-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cem-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cem-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cem-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cem-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cem-product-difference-identity
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
                  (equal (lw-complex-sub (lw-complex-mul a b) (lw-complex-mul c d))
                         (lw-complex-add (lw-complex-mul (lw-complex-sub a c) b)
                                         (lw-complex-mul c (lw-complex-sub b d)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul)))
         :rule-classes nil))

(defthm lw-complex-mul-difference-bound
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                (lw-complex-diskp b right-cap) (lw-complex-diskp c left-cap)
                (lw-complex-diskp (lw-complex-sub a c) left-error)
                (lw-complex-diskp (lw-complex-sub b d) right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-mul a b) (lw-complex-mul c d))
            (+ (* right-cap left-error) (* left-cap right-error))))
  :hints (("Goal" :use (lw-cem-product-difference-identity
                        (:instance lw-complex-mul-disk
                          (left (lw-complex-sub a c)) (radius left-error) (right b) (other-radius right-cap))
                        (:instance lw-complex-mul-disk
                          (left c) (radius left-cap) (right (lw-complex-sub b d)) (other-radius right-error))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-mul (lw-complex-sub a c) b)) (radius (* right-cap left-error))
                          (right (lw-complex-mul c (lw-complex-sub b d))) (other-radius (* left-cap right-error))))
                  :in-theory (disable lw-complex-mul-disk lw-complex-add-disk lw-complex-mul-subtract
                                      lw-complex-mul-commutative lw-complex-mul-left-commutes))))

(defthm lw-complex-exp-sum-computed-addition-error
  (implies (and (lw-complex-diskp left left-radius) (lw-complex-diskp right right-radius)
                (rationalp error) (< 0 error) (natp degree)
                (<= (lw-exp-index (+ left-radius right-radius) error) degree))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-mul (lw-complex-exp-sum left degree) (lw-complex-exp-sum right degree))
             (lw-complex-exp-sum (lw-complex-add left right) degree)) error))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (value (+ left-radius right-radius)) (epsilon error))
                        (:instance lw-exp-index-later-tail-budget (radius (+ left-radius right-radius)))
                        lw-complex-exp-sum-product-addition-error
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-mul (lw-complex-exp-sum left degree) (lw-complex-exp-sum right degree))
                                  (lw-complex-exp-sum (lw-complex-add left right) degree)))
                          (radius (* 2 (lw-exp-term (+ left-radius right-radius) (+ 1 degree)))) (cap error)))
                  :in-theory (disable lw-exp-index-adequate lw-exp-index-later-tail-budget
                                      lw-complex-exp-sum-product-addition-error))))

(defun lw-complex-exp-product-index (left right left-error right-error sum-error)
  (max (lw-exp-index (lw-complex-l1 left) left-error)
       (max (lw-exp-index (lw-complex-l1 right) right-error)
            (max (lw-exp-index (lw-complex-l1 (lw-complex-add left right)) sum-error)
                 (lw-exp-index (+ (lw-complex-l1 left) (lw-complex-l1 right)) sum-error)))))

(defthm lw-complex-exp-product-index-data
  (implies (and (lw-complexp left) (lw-complexp right)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
                (rationalp sum-error) (< 0 sum-error))
           (and (natp (lw-complex-exp-product-index left right left-error right-error sum-error))
                (<= (lw-exp-index (lw-complex-l1 left) left-error)
                    (lw-complex-exp-product-index left right left-error right-error sum-error))
                (<= (lw-exp-index (lw-complex-l1 right) right-error)
                    (lw-complex-exp-product-index left right left-error right-error sum-error))
                (<= (lw-exp-index (lw-complex-l1 (lw-complex-add left right)) sum-error)
                    (lw-complex-exp-product-index left right left-error right-error sum-error))
                (<= (lw-exp-index (+ (lw-complex-l1 left) (lw-complex-l1 right)) sum-error)
                    (lw-complex-exp-product-index left right left-error right-error sum-error))))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound (point left))
                        (:instance lw-complex-l1-bound (point right))
                        (:instance lw-complex-l1-bound (point (lw-complex-add left right)))
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 left)) (epsilon left-error))
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 right)) (epsilon right-error))
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 (lw-complex-add left right))) (epsilon sum-error))
                        (:instance lw-exp-index-adequate (value (+ (lw-complex-l1 left) (lw-complex-l1 right))) (epsilon sum-error)))
                  :in-theory (disable lw-complex-l1-bound lw-exp-index-adequate))))

(local (in-theory (disable lw-complex-exp-product-index)))

(defthm lw-complex-exp-value-multiplication
  (implies (and (lw-complexp left) (lw-complexp right)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
                (rationalp sum-error) (< 0 sum-error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-mul (lw-complex-exp-value left left-error) (lw-complex-exp-value right right-error))
             (lw-complex-exp-value (lw-complex-add left right) sum-error))
            (+ (* (lw-complex-exp-cap right) left-error)
               (* (lw-complex-exp-cap left) right-error) (* 2 sum-error))))
  :hints (("Goal" :use (lw-complex-exp-product-index-data
                        (:instance lw-complex-l1-bound (point left))
                        (:instance lw-complex-l1-bound (point right))
                        (:instance lw-complex-exp-value-tail (point left) (error left-error)
                          (large (lw-complex-exp-product-index left right left-error right-error sum-error)))
                        (:instance lw-complex-exp-value-tail (point right) (error right-error)
                          (large (lw-complex-exp-product-index left right left-error right-error sum-error)))
                        (:instance lw-complex-exp-value-tail (point (lw-complex-add left right)) (error sum-error)
                          (large (lw-complex-exp-product-index left right left-error right-error sum-error)))
                        (:instance lw-complex-difference-symmetric
                          (left (lw-complex-exp-sum left (lw-complex-exp-product-index left right left-error right-error sum-error)))
                          (right (lw-complex-exp-value left left-error)) (radius left-error))
                        (:instance lw-complex-difference-symmetric
                          (left (lw-complex-exp-sum right (lw-complex-exp-product-index left right left-error right-error sum-error)))
                          (right (lw-complex-exp-value right right-error)) (radius right-error))
                        (:instance lw-complex-mul-difference-bound
                          (a (lw-complex-exp-value left left-error)) (b (lw-complex-exp-value right right-error))
                          (c (lw-complex-exp-sum left (lw-complex-exp-product-index left right left-error right-error sum-error)))
                          (d (lw-complex-exp-sum right (lw-complex-exp-product-index left right left-error right-error sum-error)))
                          (right-cap (lw-complex-exp-cap right)) (left-cap (lw-complex-exp-cap left)))
                        (:instance lw-complex-exp-sum-computed-addition-error
                          (left-radius (lw-complex-l1 left)) (right-radius (lw-complex-l1 right)) (error sum-error)
                          (degree (lw-complex-exp-product-index left right left-error right-error sum-error)))
                        (:instance lw-complex-difference-triangle
                          (left (lw-complex-mul (lw-complex-exp-value left left-error) (lw-complex-exp-value right right-error)))
                          (middle (lw-complex-mul
                                   (lw-complex-exp-sum left (lw-complex-exp-product-index left right left-error right-error sum-error))
                                   (lw-complex-exp-sum right (lw-complex-exp-product-index left right left-error right-error sum-error))))
                          (right (lw-complex-exp-sum (lw-complex-add left right)
                                  (lw-complex-exp-product-index left right left-error right-error sum-error)))
                          (radius (+ (* (lw-complex-exp-cap right) left-error) (* (lw-complex-exp-cap left) right-error)))
                          (other-radius sum-error))
                        (:instance lw-complex-difference-triangle
                          (left (lw-complex-mul (lw-complex-exp-value left left-error) (lw-complex-exp-value right right-error)))
                          (middle (lw-complex-exp-sum (lw-complex-add left right)
                                   (lw-complex-exp-product-index left right left-error right-error sum-error)))
                          (right (lw-complex-exp-value (lw-complex-add left right) sum-error))
                          (radius (+ (* (lw-complex-exp-cap right) left-error) (* (lw-complex-exp-cap left) right-error) sum-error))
                          (other-radius sum-error)))
                  :in-theory (disable lw-complex-exp-product-index-data lw-complex-l1-bound
                                      lw-complex-exp-value-tail lw-complex-mul-difference-bound
                                      lw-complex-exp-sum-computed-addition-error lw-complex-difference-triangle))))
