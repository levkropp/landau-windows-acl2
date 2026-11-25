(in-package "ACL2")

(include-book "complex-convolution")
(include-book "exp-mixture-bounds")

; A product rectangle differs from its total-degree triangle only in
; high Taylor degrees. Real nonnegative sums majorize that finite error.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-convolution-triangle
                 lw-complex-exp-convolution-row lw-complex-exp-convolution-triangle)))

(local (defthm lw-cp-left-commutes-product
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cp-left-distribute-product
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cp-times-negative-product
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cp-negative-times-product
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cp-zero-times-product (equal (* 0 a) 0)))
(local (defthm lw-cp-minus-one-product (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cp-double-negative-product (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cp-add-cancel-product
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cp-double-product
         (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defun lw-cp-product-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-cp-product-countdown (- index 1)))))

(local (defthm lw-cp-product-term-zero
         (implies (zp index) (equal (lw-complex-exp-term point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-term)))))
(local (defthm lw-cp-product-sum-zero
         (implies (zp index) (equal (lw-complex-exp-sum point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-sum)))))
(local (defthm lw-cp-product-real-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-cp-product-real-sum-zero
         (implies (zp index) (equal (lw-exp-sum value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-sum)))))

(defthm lw-complex-exp-sum-majorant
  (implies (and (lw-complex-diskp point radius) (natp degree))
           (lw-complex-diskp (lw-complex-exp-sum point degree) (lw-exp-sum radius degree)))
  :hints (("Goal" :induct (lw-cp-product-countdown degree)
                  :expand ((lw-complex-exp-sum point degree) (lw-exp-sum radius degree)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-exp-term-majorant (index degree))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-exp-term point degree)) (radius (lw-exp-term radius degree))
                          (right (lw-complex-exp-sum point (- degree 1))) (other-radius (lw-exp-sum radius (- degree 1)))))
                 :in-theory (disable lw-complex-exp-term-majorant lw-complex-add-disk)))))

(local (defun lw-cp-complex-rectangle (left right degree count)
         (if (zp count) (cons 0 0)
           (lw-complex-add (lw-cp-complex-rectangle left right degree (- count 1))
                           (lw-complex-mul (lw-complex-exp-term left (- count 1))
                                            (lw-complex-exp-sum right degree))))))
(local (defun lw-cp-real-rectangle (left right degree count)
         (if (zp count) 0
           (+ (lw-cp-real-rectangle left right degree (- count 1))
              (* (lw-exp-term left (- count 1)) (lw-exp-sum right degree))))))

(local (defthm lw-cp-rectangle-rational
         (implies (and (lw-complexp left) (lw-complexp right) (natp degree) (natp count))
                  (lw-complexp (lw-cp-complex-rectangle left right degree count)))))
(local (defthm lw-cp-real-rectangle-rational
         (implies (and (rationalp left) (rationalp right)) (rationalp (lw-cp-real-rectangle left right degree count)))))
(local (defthm lw-cp-rectangle-zero
         (implies (zp count) (equal (lw-cp-complex-rectangle left right degree count) (cons 0 0)))))
(local (defthm lw-cp-real-rectangle-zero
         (implies (zp count) (equal (lw-cp-real-rectangle left right degree count) 0))))
(local (defthm lw-cp-triangle-zero
         (implies (zp count) (equal (lw-complex-exp-convolution-triangle left right degree count) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-convolution-triangle)))))
(local (defthm lw-cp-real-triangle-zero
         (implies (zp count) (equal (lw-exp-convolution-triangle left right degree count) 0))
         :hints (("Goal" :in-theory (enable lw-exp-convolution-triangle)))))

(local (defthm lw-cp-rectangle-factor
         (implies (and (lw-complexp left) (lw-complexp right) (natp degree) (posp count))
                  (equal (lw-cp-complex-rectangle left right degree count)
                         (lw-complex-mul (lw-complex-exp-sum left (- count 1)) (lw-complex-exp-sum right degree))))
         :hints (("Goal" :induct (lw-cp-product-countdown count)
                         :expand ((lw-complex-exp-sum left (- count 1)))))))
(local (defthm lw-cp-real-rectangle-factor
         (implies (and (rationalp left) (rationalp right) (natp degree) (posp count))
                  (equal (lw-cp-real-rectangle left right degree count)
                         (* (lw-exp-sum left (- count 1)) (lw-exp-sum right degree))))
         :hints (("Goal" :induct (lw-cp-product-countdown count)
                         :expand ((lw-exp-sum left (- count 1)))))))

(local (defthm lw-cp-rectangle-difference-majorant
         (implies (and (lw-complex-diskp left left-radius) (lw-complex-diskp right right-radius)
                       (natp degree) (natp count) (<= count (+ 1 degree)))
                  (lw-complex-diskp
                   (lw-complex-sub (lw-cp-complex-rectangle left right degree count)
                                   (lw-complex-exp-convolution-triangle left right degree count))
                   (- (lw-cp-real-rectangle left-radius right-radius degree count)
                      (lw-exp-convolution-triangle left-radius right-radius degree count))))
         :hints (("Goal" :induct (lw-cp-product-countdown count)
                         :expand ((lw-cp-complex-rectangle left right degree count)
                                  (lw-complex-exp-convolution-triangle left right degree count)
                                  (lw-cp-real-rectangle left-radius right-radius degree count)
                                  (lw-exp-convolution-triangle left-radius right-radius degree count))
                         :in-theory (disable lw-cp-rectangle-factor lw-cp-real-rectangle-factor
                                             lw-complex-sub-add-first lw-complex-add-commutative
                                             lw-complex-add-left-commutes lw-complex-mul-commutative
                                             lw-complex-mul-left-commutes))
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-complex-exp-term-majorant
                                 (point left) (radius left-radius) (index (- count 1)))
                              (:instance lw-complex-exp-sum-difference-majorant
                                 (point right) (radius right-radius) (small (- degree (- count 1))) (large degree))
                              (:instance lw-complex-mul-disk
                                (left (lw-complex-exp-term left (- count 1))) (radius (lw-exp-term left-radius (- count 1)))
                                (right (lw-complex-sub (lw-complex-exp-sum right degree)
                                                       (lw-complex-exp-sum right (- degree (- count 1)))))
                                (other-radius (- (lw-exp-sum right-radius degree)
                                                 (lw-exp-sum right-radius (- degree (- count 1))))))
                              (:instance lw-complex-add-disk
                                (left (lw-complex-sub (lw-cp-complex-rectangle left right degree (- count 1))
                                                      (lw-complex-exp-convolution-triangle left right degree (- count 1))))
                                (radius (- (lw-cp-real-rectangle left-radius right-radius degree (- count 1))
                                           (lw-exp-convolution-triangle left-radius right-radius degree (- count 1))))
                                (right (lw-complex-sub
                                        (lw-complex-mul (lw-complex-exp-term left (- count 1)) (lw-complex-exp-sum right degree))
                                        (lw-complex-mul (lw-complex-exp-term left (- count 1))
                                                         (lw-complex-exp-sum right (- degree (- count 1))))))
                                (other-radius (* (lw-exp-term left-radius (- count 1))
                                                  (- (lw-exp-sum right-radius degree)
                                                     (lw-exp-sum right-radius (- degree (- count 1))))))))
                        :in-theory (disable lw-cp-complex-rectangle lw-cp-real-rectangle
                                            lw-complex-exp-convolution-triangle lw-exp-convolution-triangle
                                            lw-cp-rectangle-factor lw-cp-real-rectangle-factor
                                            lw-complex-sub-add-first lw-complex-add-commutative
                                            lw-complex-add-left-commutes lw-complex-mul-commutative
                                            lw-complex-mul-left-commutes lw-complex-exp-term-majorant
                                            lw-complex-exp-sum-difference-majorant
                                            lw-complex-mul-disk lw-complex-add-disk))))))

(defthm lw-complex-exp-sum-product-addition-error
  (implies (and (lw-complex-diskp left left-radius) (lw-complex-diskp right right-radius)
                (natp degree) (<= (* 2 (+ left-radius right-radius)) (+ 2 degree)))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-mul (lw-complex-exp-sum left degree) (lw-complex-exp-sum right degree))
             (lw-complex-exp-sum (lw-complex-add left right) degree))
            (* 2 (lw-exp-term (+ left-radius right-radius) (+ 1 degree)))))
  :hints (("Goal" :use ((:instance lw-cp-rectangle-difference-majorant (count (+ 1 degree)))
                        (:instance lw-exp-sum-product-upper
                          (left left-radius) (right right-radius) (left-index degree) (right-index degree))
                        (:instance lw-exp-later-partial-sum-enclosed
                          (value (+ left-radius right-radius)) (small degree) (large (* 2 degree)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-mul (lw-complex-exp-sum left degree) (lw-complex-exp-sum right degree))
                                  (lw-complex-exp-sum (lw-complex-add left right) degree)))
                          (radius (- (* (lw-exp-sum left-radius degree) (lw-exp-sum right-radius degree))
                                     (lw-exp-sum (+ left-radius right-radius) degree)))
                          (cap (* 2 (lw-exp-term (+ left-radius right-radius) (+ 1 degree))))))
                  :in-theory (e/d (lw-exp-band)
                                  (lw-cp-complex-rectangle lw-cp-real-rectangle
                                   lw-cp-rectangle-difference-majorant lw-complex-disk-enlarge)))))

(defun lw-complex-exp-cap (point) (cdr (lw-exp-bounds (lw-complex-l1 point) 1)))

(defthm lw-complex-exp-cap-valid
  (implies (lw-complexp point)
           (and (rationalp (lw-complex-exp-cap point)) (<= 1 (lw-complex-exp-cap point))))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        (:instance lw-exp-bounds-valid (value (lw-complex-l1 point)) (epsilon 1)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-complex-l1-bound lw-exp-bounds-valid
                                   lw-exp-bounds-monotone-overlap lw-exp-bounds-overlap)))))

(defthm lw-complex-exp-prefix-cap
  (implies (and (lw-complexp point) (natp degree))
           (lw-complex-diskp (lw-complex-exp-sum point degree) (lw-complex-exp-cap point)))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        lw-complex-exp-cap-valid
                        (:instance lw-complex-exp-sum-majorant (radius (lw-complex-l1 point)))
                        (:instance lw-exp-partial-sum-upper (value (lw-complex-l1 point)) (index degree) (error 1))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-exp-sum point degree)) (radius (lw-exp-sum (lw-complex-l1 point) degree))
                          (cap (lw-complex-exp-cap point))))
                  :in-theory (disable lw-complex-l1-bound lw-complex-exp-cap-valid
                                      lw-complex-exp-sum-majorant lw-complex-disk-enlarge))))

(defthm lw-complex-exp-value-cap
  (implies (and (lw-complexp point) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-complex-exp-value point error) (lw-complex-exp-cap point)))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 point)) (epsilon error))
                        (:instance lw-complex-exp-prefix-cap
                          (degree (lw-exp-index (lw-complex-l1 point) error))))
                  :in-theory (e/d (lw-complex-exp-value)
                                  (lw-complex-l1-bound lw-exp-index-adequate lw-complex-exp-prefix-cap)))))

; E_2(i)*E_2(1)-E_2(1+i) = -3/4+i/2, calculated independently.
(assert-event
 (equal (lw-complex-sub
         (lw-complex-mul (lw-complex-exp-sum (cons 0 1) 2)
                          (lw-complex-exp-sum (cons 1 0) 2))
         (lw-complex-exp-sum (cons 1 1) 2))
        (cons -3/4 1/2)))
