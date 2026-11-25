(in-package "ACL2")

(include-book "complex-exp")
(include-book "exp-addition")

; Exact finite convolution over rational complex numbers. The addition
; identity is derived from Taylor recurrences, not supplied as an input.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds)))

(local (defthm lw-cc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cc-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cc-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cc-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cc-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cc-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defun lw-cc-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-cc-countdown (- index 1)))))

(local (defthm lw-cc-term-zero
         (implies (zp index) (equal (lw-complex-exp-term point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-term)))))
(local (defthm lw-cc-sum-zero
         (implies (zp index) (equal (lw-complex-exp-sum point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-sum)))))
(local (defthm lw-cc-term-rational-total
         (implies (lw-complexp point) (lw-complexp (lw-complex-exp-term point index)))
         :hints (("Goal" :cases ((natp index))))))

(defthm lw-complex-exp-term-multiplied
  (implies (and (lw-complexp point) (posp index))
           (equal (lw-complex-scale index (lw-complex-exp-term point index))
                  (lw-complex-mul point (lw-complex-exp-term point (- index 1)))))
  :hints (("Goal" :use ((:instance inverse-of-* (x index)))
                  :expand ((lw-complex-exp-term point index))
                  :in-theory (disable inverse-of-*))))

(local (defthm lw-cc-scale-sum
         (implies (and (rationalp left-factor) (rationalp right-factor) (lw-complexp point))
                  (equal (lw-complex-scale (+ left-factor right-factor) point)
                         (lw-complex-add (lw-complex-scale left-factor point)
                                         (lw-complex-scale right-factor point))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-add)))
         :rule-classes nil))

(local (defthm lw-cc-scale-product-left
         (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-scale factor (lw-complex-mul a b))
                         (lw-complex-mul (lw-complex-scale factor a) b)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-mul)))
         :rule-classes nil))

(local (defthm lw-cc-balanced-term
         (implies (and (lw-complexp left) (lw-complexp right)
                       (natp degree) (posp index) (<= index degree))
                  (equal
                   (lw-complex-scale (+ 1 degree)
                    (lw-complex-mul (lw-complex-exp-term left index)
                                     (lw-complex-exp-term right (- (+ 1 degree) index))))
                   (lw-complex-add
                    (lw-complex-mul left
                     (lw-complex-mul (lw-complex-exp-term left (- index 1))
                                      (lw-complex-exp-term right (- (+ 1 degree) index))))
                    (lw-complex-mul right
                     (lw-complex-mul (lw-complex-exp-term left index)
                                      (lw-complex-exp-term right (- degree index)))))))
         :hints (("Goal" :use ((:instance lw-complex-exp-term-multiplied (point left))
                              (:instance lw-complex-exp-term-multiplied
                                (point right) (index (- (+ 1 degree) index)))
                              (:instance lw-cc-scale-sum
                                (left-factor index) (right-factor (- (+ 1 degree) index))
                                (point (lw-complex-mul (lw-complex-exp-term left index)
                                                       (lw-complex-exp-term right (- (+ 1 degree) index)))))
                              (:instance lw-cc-scale-product-left
                                (factor index) (a (lw-complex-exp-term left index))
                                (b (lw-complex-exp-term right (- (+ 1 degree) index))))
                              (:instance lw-complex-scale-product
                                (factor (- (+ 1 degree) index)) (left (lw-complex-exp-term left index))
                                (right (lw-complex-exp-term right (- (+ 1 degree) index))))
                              (:instance lw-complex-mul-left-commutes
                                (a (lw-complex-exp-term left index)) (b right)
                                (c (lw-complex-exp-term right (- degree index)))))
                         :in-theory (disable lw-complex-exp-term-multiplied lw-complex-scale-product
                                             lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(defun lw-complex-exp-convolution-row (left right degree count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-exp-convolution-row left right degree (- count 1))
     (lw-complex-mul (lw-complex-exp-term left (- count 1))
                      (lw-complex-exp-term right (- degree (- count 1)))))))

(defthm lw-complex-exp-convolution-row-rational
  (implies (and (lw-complexp left) (lw-complexp right))
           (lw-complexp (lw-complex-exp-convolution-row left right degree count))))

(local (defthm lw-cc-row-zero
         (implies (zp count) (equal (lw-complex-exp-convolution-row left right degree count) (cons 0 0)))))
(local (defthm lw-cc-row-one
         (implies (lw-complexp right)
                  (equal (lw-complex-exp-convolution-row left right degree 1) (lw-complex-exp-term right degree)))))

(local (defthm lw-cc-partial-row-recurrence
         (implies (and (lw-complexp left) (lw-complexp right) (natp degree) (natp index) (<= index degree))
                  (equal
                   (lw-complex-scale (+ 1 degree)
                    (lw-complex-exp-convolution-row left right (+ 1 degree) (+ 1 index)))
                   (lw-complex-add
                    (lw-complex-mul (lw-complex-add left right)
                     (lw-complex-exp-convolution-row left right degree index))
                    (lw-complex-mul right
                     (lw-complex-mul (lw-complex-exp-term left index)
                                      (lw-complex-exp-term right (- degree index)))))))
         :hints (("Goal" :induct (lw-cc-countdown index))
                 (and stable-under-simplificationp
                      '(:use (lw-cc-balanced-term
                              (:instance lw-complex-exp-term-multiplied (point right) (index (+ 1 degree))))
                        :expand ((lw-complex-exp-convolution-row left right (+ 1 degree) (+ 1 index))
                                 (lw-complex-exp-convolution-row left right degree index))
                        :in-theory (e/d (lw-complexp lw-complex-add lw-complex-mul lw-complex-scale)
                                        (lw-cc-balanced-term lw-complex-exp-term-multiplied))
                        :nonlinearp nil)))))

(local (defthm lw-cc-scale-inverse
         (implies (and (rationalp factor) (not (equal factor 0)) (lw-complexp point))
                  (equal (lw-complex-scale (/ factor) (lw-complex-scale factor point)) point))
         :hints (("Goal" :use ((:instance inverse-of-* (x factor)))
                         :in-theory (disable inverse-of-*)))))

(local (defthm lw-cc-scale-injective
         (implies (and (rationalp factor) (not (equal factor 0))
                       (lw-complexp a) (lw-complexp b)
                       (equal (lw-complex-scale factor a) (lw-complex-scale factor b)))
                  (equal a b))
         :hints (("Goal" :use ((:instance lw-cc-scale-inverse (point a))
                              (:instance lw-cc-scale-inverse (point b)))
                         :in-theory (disable lw-cc-scale-inverse)))
         :rule-classes nil))

(local (defthm lw-cc-full-row-step
         (implies (and (lw-complexp left) (lw-complexp right) (posp degree))
                  (equal
                   (lw-complex-scale degree (lw-complex-exp-convolution-row left right degree (+ 1 degree)))
                   (lw-complex-mul (lw-complex-add left right)
                                   (lw-complex-exp-convolution-row left right (- degree 1) degree))))
         :hints (("Goal" :use ((:instance lw-cc-partial-row-recurrence (degree (- degree 1)) (index (- degree 1)))
                              (:instance lw-complex-exp-term-multiplied (point left) (index degree)))
                         :expand ((lw-complex-exp-convolution-row left right degree (+ 1 degree))
                                  (lw-complex-exp-convolution-row left right (- degree 1) degree))
                         :in-theory (e/d (lw-complexp lw-complex-add lw-complex-mul lw-complex-scale)
                                         (lw-complex-exp-convolution-row lw-cc-partial-row-recurrence
                                          lw-complex-exp-term-multiplied))
                         :nonlinearp nil))
         :rule-classes nil))

(defthm lw-complex-exp-convolution-row-exact
  (implies (and (lw-complexp left) (lw-complexp right) (natp degree))
           (equal (lw-complex-exp-convolution-row left right degree (+ 1 degree))
                  (lw-complex-exp-term (lw-complex-add left right) degree)))
  :hints (("Goal" :induct (lw-cc-countdown degree)
                  :in-theory (disable lw-complex-exp-convolution-row lw-complex-exp-term-multiplied))
          (and stable-under-simplificationp
               '(:use (lw-cc-full-row-step
                        (:instance lw-complex-exp-term-multiplied
                          (point (lw-complex-add left right)) (index degree))
                        (:instance lw-cc-scale-injective (factor degree)
                          (a (lw-complex-exp-convolution-row left right degree (+ 1 degree)))
                          (b (lw-complex-exp-term (lw-complex-add left right) degree))))
                 :expand ((lw-complex-exp-convolution-row left right 0 1))
                 :in-theory (disable lw-complex-exp-convolution-row lw-complex-exp-term-multiplied)))))

(local (in-theory (disable lw-complex-exp-convolution-row lw-complex-exp-convolution-row-exact)))

(local (defthm lw-cc-sum-rational-total
         (implies (lw-complexp point) (lw-complexp (lw-complex-exp-sum point index)))
         :hints (("Goal" :cases ((natp index))))))

(defun lw-complex-exp-convolution-triangle (left right degree count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-exp-convolution-triangle left right degree (- count 1))
     (lw-complex-mul (lw-complex-exp-term left (- count 1))
                      (lw-complex-exp-sum right (- degree (- count 1)))))))

(defthm lw-complex-exp-convolution-triangle-rational
  (implies (and (lw-complexp left) (lw-complexp right))
           (lw-complexp (lw-complex-exp-convolution-triangle left right degree count))))

(local (defthm lw-cc-triangle-zero
         (implies (zp count) (equal (lw-complex-exp-convolution-triangle left right degree count) (cons 0 0)))))
(local (defthm lw-cc-triangle-one
         (implies (lw-complexp right)
                  (equal (lw-complex-exp-convolution-triangle left right degree 1) (lw-complex-exp-sum right degree)))))

(local (defthm lw-cc-sum-step
         (implies (posp index)
                  (equal (lw-complex-exp-sum point index)
                         (lw-complex-add (lw-complex-exp-term point index)
                                         (lw-complex-exp-sum point (- index 1)))))
         :hints (("Goal" :expand ((lw-complex-exp-sum point index))))
         :rule-classes nil))

(local (defthm lw-cc-add-pair-substitution
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (lw-complexp d) (lw-complexp e)
                       (equal b (lw-complex-add c d)))
                  (equal (lw-complex-add b (lw-complex-add a e))
                         (lw-complex-add c (lw-complex-add d (lw-complex-add a e)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))
         :rule-classes nil))

(local (defthm lw-cc-triangle-step
         (implies (and (lw-complexp left) (lw-complexp right) (natp degree)
                       (natp count) (<= count (+ 1 degree)))
                  (equal (lw-complex-exp-convolution-triangle left right (+ 1 degree) count)
                         (lw-complex-add (lw-complex-exp-convolution-triangle left right degree count)
                                         (lw-complex-exp-convolution-row left right (+ 1 degree) count))))
         :hints (("Goal" :induct (lw-cc-countdown count)
                         :in-theory (disable lw-complex-exp-convolution-triangle))
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-cc-sum-step (point right) (index (+ 2 degree (- count))))
                              (:instance lw-cc-add-pair-substitution
                                (a (lw-complex-mul (lw-complex-exp-term left (- count 1))
                                                   (lw-complex-exp-term right (+ 2 degree (- count)))))
                                (b (lw-complex-exp-convolution-triangle left right (+ 1 degree) (- count 1)))
                                (c (lw-complex-exp-convolution-triangle left right degree (- count 1)))
                                (d (lw-complex-exp-convolution-row left right (+ 1 degree) (- count 1)))
                                (e (lw-complex-mul (lw-complex-exp-term left (- count 1))
                                                   (lw-complex-exp-sum right (+ 1 degree (- count)))))))
                        :expand ((lw-complex-exp-convolution-triangle left right (+ 1 degree) count)
                                 (lw-complex-exp-convolution-triangle left right degree count)
                                 (lw-complex-exp-convolution-row left right (+ 1 degree) count))
                        :in-theory (disable lw-complex-exp-convolution-triangle
                                            lw-complex-exp-convolution-row))))))

(local (defthm lw-cc-add-two-substitutions
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (lw-complexp d) (lw-complexp f)
                       (equal b (lw-complex-add c d))
                       (equal f (lw-complex-add d a)))
                  (equal (lw-complex-add b a) (lw-complex-add c f)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))
         :rule-classes nil))

(defthm lw-complex-exp-convolution-triangle-exact
  (implies (and (lw-complexp left) (lw-complexp right) (natp degree))
           (equal (lw-complex-exp-convolution-triangle left right degree (+ 1 degree))
                  (lw-complex-exp-sum (lw-complex-add left right) degree)))
  :hints (("Goal" :induct (lw-cc-countdown degree)
                  :in-theory (disable lw-complex-exp-convolution-triangle lw-cc-triangle-step))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cc-triangle-step (degree (- degree 1)) (count degree))
                        lw-complex-exp-convolution-row-exact
                        (:instance lw-cc-sum-step (point (lw-complex-add left right)) (index degree))
                        (:instance lw-cc-add-two-substitutions
                          (a (lw-complex-exp-term left degree))
                          (b (lw-complex-exp-convolution-triangle left right degree degree))
                          (c (lw-complex-exp-convolution-triangle left right (- degree 1) degree))
                          (d (lw-complex-exp-convolution-row left right degree degree))
                          (f (lw-complex-exp-term (lw-complex-add left right) degree))))
                 :expand ((lw-complex-exp-convolution-triangle left right degree (+ 1 degree))
                          (lw-complex-exp-convolution-row left right degree (+ 1 degree)))
                 :in-theory (disable lw-complex-exp-convolution-triangle lw-cc-triangle-step
                                     lw-complex-exp-convolution-row-exact)))))

; For z=i and w=1, the second convolution row is i=(1+i)^2/2.
(assert-event
 (and (equal (lw-complex-exp-convolution-row (cons 0 1) (cons 1 0) 2 3) (cons 0 1))
      (equal (lw-complex-exp-convolution-triangle (cons 0 1) (cons 1 0) 2 3) (cons 2 2))))
