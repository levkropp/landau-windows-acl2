(in-package "ACL2")

(include-book "exp-continuity")

; Finite Taylor convolution. This supplies arithmetic exponential product
; laws needed to shift the Mellin kernel's decay rate by the growth rate.
; No real exponential or multiplicative law is assumed.
(local (in-theory (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-neg-bounds
                           lw-exp-term-multiplied lw-exp-index lw-exp-band)))
(local (defthm lw-ea-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ea-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ea-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ea-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-ea-zero-times (equal (* 0 a) 0)))
(local (defthm lw-ea-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-ea-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-ea-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-ea-equal-times
         (implies (equal a b) (equal (* a c) (* b c))) :rule-classes nil))
(local (defun lw-ea-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-ea-countdown (- index 1)))))
(local (defthm lw-ea-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))

(defun lw-exp-convolution-row (left right degree count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (lw-exp-convolution-row left right degree (- count 1))
       (* (lw-exp-term left (- count 1)) (lw-exp-term right (- degree (- count 1)))))))

(defthm lw-exp-convolution-row-rational
  (implies (and (rationalp left) (rationalp right))
           (rationalp (lw-exp-convolution-row left right degree count)))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-ea-row-zero
         (implies (zp count) (equal (lw-exp-convolution-row left right degree count) 0))))
(local (defthm lw-ea-row-one
         (implies (rationalp right) (equal (lw-exp-convolution-row left right degree 1) (lw-exp-term right degree)))))

(local
 (defthm lw-ea-balanced-term
   (implies (and (rationalp left) (rationalp right) (natp degree) (posp index) (<= index degree))
            (equal (* (+ 1 degree) (lw-exp-term left index) (lw-exp-term right (- (+ 1 degree) index)))
                   (+ (* left (lw-exp-term left (- index 1)) (lw-exp-term right (- (+ 1 degree) index)))
                      (* right (lw-exp-term left index) (lw-exp-term right (- degree index))))))
   :hints (("Goal" :use ((:instance lw-exp-term-multiplied (value left))
                         (:instance lw-exp-term-multiplied (value right) (index (- (+ 1 degree) index)))
                         (:instance lw-ea-equal-times
                           (a (* index (lw-exp-term left index))) (b (* left (lw-exp-term left (- index 1))))
                           (c (lw-exp-term right (- (+ 1 degree) index))))
                         (:instance lw-ea-equal-times
                           (a (* (- (+ 1 degree) index) (lw-exp-term right (- (+ 1 degree) index))))
                           (b (* right (lw-exp-term right (- degree index)))) (c (lw-exp-term left index))))
                   :nonlinearp t))))

; Partial-row recurrence has one explicit boundary term. At the final
; column it becomes the full Taylor recurrence at left+right.
(local
 (defthm lw-ea-partial-row-recurrence
   (implies (and (rationalp left) (rationalp right) (natp degree) (natp index) (<= index degree))
            (equal (* (+ 1 degree) (lw-exp-convolution-row left right (+ 1 degree) (+ 1 index)))
                   (+ (* (+ left right) (lw-exp-convolution-row left right degree index))
                      (* right (lw-exp-term left index) (lw-exp-term right (- degree index))))))
   :hints (("Goal" :induct (lw-ea-countdown index))
           (and stable-under-simplificationp
                '(:use (lw-ea-balanced-term
                        (:instance lw-exp-term-multiplied (value right) (index (+ 1 degree))))
                  :in-theory (disable lw-ea-balanced-term)
                  :expand ((lw-exp-convolution-row left right (+ 1 degree) (+ 1 index))
                           (lw-exp-convolution-row left right degree index))
                  :nonlinearp t)))))

(defthm lw-exp-convolution-row-exact
  (implies (and (rationalp left) (rationalp right) (natp degree))
           (equal (lw-exp-convolution-row left right degree (+ 1 degree)) (lw-exp-term (+ left right) degree)))
  :hints (("Goal" :induct (lw-ea-countdown degree)
                  :in-theory (disable (:definition lw-exp-convolution-row) lw-ea-partial-row-recurrence))
          (and stable-under-simplificationp
               '(:use ((:instance lw-ea-partial-row-recurrence (degree (- degree 1)) (index (- degree 1)))
                       (:instance lw-exp-term-multiplied (value left) (index degree))
                       (:instance lw-exp-term-multiplied (value (+ left right)) (index degree)))
                 :expand ((lw-exp-convolution-row left right degree (+ 1 degree))
                          (lw-exp-convolution-row left right (- degree 1) degree))
                 :in-theory (disable (:definition lw-exp-convolution-row) lw-ea-partial-row-recurrence)
                 :nonlinearp t))))

(local (in-theory (disable lw-exp-convolution-row lw-exp-convolution-row-exact)))

(defun lw-exp-convolution-triangle (left right degree count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (lw-exp-convolution-triangle left right degree (- count 1))
       (* (lw-exp-term left (- count 1)) (lw-exp-sum right (- degree (- count 1)))))))

(defthm lw-exp-convolution-triangle-rational
  (implies (and (rationalp left) (rationalp right))
           (rationalp (lw-exp-convolution-triangle left right degree count)))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-ea-triangle-zero
         (implies (zp count) (equal (lw-exp-convolution-triangle left right degree count) 0))))
(local (defthm lw-ea-triangle-one
         (implies (and (rationalp right) (rationalp degree))
                  (equal (lw-exp-convolution-triangle left right degree 1) (lw-exp-sum right degree)))))
(local (defthm lw-ea-sum-zero
         (implies (zp index) (equal (lw-exp-sum value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-sum)))))

(local
 (defthm lw-ea-triangle-step
   (implies (and (rationalp left) (rationalp right) (natp degree) (natp count) (<= count (+ 1 degree)))
            (equal (lw-exp-convolution-triangle left right (+ 1 degree) count)
                   (+ (lw-exp-convolution-triangle left right degree count)
                      (lw-exp-convolution-row left right (+ 1 degree) count))))
   :hints (("Goal" :induct (lw-ea-countdown count)
                   :in-theory (disable (:definition lw-exp-convolution-triangle)))
           (and stable-under-simplificationp
                '(:use ((:instance lw-exp-sum-successor (value right) (index (- (+ 1 degree) count))))
                  :expand ((lw-exp-convolution-triangle left right (+ 1 degree) count)
                           (lw-exp-convolution-triangle left right degree count)
                           (lw-exp-convolution-row left right (+ 1 degree) count)
                           (lw-exp-sum right (+ 2 degree (- count)))))))))

(defthm lw-exp-convolution-triangle-exact
  (implies (and (rationalp left) (rationalp right) (natp degree))
           (equal (lw-exp-convolution-triangle left right degree (+ 1 degree)) (lw-exp-sum (+ left right) degree)))
  :hints (("Goal" :induct (lw-ea-countdown degree)
                  :in-theory (disable (:definition lw-exp-convolution-triangle) lw-ea-triangle-step))
          (and stable-under-simplificationp
               '(:use ((:instance lw-ea-triangle-step (degree (- degree 1)) (count degree))
                       (:instance lw-exp-convolution-row-exact))
                 :expand ((lw-exp-convolution-triangle left right degree (+ 1 degree))
                          (lw-exp-convolution-row left right degree (+ 1 degree))
                          (lw-exp-sum (+ left right) degree))
                 :in-theory (disable (:definition lw-exp-convolution-triangle) lw-ea-triangle-step)))))

(local (in-theory (disable (:definition lw-exp-convolution-triangle) lw-exp-convolution-triangle-exact)))

(local (defthm lw-ea-triangle-nonnegative
         (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right))
                  (<= 0 (lw-exp-convolution-triangle left right degree count)))
         :hints (("Goal" :induct (lw-ea-countdown count)
                         :in-theory (enable lw-exp-convolution-triangle) :nonlinearp t)
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-exp-term-nonnegative (value left) (index (- count 1)))
                              (:instance lw-exp-sum-at-least-one (value right) (index (- (+ 1 degree) count))))
                        :in-theory (disable lw-exp-term-nonnegative lw-exp-sum-at-least-one) :nonlinearp t)))
         :rule-classes (:rewrite :linear)))

(local (defthm lw-ea-triangle-monotone-count
         (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                       (natp small) (natp large) (<= small large))
                  (<= (lw-exp-convolution-triangle left right degree small)
                      (lw-exp-convolution-triangle left right degree large)))
         :hints (("Goal" :induct (lw-ea-countdown large))
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-exp-term-nonnegative (value left) (index (- large 1)))
                              (:instance lw-exp-sum-at-least-one (value right) (index (- (+ 1 degree) large))))
                        :expand ((lw-exp-convolution-triangle left right degree large))
                        :in-theory (disable lw-exp-term-nonnegative lw-exp-sum-at-least-one) :nonlinearp t)))
         :rule-classes nil))

(local (defthm lw-ea-triangle-rectangle-upper
         (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                       (natp degree) (natp count) (<= count (+ 1 degree)))
                  (<= (lw-exp-convolution-triangle left right degree count)
                      (* (lw-exp-sum left (- count 1)) (lw-exp-sum right degree))))
         :hints (("Goal" :induct (lw-ea-countdown count))
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-exp-sum-monotone-index (value right)
                                (small (- (+ 1 degree) count)) (large degree)))
                        :expand ((lw-exp-convolution-triangle left right degree count)
                                 (lw-exp-sum left (- count 1))) :nonlinearp t)))
         :rule-classes nil))

(local (defthm lw-ea-triangle-rectangle-lower
         (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                       (natp degree) (posp count) (natp right-index) (<= (+ (- count 1) right-index) degree))
                  (<= (* (lw-exp-sum left (- count 1)) (lw-exp-sum right right-index))
                      (lw-exp-convolution-triangle left right degree count)))
         :hints (("Goal" :induct (lw-ea-countdown count))
                 (and stable-under-simplificationp
                      '(:use ((:instance lw-exp-sum-monotone-index (value right)
                                (small right-index) (large (- (+ 1 degree) count)))
                              (:instance lw-exp-sum-monotone-index (value right) (small right-index) (large degree)))
                        :expand ((lw-exp-convolution-triangle left right degree count)
                                 (lw-exp-sum left (- count 1))) :nonlinearp t)))
         :rule-classes nil))

(defthm lw-exp-sum-product-upper
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right) (natp left-index) (natp right-index))
           (<= (* (lw-exp-sum left left-index) (lw-exp-sum right right-index))
               (lw-exp-sum (+ left right) (+ left-index right-index))))
  :hints (("Goal" :use ((:instance lw-ea-triangle-rectangle-lower
                          (degree (+ left-index right-index)) (count (+ 1 left-index)))
                        (:instance lw-ea-triangle-monotone-count
                          (degree (+ left-index right-index)) (small (+ 1 left-index)) (large (+ 1 left-index right-index)))
                        (:instance lw-exp-convolution-triangle-exact (degree (+ left-index right-index))))
                  :in-theory (disable (:definition lw-exp-convolution-triangle))))
  :rule-classes nil)

(defthm lw-exp-sum-addition-upper
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right) (natp index))
           (<= (lw-exp-sum (+ left right) index) (* (lw-exp-sum left index) (lw-exp-sum right index))))
  :hints (("Goal" :use ((:instance lw-ea-triangle-rectangle-upper (degree index) (count (+ 1 index)))
                        (:instance lw-exp-convolution-triangle-exact (degree index)))))
  :rule-classes nil)

(defthm lw-exp-partial-sum-upper
  (implies (and (rationalp value) (<= 0 value) (natp index))
           (<= (lw-exp-sum value index) (cdr (lw-exp-bounds value error))))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (epsilon error))
                        (:instance lw-exp-bounds-later-sum (index (+ index (lw-exp-index value error))))
                        (:instance lw-exp-sum-monotone-index (small index) (large (+ index (lw-exp-index value error)))))
                  :in-theory (disable lw-exp-index-adequate lw-exp-bounds-later-sum)))
  :rule-classes nil)

; Arbitrary precisions on the three enclosures. The cross bounds are
; exact: neither direction pays an approximation error or assumes an
; analytic product law.
(defthm lw-exp-bounds-product-transport
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right))
           (and (<= (* (car (lw-exp-bounds left left-error)) (car (lw-exp-bounds right right-error)))
                    (cdr (lw-exp-bounds (+ left right) sum-error)))
                (<= (car (lw-exp-bounds (+ left right) sum-error))
                    (* (cdr (lw-exp-bounds left left-error)) (cdr (lw-exp-bounds right right-error))))))
  :hints (("Goal"
           :use ((:instance lw-exp-index-adequate (value left) (epsilon left-error))
                 (:instance lw-exp-index-adequate (value right) (epsilon right-error))
                 (:instance lw-exp-index-adequate (value (+ left right)) (epsilon sum-error))
                 (:instance lw-exp-sum-product-upper (left-index (lw-exp-index left left-error))
                   (right-index (lw-exp-index right right-error)))
                 (:instance lw-exp-sum-addition-upper (index (lw-exp-index (+ left right) sum-error)))
                 (:instance lw-exp-partial-sum-upper (value (+ left right))
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error))) (error sum-error))
                 (:instance lw-exp-partial-sum-upper (value left) (index (lw-exp-index (+ left right) sum-error)) (error left-error))
                 (:instance lw-exp-partial-sum-upper (value right) (index (lw-exp-index (+ left right) sum-error)) (error right-error))
                 (:instance lw-exp-bounds-valid (value left) (epsilon left-error))
                 (:instance lw-exp-bounds-valid (value right) (epsilon right-error))
                 (:instance lw-exp-bounds-valid (value (+ left right)) (epsilon sum-error))
                 (:instance lw-exp-sum-at-least-one (value left) (index (lw-exp-index (+ left right) sum-error)))
                 (:instance lw-exp-sum-at-least-one (value right) (index (lw-exp-index (+ left right) sum-error))))
           :in-theory (e/d (lw-exp-bounds lw-exp-band)
                           (lw-exp-index-adequate lw-exp-bounds-valid lw-exp-sum-at-least-one))
           :nonlinearp t)))

(defthm lw-exp-bounds-square-shift
  (implies (and (rationalp value) (<= 0 value) (rationalp rate) (<= 0 rate))
           (<= (* (car (lw-exp-bounds value signal-error)) (car (lw-exp-bounds value signal-error))
                  (car (lw-exp-bounds (* rate value) rate-error)))
               (cdr (lw-exp-bounds (* (+ rate 2) value) total-error))))
  :hints (("Goal"
           :use ((:instance lw-exp-index-adequate (epsilon signal-error))
                 (:instance lw-exp-index-adequate (value (* rate value)) (epsilon rate-error))
                 (:instance lw-exp-sum-product-upper (left value) (right value)
                   (left-index (lw-exp-index value signal-error)) (right-index (lw-exp-index value signal-error)))
                 (:instance lw-exp-sum-product-upper (left (* 2 value)) (right (* rate value))
                   (left-index (* 2 (lw-exp-index value signal-error)))
                   (right-index (lw-exp-index (* rate value) rate-error)))
                 (:instance lw-exp-partial-sum-upper (value (* (+ rate 2) value))
                   (index (+ (* 2 (lw-exp-index value signal-error)) (lw-exp-index (* rate value) rate-error))) (error total-error))
                 (:instance lw-exp-sum-at-least-one (value (* rate value)) (index (lw-exp-index (* rate value) rate-error))))
           :in-theory (e/d (lw-exp-bounds lw-exp-band) (lw-exp-index-adequate lw-exp-sum-at-least-one))
           :nonlinearp t)))
