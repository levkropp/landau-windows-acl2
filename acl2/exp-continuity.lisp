(in-package "ACL2")

(include-book "exp-bounds")

(local (in-theory (disable lw-exp-bounds-overlap)))

(local (defthm lw-ec-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ec-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ec-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))
         :hints (("Goal" :use ((:instance lw-ec-times-negative (a b) (b a)))
                         :in-theory (disable lw-ec-times-negative)))))
(local (defthm lw-ec-times-zero (equal (* 0 a) 0)))
(local (defthm lw-ec-times-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-ec-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-ec-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ec-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-ec-left-commutes)))))
(local (defthm lw-ec-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c))
                  (<= (* a c) (* b c)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defun lw-ec-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-ec-countdown (- index 1)))))
(local (defthm lw-ec-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))))
(local (defthm lw-ec-sum-zero
         (implies (zp index) (equal (lw-exp-sum value index) 1))))
(local (defthm lw-ec-term-one
         (implies (rationalp value) (equal (lw-exp-term value 1) value))))
(local (defthm lw-ec-sum-one
         (implies (rationalp value) (equal (lw-exp-sum value 1) (+ 1 value)))))

(defthm lw-exp-term-multiplied
  (implies (and (rationalp value) (posp index))
           (equal (* index (lw-exp-term value index)) (* value (lw-exp-term value (- index 1)))))
  :hints (("Goal" :expand ((lw-exp-term value index)) :in-theory (disable lw-exp-term))))

(local
 (defthm lw-ec-derivative-step
   (implies (and (rationalp cap) (posp index))
            (equal (* cap (if (zp (- index 1)) 0 (lw-exp-term cap (- index 2))))
                   (* (- index 1) (lw-exp-term cap (- index 1)))))
   :hints (("Goal" :cases ((equal index 1))
                   :use ((:instance lw-exp-term-multiplied (value cap) (index (- index 1))))
                   :in-theory (disable lw-exp-term lw-exp-term-multiplied)))
   :rule-classes nil))

(defthm lw-exp-term-monotone
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right) (natp index))
           (<= (lw-exp-term left index) (lw-exp-term right index)))
  :hints (("Goal" :induct (lw-ec-countdown index)
                  :in-theory (disable (:definition lw-exp-term)))
          (and stable-under-simplificationp
               '(:expand ((lw-exp-term left index) (lw-exp-term right index))
                 :use ((:instance lw-exp-term-nonnegative (value left) (index (- index 1)))
                       (:instance lw-exp-term-nonnegative (value right) (index (- index 1)))
                       (:instance lw-ec-multiply-order
                         (a (lw-exp-term left (- index 1))) (b (lw-exp-term right (- index 1))) (c left))
                       (:instance lw-ec-multiply-order
                         (a left) (b right) (c (lw-exp-term right (- index 1))))
                       (:instance lw-ec-multiply-order
                         (a (* left (lw-exp-term left (- index 1))))
                         (b (* right (lw-exp-term right (- index 1)))) (c (/ index))))
                 :nonlinearp t))))

(defthm lw-exp-sum-monotone-argument
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right) (natp index))
           (<= (lw-exp-sum left index) (lw-exp-sum right index)))
  :hints (("Goal" :induct (lw-ec-countdown index) :in-theory (disable lw-exp-term lw-exp-term-monotone))
          (and stable-under-simplificationp '(:use (lw-exp-term-monotone)))))

(defthm lw-exp-sum-monotone-index
  (implies (and (rationalp value) (<= 0 value) (natp small) (natp large) (<= small large))
           (<= (lw-exp-sum value small) (lw-exp-sum value large)))
  :hints (("Goal" :induct (lw-ec-countdown large)
                  :in-theory (disable lw-exp-term (:definition lw-exp-sum)))
          (and stable-under-simplificationp
               '(:expand ((lw-exp-sum value large)))))
  :rule-classes nil)

; The derivative majorant for a Taylor term is the preceding Taylor term.
; This finite algebraic step supplies that fact without a derivative oracle.
(local
 (defthm lw-ec-term-step
   (implies (and (rationalp left) (rationalp right) (rationalp cap)
                 (<= 0 left) (<= left right) (<= right cap)
                 (rationalp low) (rationalp high) (<= 0 low) (<= low high)
                 (rationalp top) (<= high top) (rationalp prev) (<= 0 prev)
                 (rationalp index) (< 0 index)
                 (<= (- high low) (* (- right left) prev))
                 (equal (* cap prev) (* (- index 1) top)))
            (<= (- (/ (* right high) index) (/ (* left low) index)) (* (- right left) top)))
   :hints (("Goal" :use ((:instance lw-ec-multiply-order
                          (a (- high low)) (b (* (- right left) prev)) (c left))
                         (:instance lw-ec-multiply-order
                          (a left) (b cap) (c (* (- right left) prev)))
                         (:instance lw-ec-multiply-order
                          (a high) (b top) (c (- right left)))
                         (:instance lw-positive-division-bound
                          (numerator (- (* right high) (* left low)))
                          (divisor index) (bound (* (- right left) top))))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-exp-term-lipschitz-ordered
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= left right) (<= right cap) (natp index))
           (<= (- (lw-exp-term right index) (lw-exp-term left index))
               (* (- right left) (if (zp index) 0 (lw-exp-term cap (- index 1))))))
  :hints (("Goal" :induct (lw-ec-countdown index)
                  :in-theory (disable (:definition lw-exp-term) lw-exp-term-monotone))
          (and stable-under-simplificationp
               '(:expand ((lw-exp-term left index) (lw-exp-term right index))
                 :use ((:instance lw-exp-term-monotone (index (- index 1)))
                       (:instance lw-exp-term-monotone (left right) (right cap) (index (- index 1)))
                       lw-ec-derivative-step
                       (:instance lw-ec-term-step
                         (low (lw-exp-term left (- index 1)))
                         (high (lw-exp-term right (- index 1)))
                         (top (lw-exp-term cap (- index 1)))
                         (prev (if (zp (- index 1)) 0 (lw-exp-term cap (- index 2))))))
                 :nonlinearp t))))

(defthm lw-exp-sum-lipschitz-ordered
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= left right) (<= right cap) (natp index))
           (<= (- (lw-exp-sum right index) (lw-exp-sum left index))
               (* (- right left) (if (zp index) 0 (lw-exp-sum cap (- index 1))))))
  :hints (("Goal" :induct (lw-ec-countdown index)
                  :in-theory (disable lw-exp-term lw-exp-sum lw-exp-term-lipschitz-ordered))
          (and stable-under-simplificationp
               '(:expand ((lw-exp-sum left index) (lw-exp-sum right index) (lw-exp-sum cap (- index 1)))
                 :use (lw-exp-term-lipschitz-ordered)
                 :nonlinearp t))))

(defun lw-exp-lipschitz-cap (cap) (cdr (lw-exp-bounds cap 1)))

(defthm lw-exp-lipschitz-cap-valid
  (implies (and (rationalp cap) (<= 0 cap))
           (and (rationalp (lw-exp-lipschitz-cap cap)) (<= 1 (lw-exp-lipschitz-cap cap))))
  :hints (("Goal" :use ((:instance lw-exp-bounds-valid (value cap) (epsilon 1)))
                  :in-theory (disable lw-exp-bounds lw-exp-bounds-valid))))

(defthm lw-exp-sum-uniform-bound
  (implies (and (rationalp cap) (<= 0 cap) (natp index))
           (<= (lw-exp-sum cap index) (lw-exp-lipschitz-cap cap)))
  :hints (("Goal" :cases ((<= index (lw-exp-index cap 1)))
                  :use ((:instance lw-exp-index-adequate (value cap) (epsilon 1))
                        (:instance lw-exp-band-valid (value cap) (index (lw-exp-index cap 1)))
                        (:instance lw-exp-sum-monotone-index (value cap) (small index) (large (lw-exp-index cap 1)))
                        (:instance lw-exp-later-partial-sum-enclosed
                          (value cap) (small (lw-exp-index cap 1)) (large index)))
                  :in-theory (disable lw-exp-term lw-exp-sum lw-exp-index
                                      lw-exp-index-adequate lw-exp-band-valid
                                      lw-exp-later-partial-sum-enclosed))))

(defthm lw-exp-sum-spatial-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap) (natp index))
           (<= (abs (- (lw-exp-sum left index) (lw-exp-sum right index)))
               (* (lw-exp-lipschitz-cap cap) (abs (- left right)))))
  :hints (("Goal" :cases ((<= left right) (zp index))
                  :use (lw-exp-lipschitz-cap-valid
                        (:instance lw-exp-sum-lipschitz-ordered)
                        (:instance lw-exp-sum-lipschitz-ordered (left right) (right left))
                        (:instance lw-exp-sum-monotone-argument)
                        (:instance lw-exp-sum-monotone-argument (left right) (right left))
                        (:instance lw-exp-sum-uniform-bound (index (nfix (- index 1)))))
                  :in-theory (disable lw-exp-term lw-exp-sum lw-exp-lipschitz-cap
                                      lw-exp-lipschitz-cap-valid lw-exp-sum-lipschitz-ordered
                                      lw-exp-sum-monotone-argument lw-exp-sum-uniform-bound)
                  :nonlinearp t)))

(defthm lw-exp-bounds-later-sum
  (implies (and (rationalp value) (<= 0 value) (natp index) (<= (lw-exp-index value error) index))
           (and (<= (car (lw-exp-bounds value error)) (lw-exp-sum value index))
                (<= (lw-exp-sum value index) (cdr (lw-exp-bounds value error)))))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (epsilon error))
                        (:instance lw-exp-later-partial-sum-enclosed
                          (small (lw-exp-index value error)) (large index)))
                  :in-theory (disable lw-exp-term lw-exp-sum lw-exp-index
                                      lw-exp-index-adequate lw-exp-later-partial-sum-enclosed))))

; Comparing against a common later partial sum removes all precision loss
; in the lower-versus-upper transport theorem.
(defthm lw-exp-bounds-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap))
           (<= (- (car (lw-exp-bounds left left-error)) (cdr (lw-exp-bounds right right-error)))
               (* (lw-exp-lipschitz-cap cap) (abs (- left right)))))
  :hints (("Goal"
           :use ((:instance lw-exp-index-adequate (value left) (epsilon left-error))
                 (:instance lw-exp-index-adequate (value right) (epsilon right-error))
                 (:instance lw-exp-bounds-later-sum (value left) (error left-error)
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error))))
                 (:instance lw-exp-bounds-later-sum (value right) (error right-error)
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error))))
                 (:instance lw-exp-sum-spatial-bound
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error)))))
           :in-theory (disable lw-exp-bounds lw-exp-index lw-exp-sum lw-exp-lipschitz-cap
                               lw-exp-index-adequate lw-exp-bounds-later-sum lw-exp-sum-spatial-bound))))

(defthm lw-exp-bounds-monotone-overlap
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right))
           (<= (car (lw-exp-bounds left left-error)) (cdr (lw-exp-bounds right right-error))))
  :hints (("Goal"
           :use ((:instance lw-exp-index-adequate (value left) (epsilon left-error))
                 (:instance lw-exp-index-adequate (value right) (epsilon right-error))
                 (:instance lw-exp-bounds-later-sum (value left) (error left-error)
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error))))
                 (:instance lw-exp-bounds-later-sum (value right) (error right-error)
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error))))
                 (:instance lw-exp-sum-monotone-argument
                   (index (+ (lw-exp-index left left-error) (lw-exp-index right right-error)))))
           :in-theory (disable lw-exp-bounds lw-exp-index lw-exp-sum
                               lw-exp-index-adequate lw-exp-bounds-later-sum lw-exp-sum-monotone-argument))))

(local (in-theory (disable lw-exp-bounds-monotone-overlap)))

(defthm lw-exp-bounds-spatial-cauchy
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-exp-bounds left left-error)) (car (lw-exp-bounds right right-error))))
               (+ (* (lw-exp-lipschitz-cap cap) (abs (- left right))) left-error right-error)))
  :hints (("Goal" :use (lw-exp-bounds-transport
                        (:instance lw-exp-bounds-transport
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-exp-bounds-width (value left) (epsilon left-error))
                        (:instance lw-exp-bounds-width (value right) (epsilon right-error))
                        (:instance lw-exp-bounds-valid (value left) (epsilon left-error))
                        (:instance lw-exp-bounds-valid (value right) (epsilon right-error)))
                  :in-theory (disable lw-exp-bounds lw-exp-lipschitz-cap lw-exp-bounds-transport
                                      lw-exp-bounds-width lw-exp-bounds-valid))))

(local
 (defthm lw-ec-reciprocal-width
   (implies (and (rationalp lower) (rationalp upper) (<= 1 lower) (<= lower upper))
            (<= (- (/ lower) (/ upper)) (- upper lower)))
   :hints (("Goal" :use ((:instance inverse-of-* (x lower))
                         (:instance inverse-of-* (x upper))
                         (:instance lw-reciprocal-antitone (left 1) (right lower))
                         (:instance lw-reciprocal-antitone (left lower) (right upper)))
                   :in-theory (disable inverse-of-* lw-reciprocal-antitone) :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ec-reciprocal-transport
   (implies (and (rationalp a) (rationalp b) (<= 1 a) (<= 1 b)
                 (rationalp radius) (<= 0 radius) (<= (- b a) radius))
            (<= (- (/ a) (/ b)) radius))
   :hints (("Goal" :cases ((<= a b))
                   :use ((:instance lw-ec-reciprocal-width (lower a) (upper b))
                         (:instance lw-reciprocal-antitone (left b) (right a)))
                   :in-theory (disable lw-reciprocal-antitone)))
   :rule-classes nil))

(defthm lw-exp-neg-bounds-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap))
           (<= (- (car (lw-exp-neg-bounds left left-error)) (cdr (lw-exp-neg-bounds right right-error)))
               (* (lw-exp-lipschitz-cap cap) (abs (- left right)))))
  :hints (("Goal" :use (lw-exp-lipschitz-cap-valid
                        (:instance lw-exp-bounds-transport
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-exp-bounds-valid (value left) (epsilon left-error))
                        (:instance lw-exp-bounds-valid (value right) (epsilon right-error))
                        (:instance lw-ec-reciprocal-transport
                          (a (cdr (lw-exp-bounds left left-error))) (b (car (lw-exp-bounds right right-error)))
                          (radius (* (lw-exp-lipschitz-cap cap) (abs (- left right))))))
                  :in-theory (disable lw-exp-bounds lw-exp-lipschitz-cap lw-exp-lipschitz-cap-valid
                                      lw-exp-bounds-transport lw-exp-bounds-valid)
                  :nonlinearp t)))

(defthm lw-exp-neg-bounds-spatial-cauchy
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-exp-neg-bounds left left-error)) (car (lw-exp-neg-bounds right right-error))))
               (+ (* (lw-exp-lipschitz-cap cap) (abs (- left right))) left-error right-error)))
  :hints (("Goal" :use (lw-exp-neg-bounds-transport
                        (:instance lw-exp-neg-bounds-transport
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-exp-neg-bounds-width (value left) (epsilon left-error))
                        (:instance lw-exp-neg-bounds-width (value right) (epsilon right-error))
                        (:instance lw-exp-neg-bounds-valid (value left) (epsilon left-error))
                        (:instance lw-exp-neg-bounds-valid (value right) (epsilon right-error)))
                  :in-theory (disable lw-exp-neg-bounds lw-exp-lipschitz-cap lw-exp-neg-bounds-transport
                                      lw-exp-neg-bounds-width lw-exp-neg-bounds-valid lw-exp-neg-bounds-overlap))))

(assert-event
 (and (<= (abs (- (car (lw-exp-bounds 1/2 1/10)) (car (lw-exp-bounds 2/3 1/8))))
          (+ (* (lw-exp-lipschitz-cap 1) 1/6) 1/10 1/8))
      (<= (- (car (lw-exp-bounds 2/3 1/8)) (cdr (lw-exp-bounds 1/2 1/10)))
          (* (lw-exp-lipschitz-cap 1) 1/6))))
