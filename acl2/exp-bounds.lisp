(in-package "ACL2")

(include-book "window-index")

(local (defthm lw-eb-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eb-two-halves
         (implies (rationalp value) (equal (* 2 1/2 value) value))
         :hints (("Goal" :use ((:instance associativity-of-* (x 2) (y 1/2) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eb-add-cancel
         (implies (and (rationalp value) (rationalp rest))
                  (equal (+ value (- value) rest) rest))))

; Taylor terms and partial sums are exact rationals. A band after index n
; encloses every later partial sum once 2*x <= n+2. This arithmetic fact,
; not an assumed real exponential, is the foundation of the evaluator.
(defun lw-exp-term (value index)
  (declare (xargs :measure (nfix index)))
  (if (zp index) 1
    (/ (* value (lw-exp-term value (- index 1))) index)))

(defun lw-exp-sum (value index)
  (declare (xargs :measure (nfix index)))
  (if (zp index) 1
    (+ (lw-exp-sum value (- index 1)) (lw-exp-term value index))))

(defun lw-exp-band (value index)
  (let ((lower (lw-exp-sum value index)))
    (cons lower (+ lower (* 2 (lw-exp-term value (+ 1 (nfix index))))))))

(defthm lw-exp-term-rational
  (implies (rationalp value) (rationalp (lw-exp-term value index)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-exp-term-nonnegative
  (implies (and (rationalp value) (<= 0 value))
           (<= 0 (lw-exp-term value index)))
  :hints (("Goal" :induct (lw-exp-term value index) :nonlinearp t))
  :rule-classes (:rewrite :linear))

(defthm lw-exp-sum-rational
  (implies (rationalp value) (rationalp (lw-exp-sum value index)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-exp-sum-at-least-one
  (implies (and (rationalp value) (<= 0 value))
           (<= 1 (lw-exp-sum value index)))
  :hints (("Goal" :induct (lw-exp-sum value index) :in-theory (disable lw-exp-term))))

(defthm lw-exp-band-valid
  (implies (and (rationalp value) (<= 0 value))
           (and (lw-intervalp (lw-exp-band value index))
                (<= 1 (car (lw-exp-band value index)))))
  :hints (("Goal" :in-theory (disable lw-exp-term lw-exp-sum))))

(defthm lw-exp-band-width
  (implies (rationalp value)
           (equal (- (cdr (lw-exp-band value index)) (car (lw-exp-band value index)))
                  (* 2 (lw-exp-term value (+ 1 (nfix index))))))
  :hints (("Goal" :in-theory (disable lw-exp-term lw-exp-sum))))

(defthm lw-exp-term-successor
  (implies (natp index)
           (equal (lw-exp-term value (+ 1 index))
                  (/ (* value (lw-exp-term value index)) (+ 1 index))))
  :hints (("Goal" :expand ((lw-exp-term value (+ 1 index)))
                  :in-theory (disable lw-exp-term)))
  :rule-classes nil)

(defthm lw-exp-sum-successor
  (implies (natp index)
           (equal (lw-exp-sum value (+ 1 index))
                  (+ (lw-exp-sum value index) (lw-exp-term value (+ 1 index)))))
  :hints (("Goal" :expand ((lw-exp-sum value (+ 1 index)))
                  :in-theory (disable lw-exp-sum)))
  :rule-classes nil)

(defthm lw-exp-term-half-step
  (implies (and (rationalp value) (<= 0 value) (natp index)
                (<= (* 2 value) (+ 1 index)))
           (<= (lw-exp-term value (+ 1 index)) (/ (lw-exp-term value index) 2)))
  :hints (("Goal"
           :use (lw-exp-term-successor
                 (:instance lw-positive-division-bound
                   (numerator (* value (lw-exp-term value index))) (divisor (+ 1 index))
                   (bound (/ (lw-exp-term value index) 2))))
           :in-theory (disable lw-exp-term)
           :nonlinearp t)))

(defthm lw-exp-band-step-nested
  (implies (and (rationalp value) (<= 0 value) (natp index)
                (<= (* 2 value) (+ 2 index)))
           (and (<= (car (lw-exp-band value index)) (car (lw-exp-band value (+ 1 index))))
                (<= (cdr (lw-exp-band value (+ 1 index))) (cdr (lw-exp-band value index)))))
  :hints (("Goal" :use (lw-exp-sum-successor
                        (:instance lw-exp-term-half-step (index (+ 1 index))))
                  :in-theory (disable lw-exp-term lw-exp-sum lw-exp-term-half-step))))

(local
 (defun lw-eb-countdown (large small)
   (declare (xargs :measure (nfix large)))
   (if (or (zp large) (<= large small)) nil
     (lw-eb-countdown (- large 1) small))))

(defthm lw-exp-band-nested
  (implies (and (rationalp value) (<= 0 value) (natp small) (natp large)
                (<= (* 2 value) (+ 2 small)) (<= small large))
           (and (<= (car (lw-exp-band value small)) (car (lw-exp-band value large)))
                (<= (cdr (lw-exp-band value large)) (cdr (lw-exp-band value small)))))
  :hints (("Goal" :induct (lw-eb-countdown large small)
                  :in-theory (disable lw-exp-band lw-exp-term lw-exp-sum))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-band-step-nested (index (- large 1))))
                 :in-theory (disable lw-exp-band lw-exp-term lw-exp-sum lw-exp-band-step-nested))))
  :rule-classes nil)

(defthm lw-exp-later-partial-sum-enclosed
  (implies (and (rationalp value) (<= 0 value) (natp small) (natp large)
                (<= (* 2 value) (+ 2 small)) (<= small large))
           (and (<= (car (lw-exp-band value small)) (lw-exp-sum value large))
                (<= (lw-exp-sum value large) (cdr (lw-exp-band value small)))))
  :hints (("Goal" :use (lw-exp-band-nested (:instance lw-exp-band-valid (index large)))
                  :in-theory (disable lw-exp-sum lw-exp-term))))

(defthm lw-exp-term-geometric-tail
  (implies (and (rationalp value) (<= 0 value) (natp index) (natp steps)
                (<= (* 2 value) (+ 1 index)))
           (<= (lw-exp-term value (+ index steps))
               (lw-halved-width (lw-exp-term value index) steps)))
  :hints (("Goal" :induct (lw-halved-width (lw-exp-term value index) steps)
                  :in-theory (disable lw-exp-term))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-term-half-step (index (+ -1 index steps))))
                 :in-theory (disable lw-exp-term lw-exp-term-half-step)))))

(defun lw-exp-start-index (value)
  (+ 1 (lw-ceiling-rational (* 2 value))))

(defthm lw-exp-start-index-natural
  (natp (lw-exp-start-index value))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-exp-start-index-adequate
  (implies (and (rationalp value) (<= 0 value))
           (<= (* 2 value) (lw-exp-start-index value)))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value (* 2 value))))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket))))

(defun lw-exp-initial-width (value)
  (* 2 (lw-exp-term value (+ 1 (lw-exp-start-index value)))))

(defun lw-exp-depth (value epsilon)
  (lw-halving-depth (lw-exp-initial-width value) epsilon
                    (lw-precision-fuel (lw-exp-initial-width value) epsilon)))

(defun lw-exp-index (value epsilon)
  (+ (lw-exp-start-index value) (lw-exp-depth value epsilon)))

(defun lw-exp-bounds (value epsilon)
  (lw-exp-band value (lw-exp-index value epsilon)))

(defthm lw-exp-index-adequate
  (implies (and (rationalp value) (<= 0 value))
           (and (natp (lw-exp-index value epsilon))
                (<= (lw-exp-start-index value) (lw-exp-index value epsilon))
                (<= (* 2 value) (lw-exp-index value epsilon))))
  :hints (("Goal" :use (lw-exp-start-index-adequate)
                  :in-theory (disable lw-exp-start-index lw-exp-depth lw-exp-start-index-adequate))))

(defthm lw-exp-bounds-valid
  (implies (and (rationalp value) (<= 0 value))
           (and (lw-intervalp (lw-exp-bounds value epsilon))
                (<= 1 (car (lw-exp-bounds value epsilon)))))
  :hints (("Goal" :use ((:instance lw-exp-band-valid (index (lw-exp-index value epsilon))))
                  :in-theory (disable lw-exp-index lw-exp-band lw-exp-band-valid))))

(defthm lw-exp-bounds-width
  (implies (and (rationalp value) (<= 0 value) (rationalp epsilon) (< 0 epsilon))
           (<= (- (cdr (lw-exp-bounds value epsilon)) (car (lw-exp-bounds value epsilon))) epsilon))
  :hints (("Goal"
           :use ((:instance lw-exp-term-geometric-tail
                   (index (+ 1 (lw-exp-start-index value))) (steps (lw-exp-depth value epsilon)))
                 (:instance lw-halving-depth-adequate
                   (width (lw-exp-initial-width value))
                   (fuel (lw-precision-fuel (lw-exp-initial-width value) epsilon)))
                 (:instance lw-precision-fuel-adequate (width (lw-exp-initial-width value)))
                 lw-exp-start-index-adequate
                 (:instance lw-halved-width-half
                   (width (* 2 (lw-exp-term value (+ 1 (lw-exp-start-index value)))))
                   (steps (lw-exp-depth value epsilon))))
           :in-theory (disable lw-exp-term lw-exp-sum lw-exp-start-index lw-exp-start-index-adequate
                               lw-exp-term-geometric-tail lw-halved-width lw-halved-width-half
                               lw-halving-depth lw-halving-depth-adequate lw-precision-fuel lw-precision-fuel-adequate))))

(defthm lw-exp-bounds-overlap
  (implies (and (rationalp value) (<= 0 value))
           (<= (car (lw-exp-bounds value left-error)) (cdr (lw-exp-bounds value right-error))))
  :hints (("Goal" :cases ((<= (lw-exp-index value left-error) (lw-exp-index value right-error)))
                  :use ((:instance lw-exp-band-nested
                          (small (lw-exp-index value left-error)) (large (lw-exp-index value right-error)))
                        (:instance lw-exp-band-nested
                          (small (lw-exp-index value right-error)) (large (lw-exp-index value left-error)))
                        (:instance lw-exp-index-adequate (epsilon left-error))
                        (:instance lw-exp-index-adequate (epsilon right-error))
                        (:instance lw-exp-band-valid (index (lw-exp-index value left-error)))
                        (:instance lw-exp-band-valid (index (lw-exp-index value right-error))))
                  :in-theory (disable lw-exp-index lw-exp-index-adequate lw-exp-band lw-exp-band-valid))))

(defthm lw-exp-bounds-lower-cauchy
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-exp-bounds value left-error)) (car (lw-exp-bounds value right-error))))
               (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-exp-bounds-overlap)
                        (:instance lw-exp-bounds-overlap (left-error right-error) (right-error left-error))
                        (:instance lw-exp-bounds-width (epsilon left-error))
                        (:instance lw-exp-bounds-width (epsilon right-error))
                        (:instance lw-exp-bounds-valid (epsilon left-error))
                        (:instance lw-exp-bounds-valid (epsilon right-error)))
                  :in-theory (disable lw-exp-bounds lw-exp-bounds-overlap lw-exp-bounds-width lw-exp-bounds-valid))))

(local
 (defthm lw-eb-reciprocal-width
   (implies (and (rationalp lower) (rationalp upper) (<= 1 lower) (<= lower upper))
            (<= (- (/ lower) (/ upper)) (- upper lower)))
   :hints (("Goal" :use ((:instance inverse-of-* (x lower))
                         (:instance inverse-of-* (x upper))
                         (:instance lw-reciprocal-antitone (left 1) (right lower))
                         (:instance lw-reciprocal-antitone (left lower) (right upper)))
                   :in-theory (disable inverse-of-* lw-reciprocal-antitone)
                   :nonlinearp t))
   :rule-classes nil))

(defun lw-exp-neg-bounds (value epsilon)
  (let ((bounds (lw-exp-bounds value epsilon)))
    (cons (/ (cdr bounds)) (/ (car bounds)))))

(defthm lw-exp-neg-bounds-valid
  (implies (and (rationalp value) (<= 0 value))
           (and (lw-intervalp (lw-exp-neg-bounds value epsilon))
                (< 0 (car (lw-exp-neg-bounds value epsilon)))
                (<= (cdr (lw-exp-neg-bounds value epsilon)) 1)))
  :hints (("Goal" :use (lw-exp-bounds-valid
                        (:instance lw-reciprocal-antitone
                          (left (car (lw-exp-bounds value epsilon))) (right (cdr (lw-exp-bounds value epsilon))))
                        (:instance lw-reciprocal-antitone (left 1) (right (car (lw-exp-bounds value epsilon)))))
                  :in-theory (disable lw-exp-bounds lw-exp-bounds-valid lw-exp-bounds-overlap
                                      lw-reciprocal-antitone))))

(defthm lw-exp-neg-bounds-width
  (implies (and (rationalp value) (<= 0 value) (rationalp epsilon) (< 0 epsilon))
           (<= (- (cdr (lw-exp-neg-bounds value epsilon)) (car (lw-exp-neg-bounds value epsilon))) epsilon))
  :hints (("Goal" :use (lw-exp-bounds-valid lw-exp-bounds-width
                        (:instance lw-eb-reciprocal-width
                          (lower (car (lw-exp-bounds value epsilon))) (upper (cdr (lw-exp-bounds value epsilon)))))
                  :in-theory (disable lw-exp-bounds lw-exp-bounds-valid lw-exp-bounds-width lw-exp-bounds-overlap))))

(defthm lw-exp-neg-bounds-overlap
  (implies (and (rationalp value) (<= 0 value))
           (<= (car (lw-exp-neg-bounds value left-error)) (cdr (lw-exp-neg-bounds value right-error))))
  :hints (("Goal" :use ((:instance lw-exp-bounds-valid (epsilon left-error))
                        (:instance lw-exp-bounds-valid (epsilon right-error))
                        (:instance lw-exp-bounds-overlap (left-error right-error) (right-error left-error))
                        (:instance lw-reciprocal-antitone
                          (left (car (lw-exp-bounds value right-error)))
                          (right (cdr (lw-exp-bounds value left-error)))))
                  :in-theory (disable lw-exp-bounds lw-exp-bounds-valid lw-exp-bounds-overlap
                                      lw-reciprocal-antitone))))

(assert-event
 (let ((bounds (lw-exp-bounds 1 1/100)))
   (and (lw-intervalp bounds) (< 2 (car bounds)) (< (cdr bounds) 3)
        (<= (- (cdr bounds) (car bounds)) 1/100))))

(assert-event
 (let ((bounds (lw-exp-neg-bounds 1 1/100)))
   (and (equal (lw-exp-bounds 0 1/100) (cons 1 1))
        (equal (lw-exp-neg-bounds 0 1/100) (cons 1 1))
        (< 1/3 (car bounds)) (< (cdr bounds) 1/2)
        (<= (- (cdr bounds) (car bounds)) 1/100))))
