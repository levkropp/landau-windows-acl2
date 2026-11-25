(in-package "ACL2")

(include-book "signal-continuity")
(include-book "exp-bounds")

(local (defthm lw-ls-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ls-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ls-minus-one-product
         (implies (rationalp value) (equal (* -1 value) (- value)))))
(local (defthm lw-ls-add-cancel
         (implies (and (rationalp value) (rationalp rest))
                  (equal (+ value (- value) rest) rest))))
(local (defthm lw-ls-sum-left-distribute
         (implies (and (rationalp left) (rationalp right) (rationalp factor))
                  (equal (* (+ left right) factor) (+ (* left factor) (* right factor))))
         :hints (("Goal" :use ((:instance distributivity (x factor) (y left) (z right)))
                         :in-theory (disable distributivity)))))

(defun lw-log-signal-cap (value) (+ 1 (cdr (lw-exp-bounds value 1))))
(defun lw-log-signal-lipschitz (value) (lw-signal-lipschitz-factor (lw-log-signal-cap value) 0))
(defun lw-log-signal-budget (error) (min 1 error))
(defun lw-log-signal-delta (value error)
  (/ (lw-log-signal-budget error) (* 4 (+ 1 (lw-log-signal-lipschitz value)))))

; This rational point is strictly greater than 1, even when u=0. It is
; between exp(u) and exp(u)+delta in the real interpretation, since the
; exponential band's width is at most delta.
(defun lw-log-signal-point (value error)
  (let ((delta (lw-log-signal-delta value error)))
    (+ (car (lw-exp-bounds value delta)) delta)))

(defun lw-log-signal-margin (value error)
  (* (lw-log-signal-lipschitz value) (lw-log-signal-delta value error)))

(defun lw-log-signal-base (value error)
  (lw-signal-bounds (lw-log-signal-point value error) 0 0 1 (/ (lw-log-signal-budget error) 2)))

(defun lw-log-signal-bounds (value error)
  (let ((margin (lw-log-signal-margin value error)))
    (lw-interval-add (lw-log-signal-base value error) (cons (- margin) margin))))

(defthm lw-log-signal-budget-valid
  (implies (and (rationalp error) (< 0 error))
           (and (rationalp (lw-log-signal-budget error))
                (< 0 (lw-log-signal-budget error))
                (<= (lw-log-signal-budget error) 1)
                (<= (lw-log-signal-budget error) error))))

(defthm lw-log-signal-cap-valid
  (implies (and (rationalp value) (<= 0 value))
           (and (rationalp (lw-log-signal-cap value)) (<= 2 (lw-log-signal-cap value))))
  :hints (("Goal" :use ((:instance lw-exp-bounds-valid (epsilon 1)))
                  :in-theory (disable lw-exp-bounds lw-exp-bounds-valid lw-exp-bounds-overlap))))

(defthm lw-log-signal-lipschitz-valid
  (implies (and (rationalp value) (<= 0 value))
           (and (rationalp (lw-log-signal-lipschitz value)) (<= 0 (lw-log-signal-lipschitz value))))
  :hints (("Goal" :use (lw-log-signal-cap-valid
                        (:instance lw-signal-lipschitz-factor-valid (cap (lw-log-signal-cap value)) (ceiling 0)))
                  :in-theory (disable lw-log-signal-cap lw-log-signal-cap-valid
                                      lw-signal-lipschitz-factor lw-signal-lipschitz-factor-valid))))

(defthm lw-log-signal-delta-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (rationalp (lw-log-signal-delta value error))
                (< 0 (lw-log-signal-delta value error))
                (<= (lw-log-signal-delta value error) 1)
                (<= (lw-log-signal-margin value error) (/ (lw-log-signal-budget error) 4))))
  :hints (("Goal" :use (lw-log-signal-budget-valid lw-log-signal-lipschitz-valid
                        (:instance lw-positive-division-bound
                          (numerator (lw-log-signal-budget error))
                          (divisor (* 4 (+ 1 (lw-log-signal-lipschitz value)))) (bound 1))
                        (:instance lw-positive-division-bound
                          (numerator (* (lw-log-signal-lipschitz value) (lw-log-signal-budget error)))
                          (divisor (* 4 (+ 1 (lw-log-signal-lipschitz value))))
                          (bound (/ (lw-log-signal-budget error) 4))))
                  :in-theory (disable lw-log-signal-budget lw-log-signal-budget-valid
                                      lw-log-signal-lipschitz lw-log-signal-lipschitz-valid)
                  :nonlinearp t)))

(defthm lw-log-signal-point-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (rationalp (lw-log-signal-point value error))
                (< 1 (lw-log-signal-point value error))
                (<= (lw-log-signal-point value error) (lw-log-signal-cap value))))
  :hints (("Goal" :use (lw-log-signal-delta-valid
                        (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value error)))
                        (:instance lw-exp-bounds-valid (epsilon 1))
                        (:instance lw-exp-bounds-overlap
                          (left-error (lw-log-signal-delta value error)) (right-error 1)))
                  :in-theory (disable lw-log-signal-delta lw-log-signal-delta-valid
                                      lw-exp-bounds lw-exp-bounds-valid lw-exp-bounds-overlap))))

(defthm lw-log-signal-margin-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (rationalp (lw-log-signal-margin value error)) (<= 0 (lw-log-signal-margin value error))))
  :hints (("Goal" :use (lw-log-signal-delta-valid lw-log-signal-lipschitz-valid)
                  :in-theory (disable lw-log-signal-delta lw-log-signal-lipschitz
                                      lw-log-signal-delta-valid lw-log-signal-lipschitz-valid)
                  :nonlinearp t)))

(defthm lw-log-signal-base-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (lw-intervalp (lw-log-signal-base value error))
                (<= (lw-interval-width (lw-log-signal-base value error)) (/ (lw-log-signal-budget error) 2))))
  :hints (("Goal" :use (lw-log-signal-budget-valid lw-log-signal-point-valid
                        (:instance lw-signal-bounds-valid (value (lw-log-signal-point value error))
                          (ceiling 0) (numerator 0) (denominator 1) (error (/ (lw-log-signal-budget error) 2)))
                        (:instance lw-signal-bounds-width (value (lw-log-signal-point value error))
                          (ceiling 0) (numerator 0) (denominator 1) (error (/ (lw-log-signal-budget error) 2))))
                  :in-theory (disable lw-log-signal-point lw-log-signal-budget
                                      lw-log-signal-point-valid lw-log-signal-budget-valid
                                      lw-signal-bounds lw-signal-bounds-valid lw-signal-bounds-width))))

(defthm lw-log-signal-bounds-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (lw-intervalp (lw-log-signal-bounds value error)))
  :hints (("Goal" :use (lw-log-signal-base-valid lw-log-signal-margin-valid)
                  :in-theory (disable lw-log-signal-base lw-log-signal-margin
                                      lw-log-signal-base-valid lw-log-signal-margin-valid))))

(defthm lw-log-signal-bounds-width
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (lw-interval-width (lw-log-signal-bounds value error)) error))
  :hints (("Goal" :use (lw-log-signal-base-valid lw-log-signal-margin-valid
                        lw-log-signal-delta-valid lw-log-signal-budget-valid)
                  :in-theory (disable lw-log-signal-base lw-log-signal-margin lw-log-signal-budget
                                      lw-log-signal-base-valid lw-log-signal-margin-valid
                                      lw-log-signal-delta-valid lw-log-signal-budget-valid))))

(defthm lw-log-signal-point-cauchy
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (lw-log-signal-point value left-error) (lw-log-signal-point value right-error)))
               (+ (lw-log-signal-delta value left-error) (lw-log-signal-delta value right-error))))
  :hints (("Goal"
           :use ((:instance lw-log-signal-delta-valid (error left-error))
                 (:instance lw-log-signal-delta-valid (error right-error))
                 (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value left-error)))
                 (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value right-error)))
                 (:instance lw-exp-bounds-width (epsilon (lw-log-signal-delta value left-error)))
                 (:instance lw-exp-bounds-width (epsilon (lw-log-signal-delta value right-error)))
                 (:instance lw-exp-bounds-overlap
                   (left-error (lw-log-signal-delta value left-error)) (right-error (lw-log-signal-delta value right-error)))
                 (:instance lw-exp-bounds-overlap
                   (left-error (lw-log-signal-delta value right-error)) (right-error (lw-log-signal-delta value left-error))))
           :in-theory (disable lw-log-signal-delta lw-log-signal-delta-valid lw-exp-bounds
                               lw-exp-bounds-valid lw-exp-bounds-width lw-exp-bounds-overlap))))

(defthm lw-log-signal-base-transport
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-log-signal-base value left-error)) (cdr (lw-log-signal-base value right-error)))
               (* (lw-log-signal-lipschitz value)
                  (+ (lw-log-signal-delta value left-error) (lw-log-signal-delta value right-error)))))
  :hints (("Goal"
           :use (lw-log-signal-point-cauchy lw-log-signal-lipschitz-valid
                 (:instance lw-log-signal-point-valid (error left-error))
                 (:instance lw-log-signal-point-valid (error right-error))
                 (:instance lw-log-signal-budget-valid (error left-error))
                 (:instance lw-log-signal-budget-valid (error right-error))
                 (:instance lw-signal-bounds-transport
                   (left (lw-log-signal-point value left-error)) (right (lw-log-signal-point value right-error))
                   (left-error (/ (lw-log-signal-budget left-error) 2))
                   (right-error (/ (lw-log-signal-budget right-error) 2))
                   (cap (lw-log-signal-cap value)) (ceiling 0) (numerator 0) (denominator 1)))
           :in-theory (disable lw-log-signal-point lw-log-signal-budget lw-log-signal-cap lw-signal-lipschitz-factor
                               lw-log-signal-point-cauchy lw-log-signal-lipschitz-valid
                               lw-log-signal-point-valid lw-log-signal-budget-valid lw-signal-bounds lw-signal-bounds-transport)
           :nonlinearp t)))

(defthm lw-log-signal-bounds-overlap
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (car (lw-log-signal-bounds value left-error)) (cdr (lw-log-signal-bounds value right-error))))
  :hints (("Goal"
           :use (lw-log-signal-base-transport lw-log-signal-lipschitz-valid
                 (:instance lw-log-signal-base-valid (error left-error))
                 (:instance lw-log-signal-base-valid (error right-error))
                 (:instance lw-log-signal-delta-valid (error left-error))
                 (:instance lw-log-signal-delta-valid (error right-error)))
           :in-theory (disable lw-log-signal-base lw-log-signal-delta lw-log-signal-lipschitz
                               lw-log-signal-base-transport lw-log-signal-base-valid
                               lw-log-signal-delta-valid lw-log-signal-lipschitz-valid))))

(defthm lw-log-signal-lower-cauchy
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-log-signal-bounds value left-error)) (car (lw-log-signal-bounds value right-error))))
               (+ left-error right-error)))
  :hints (("Goal"
           :use (lw-log-signal-bounds-overlap
                 (:instance lw-log-signal-bounds-overlap (left-error right-error) (right-error left-error))
                 (:instance lw-log-signal-bounds-width (error left-error))
                 (:instance lw-log-signal-bounds-width (error right-error))
                 (:instance lw-log-signal-bounds-valid (error left-error))
                 (:instance lw-log-signal-bounds-valid (error right-error)))
           :in-theory (disable lw-log-signal-bounds lw-log-signal-bounds-overlap
                               lw-log-signal-bounds-width lw-log-signal-bounds-valid))))

(assert-event
 (and (equal (lw-log-signal-cap 0) 2)
      (equal (lw-log-signal-point 0 1) 41/40)
      (<= (lw-log-signal-margin 0 1) 1/4)
      (< 1 (lw-log-signal-point 1/2 1))))
