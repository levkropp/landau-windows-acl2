(in-package "ACL2")

(include-book "log-signal")
(include-book "exp-continuity")

(local (in-theory
        (disable lw-exp-bounds lw-exp-bounds-valid lw-exp-bounds-width
                 lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap lw-exp-bounds-transport
                 lw-exp-lipschitz-cap lw-exp-lipschitz-cap-valid
                 lw-log-signal-bounds lw-log-signal-bounds-valid lw-log-signal-bounds-width
                 lw-log-signal-bounds-overlap lw-log-signal-point lw-log-signal-point-valid
                 lw-log-signal-delta lw-log-signal-delta-valid lw-log-signal-budget
                 lw-log-signal-budget-valid lw-log-signal-lipschitz lw-log-signal-lipschitz-valid
                 lw-log-signal-margin lw-log-signal-margin-valid lw-log-signal-cap
                 lw-log-signal-base lw-signal-bounds lw-signal-bounds-transport
                 lw-signal-lipschitz-factor lw-signal-lipschitz-factor-valid)))

(local (defthm lw-lsc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-lsc-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-lsc-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-lsc-times-zero (equal (* 0 a) 0)))
(local (defthm lw-lsc-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-lsc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-lsc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c))
                  (<= (* a c) (* b c)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-lsc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-lsc-left-commutes)))))

(defun lw-log-signal-spatial-cap (cap) (+ 2 (lw-exp-lipschitz-cap cap)))
(defun lw-log-signal-spatial-slope (cap)
  (lw-signal-lipschitz-factor (lw-log-signal-spatial-cap cap) 0))

(defthm lw-log-signal-spatial-cap-valid
  (implies (and (rationalp cap) (<= 0 cap))
           (and (rationalp (lw-log-signal-spatial-cap cap)) (<= 3 (lw-log-signal-spatial-cap cap))))
  :hints (("Goal" :use (lw-exp-lipschitz-cap-valid))))

(defthm lw-log-signal-spatial-slope-valid
  (implies (and (rationalp cap) (<= 0 cap))
           (and (rationalp (lw-log-signal-spatial-slope cap)) (<= 0 (lw-log-signal-spatial-slope cap))))
  :hints (("Goal" :use (lw-log-signal-spatial-cap-valid
                        (:instance lw-signal-lipschitz-factor-valid
                          (cap (lw-log-signal-spatial-cap cap)) (ceiling 0)))
                  :in-theory (disable lw-log-signal-spatial-cap lw-log-signal-spatial-cap-valid))))

(defthm lw-log-signal-point-spatial-cap
  (implies (and (rationalp value) (rationalp cap) (<= 0 value) (<= value cap)
                (rationalp error) (< 0 error))
           (<= (lw-log-signal-point value error) (lw-log-signal-spatial-cap cap)))
  :hints (("Goal" :use (lw-log-signal-point-valid
                        (:instance lw-exp-bounds-monotone-overlap
                          (left value) (right cap) (left-error 1) (right-error 1))
                        (:instance lw-exp-bounds-width (epsilon 1)))
                  :in-theory (enable lw-log-signal-cap lw-exp-lipschitz-cap))))

(defthm lw-log-signal-delta-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (lw-log-signal-delta value error) error))
  :hints (("Goal" :use (lw-log-signal-budget-valid lw-log-signal-lipschitz-valid
                        (:instance lw-positive-division-bound
                          (numerator (lw-log-signal-budget error))
                          (divisor (* 4 (+ 1 (lw-log-signal-lipschitz value)))) (bound error)))
                  :in-theory (enable lw-log-signal-delta) :nonlinearp t)))

(defthm lw-log-signal-point-spatial-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (lw-log-signal-point left left-error) (lw-log-signal-point right right-error)))
               (+ (* (lw-exp-lipschitz-cap cap) (abs (- left right)))
                  (lw-log-signal-delta left left-error) (lw-log-signal-delta right right-error))))
  :hints (("Goal"
           :use ((:instance lw-log-signal-delta-valid (value left) (error left-error))
                 (:instance lw-log-signal-delta-valid (value right) (error right-error))
                 (:instance lw-exp-bounds-transport
                   (left-error (lw-log-signal-delta left left-error))
                   (right-error (lw-log-signal-delta right right-error)))
                 (:instance lw-exp-bounds-transport (left right) (right left)
                   (left-error (lw-log-signal-delta right right-error))
                   (right-error (lw-log-signal-delta left left-error)))
                 (:instance lw-exp-bounds-width (value left) (epsilon (lw-log-signal-delta left left-error)))
                 (:instance lw-exp-bounds-width (value right) (epsilon (lw-log-signal-delta right right-error)))
                 (:instance lw-exp-bounds-valid (value left) (epsilon (lw-log-signal-delta left left-error)))
                 (:instance lw-exp-bounds-valid (value right) (epsilon (lw-log-signal-delta right right-error)))
                 lw-exp-lipschitz-cap-valid)
           :in-theory (enable lw-log-signal-point))))

(defthm lw-log-signal-base-spatial-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-log-signal-base left left-error)) (cdr (lw-log-signal-base right right-error)))
               (* (lw-log-signal-spatial-slope cap)
                  (+ (* (lw-exp-lipschitz-cap cap) (abs (- left right)))
                     (lw-log-signal-delta left left-error) (lw-log-signal-delta right right-error)))))
  :hints (("Goal"
           :use (lw-log-signal-point-spatial-bound lw-log-signal-spatial-slope-valid
                 lw-log-signal-spatial-cap-valid lw-exp-lipschitz-cap-valid
                 (:instance lw-log-signal-delta-valid (value left) (error left-error))
                 (:instance lw-log-signal-delta-valid (value right) (error right-error))
                 (:instance lw-log-signal-point-valid (value left) (error left-error))
                 (:instance lw-log-signal-point-valid (value right) (error right-error))
                 (:instance lw-log-signal-point-spatial-cap (value left) (error left-error))
                 (:instance lw-log-signal-point-spatial-cap (value right) (error right-error))
                 (:instance lw-log-signal-budget-valid (error left-error))
                 (:instance lw-log-signal-budget-valid (error right-error))
                 (:instance lw-signal-bounds-transport
                   (left (lw-log-signal-point left left-error)) (right (lw-log-signal-point right right-error))
                   (left-error (/ (lw-log-signal-budget left-error) 2))
                   (right-error (/ (lw-log-signal-budget right-error) 2))
                   (cap (lw-log-signal-spatial-cap cap)) (ceiling 0) (numerator 0) (denominator 1)))
           :in-theory (enable lw-log-signal-base)
           :nonlinearp t)))

(defthm lw-log-signal-bounds-spatial-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-log-signal-bounds left left-error)) (cdr (lw-log-signal-bounds right right-error)))
               (* (lw-log-signal-spatial-slope cap)
                  (+ (* (lw-exp-lipschitz-cap cap) (abs (- left right)))
                     (lw-log-signal-delta left left-error) (lw-log-signal-delta right right-error)))))
  :hints (("Goal" :use (lw-log-signal-base-spatial-transport
                        (:instance lw-log-signal-base-valid (value left) (error left-error))
                        (:instance lw-log-signal-base-valid (value right) (error right-error))
                        (:instance lw-log-signal-margin-valid (value left) (error left-error))
                        (:instance lw-log-signal-margin-valid (value right) (error right-error)))
                  :in-theory (e/d (lw-log-signal-bounds) (lw-log-signal-base-valid
                                                        lw-log-signal-base-spatial-transport)))))

(defthm lw-log-signal-spatial-cauchy
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-log-signal-bounds left left-error))
                        (car (lw-log-signal-bounds right right-error))))
               (+ (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) (abs (- left right)))
                  (* (+ 1 (lw-log-signal-spatial-slope cap)) (+ left-error right-error)))))
  :hints (("Goal" :use (lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid
                        lw-log-signal-bounds-spatial-transport
                        (:instance lw-log-signal-bounds-spatial-transport
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-log-signal-bounds-valid (value left) (error left-error))
                        (:instance lw-log-signal-bounds-valid (value right) (error right-error))
                        (:instance lw-log-signal-bounds-width (value left) (error left-error))
                        (:instance lw-log-signal-bounds-width (value right) (error right-error))
                        (:instance lw-log-signal-delta-budget (value left) (error left-error))
                        (:instance lw-log-signal-delta-budget (value right) (error right-error))
                        (:instance lw-log-signal-delta-valid (value left) (error left-error))
                        (:instance lw-log-signal-delta-valid (value right) (error right-error)))
                  :in-theory (disable lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid
                                      lw-log-signal-bounds-spatial-transport lw-log-signal-delta-budget)
                  :nonlinearp t)))

(defthm lw-log-signal-refined-spatial-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
                (rationalp precision) (< 0 precision))
           (<= (- (car (lw-log-signal-bounds left left-error)) (cdr (lw-log-signal-bounds right right-error)))
               (+ (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) (abs (- left right)))
                  (* 2 (+ 1 (lw-log-signal-spatial-slope cap)) precision))))
  :hints (("Goal"
           :use (lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid
                 (:instance lw-log-signal-bounds-overlap (value left) (right-error precision))
                 (:instance lw-log-signal-bounds-overlap (value right) (left-error precision))
                 (:instance lw-log-signal-bounds-width (value left) (error precision))
                 (:instance lw-log-signal-bounds-width (value right) (error precision))
                 (:instance lw-log-signal-bounds-valid (value left) (error precision))
                 (:instance lw-log-signal-bounds-valid (value right) (error precision))
                 (:instance lw-log-signal-bounds-valid (value left) (error left-error))
                 (:instance lw-log-signal-bounds-valid (value right) (error right-error))
                 (:instance lw-log-signal-bounds-spatial-transport (left-error precision) (right-error precision))
                 (:instance lw-log-signal-delta-budget (value left) (error precision))
                 (:instance lw-log-signal-delta-budget (value right) (error precision))
                 (:instance lw-log-signal-delta-valid (value left) (error precision))
                 (:instance lw-log-signal-delta-valid (value right) (error precision)))
           :in-theory (disable lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid
                               lw-log-signal-bounds-spatial-transport lw-log-signal-delta-budget)
           :nonlinearp t)))

(local
 (defthm lw-lsc-slack-budget
   (implies (and (rationalp slope) (<= 0 slope) (rationalp gap) (< 0 gap))
            (and (rationalp (/ gap (* 4 (+ 1 slope))))
                 (< 0 (/ gap (* 4 (+ 1 slope))))
                 (<= (* 2 (+ 1 slope) (/ gap (* 4 (+ 1 slope)))) (/ gap 2))))
   :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* 2 (+ 1 slope) gap)) (divisor (* 4 (+ 1 slope))) (bound (/ gap 2))))
                   :nonlinearp t))
   :rule-classes nil))

; A positive excess would survive comparison with sufficiently fine
; rational enclosures, contradicting the preceding explicit error bound.
; The chosen refinement precision is a rational function of that excess.
(defthm lw-log-signal-bounds-lipschitz
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-log-signal-bounds left left-error)) (cdr (lw-log-signal-bounds right right-error)))
               (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) (abs (- left right)))))
  :hints (("Goal"
           :use (lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid
                 (:instance lw-log-signal-bounds-valid (value left) (error left-error))
                 (:instance lw-log-signal-bounds-valid (value right) (error right-error))
                 (:instance lw-lsc-slack-budget
                   (slope (lw-log-signal-spatial-slope cap))
                   (gap (- (- (car (lw-log-signal-bounds left left-error))
                              (cdr (lw-log-signal-bounds right right-error)))
                           (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) (abs (- left right))))))
                 (:instance lw-log-signal-refined-spatial-transport
                   (precision
                    (/ (- (- (car (lw-log-signal-bounds left left-error))
                             (cdr (lw-log-signal-bounds right right-error)))
                          (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) (abs (- left right))))
                       (* 4 (+ 1 (lw-log-signal-spatial-slope cap)))))))
           :in-theory (disable lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid
                               lw-log-signal-refined-spatial-transport))))

(defthm lw-log-signal-lower-spatial-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-log-signal-bounds left left-error))
                        (car (lw-log-signal-bounds right right-error))))
               (+ (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) (abs (- left right)))
                  left-error right-error)))
  :hints (("Goal" :use (lw-log-signal-bounds-lipschitz
                        (:instance lw-log-signal-bounds-lipschitz
                          (left right) (right left) (left-error right-error) (right-error left-error))
                        (:instance lw-log-signal-bounds-width (value left) (error left-error))
                        (:instance lw-log-signal-bounds-width (value right) (error right-error))
                        (:instance lw-log-signal-bounds-valid (value left) (error left-error))
                        (:instance lw-log-signal-bounds-valid (value right) (error right-error))
                        lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid)
                  :in-theory (disable lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid
                                      lw-log-signal-bounds-lipschitz))))

(defun lw-log-signal-modulus (cap error)
  (/ error (* 4 (+ 1 (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap))))))

(defthm lw-log-signal-modulus-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
           (and (rationalp (lw-log-signal-modulus cap error))
                (< 0 (lw-log-signal-modulus cap error))
                (<= (lw-log-signal-modulus cap error) (/ error 4))
                (<= (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap)
                       (lw-log-signal-modulus cap error)) (/ error 4))))
  :hints (("Goal" :use (lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid
                        (:instance lw-positive-division-bound
                          (numerator error)
                          (divisor (* 4 (+ 1 (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap)))))
                          (bound (/ error 4)))
                        (:instance lw-positive-division-bound
                          (numerator (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap) error))
                          (divisor (* 4 (+ 1 (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap)))))
                          (bound (/ error 4))))
                  :in-theory (disable lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid)
                  :nonlinearp t)))

(defthm lw-log-signal-computed-spatial-modulus
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp error) (< 0 error)
                (rationalp left-error) (< 0 left-error) (<= left-error (/ error 4))
                (rationalp right-error) (< 0 right-error) (<= right-error (/ error 4))
                (<= (abs (- left right)) (lw-log-signal-modulus cap error)))
           (<= (abs (- (car (lw-log-signal-bounds left left-error))
                        (car (lw-log-signal-bounds right right-error)))) error))
  :hints (("Goal" :use (lw-log-signal-lower-spatial-bound lw-log-signal-modulus-valid
                        lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid
                        (:instance lw-lsc-multiply-order
                          (a (abs (- left right))) (b (lw-log-signal-modulus cap error))
                          (c (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap)))))
                  :in-theory (disable lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid
                                      lw-log-signal-modulus lw-log-signal-modulus-valid lw-log-signal-lower-spatial-bound)
                  :nonlinearp t)))

(assert-event
 (and (<= (lw-log-signal-modulus 0 1) 1/4)
      (< 0 (lw-log-signal-modulus 1/2 1/10))))
