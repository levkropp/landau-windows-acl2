(in-package "ACL2")

(include-book "log-exp-inverse")

; A computed logarithm is a usable ramp breakpoint. Bound exp(log(n))
; arithmetically, then control the positive-part ramp even on the small
; interval where rounding changes which side of the breakpoint is used.

(local (in-theory
        (disable lw-log-bounds lw-log-count lw-log-rectangles
                 lw-log-bounds-interval lw-log-bounds-width lw-log-bounds-nonnegative
                 lw-log-bounds-lower-coarse lw-log-lower-bounds-taylor lw-log-upper-bounds-exp
                 lw-log-bounds-monotone-overlap lw-log-bounds-overlap lw-log-upper-coarse
                 lw-exp-bounds lw-exp-index lw-exp-band lw-exp-term lw-exp-sum
                 lw-exp-lipschitz-cap lw-exp-bounds-transport lw-exp-bounds-width
                 lw-exp-bounds-valid lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap
                 lw-log-signal-point lw-log-signal-delta lw-ramp)))

(local (defthm lw-elr-log-data
         (implies (and (rationalp point) (< 1 point) (rationalp log-error) (< 0 log-error)
                       (<= log-error 1))
                  (and (rationalp (car (lw-log-bounds point log-error)))
                       (rationalp (cdr (lw-log-bounds point log-error)))
                       (<= 0 (car (lw-log-bounds point log-error)))
                       (<= (car (lw-log-bounds point log-error)) (cdr (lw-log-bounds point log-error)))
                       (<= (cdr (lw-log-bounds point log-error)) point)
                       (<= (- (cdr (lw-log-bounds point log-error))
                              (car (lw-log-bounds point log-error))) log-error)))
         :hints (("Goal"
                  :use ((:instance lw-log-bounds-interval (value point) (epsilon log-error))
                        (:instance lw-log-bounds-width (value point) (epsilon log-error))
                        (:instance lw-log-bounds-lower-coarse (value point) (epsilon log-error)))
                  :in-theory (enable lw-intervalp) :do-not-induct t))))

(defthm lw-exp-log-lower-bracket
  (implies (and (rationalp point) (< 1 point) (rationalp log-error) (< 0 log-error)
                (rationalp exp-error) (< 0 exp-error))
           (<= (car (lw-exp-bounds (car (lw-log-bounds point log-error)) exp-error)) point))
  :hints (("Goal"
           :use ((:instance lw-log-bounds-interval (value point) (epsilon log-error))
                 (:instance lw-log-bounds-nonnegative)
                 (:instance lw-exp-index-adequate
                   (value (car (lw-log-bounds point log-error))) (epsilon exp-error))
                 (:instance lw-log-lower-bounds-taylor
                   (index (lw-exp-index (car (lw-log-bounds point log-error)) exp-error))))
           :in-theory (e/d (lw-exp-bounds lw-exp-band lw-intervalp)
                           (lw-exp-index-adequate))
           :do-not-induct t)))

(local (defthm lw-elr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-exp-log-inverse-error
  (implies (and (rationalp point) (< 1 point)
                (rationalp log-error) (< 0 log-error) (<= log-error 1)
                (rationalp exp-error) (< 0 exp-error))
           (<= (abs (- (car (lw-exp-bounds (car (lw-log-bounds point log-error)) exp-error)) point))
               (+ (* (lw-exp-lipschitz-cap point) log-error) (* 2 exp-error))))
  :hints (("Goal"
           :use (lw-elr-log-data lw-exp-log-lower-bracket
                 (:instance lw-exp-lipschitz-cap-valid (cap point))
                 (:instance lw-log-upper-bounds-exp
                   (value (cdr (lw-log-bounds point log-error))))
                 (:instance lw-exp-bounds-valid
                   (value (car (lw-log-bounds point log-error))) (epsilon exp-error))
                 (:instance lw-exp-bounds-valid
                   (value (cdr (lw-log-bounds point log-error))) (epsilon exp-error))
                 (:instance lw-exp-bounds-width
                   (value (car (lw-log-bounds point log-error))) (epsilon exp-error))
                 (:instance lw-exp-bounds-width
                   (value (cdr (lw-log-bounds point log-error))) (epsilon exp-error))
                 (:instance lw-exp-bounds-transport
                   (left (cdr (lw-log-bounds point log-error)))
                   (right (car (lw-log-bounds point log-error)))
                   (left-error exp-error) (right-error exp-error) (cap point))
                 (:instance lw-elr-multiply-order
                   (a (- (cdr (lw-log-bounds point log-error)) (car (lw-log-bounds point log-error))))
                   (b log-error) (factor (lw-exp-lipschitz-cap point))))
           :in-theory (e/d (lw-intervalp)
                           (lw-elr-log-data lw-exp-log-lower-bracket lw-exp-lipschitz-cap-valid))
           :nonlinearp nil :do-not-induct t)))

(defun lw-log-ramp-extension (value point index log-error)
  (if (< value (car (lw-log-bounds index log-error))) 0 (- (/ point index) 1)))

(defthm lw-log-ramp-extension-rational
  (implies (and (rationalp value) (rationalp point) (rationalp index) (< 1 index)
                (rationalp log-error) (< 0 log-error))
           (rationalp (lw-log-ramp-extension value point index log-error))))

(local (defthm lw-elr-threshold-error
         (implies
          (and (rationalp point) (rationalp threshold) (< 0 threshold)
               (rationalp radius) (<= 0 radius)
               (if below (<= point (+ threshold radius)) (<= (- threshold radius) point)))
          (<= (abs (- (lw-ramp point threshold) (if below 0 (- (/ point threshold) 1))))
              (* radius (/ threshold))))
         :hints (("Goal" :use ((:instance inverse-of-* (x threshold))
                              (:instance lw-elr-multiply-order
                                (a point) (b (+ threshold radius)) (factor (/ threshold)))
                              (:instance lw-elr-multiply-order
                                (a (- threshold radius)) (b point) (factor (/ threshold))))
                         :in-theory (e/d (lw-ramp) (inverse-of-*)) :nonlinearp t))
         :rule-classes nil))

(defthm lw-log-ramp-cutpoint-error
  (implies
   (and (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error) (<= log-error 1)
        (rationalp value) (<= 0 value) (rationalp point)
        (rationalp exp-error) (< 0 exp-error) (rationalp slack) (<= 0 slack)
        (<= (car (lw-exp-bounds value exp-error)) point)
        (<= point (+ (cdr (lw-exp-bounds value exp-error)) slack)))
   (<= (abs (- (lw-ramp point index) (lw-log-ramp-extension value point index log-error)))
       (* (+ (* (lw-exp-lipschitz-cap index) log-error) (* 3 exp-error) slack) (/ index))))
  :hints (("Goal"
           :cases ((< value (car (lw-log-bounds index log-error))))
           :use ((:instance lw-elr-log-data (point index))
                 (:instance lw-exp-log-inverse-error (point index))
                 (:instance lw-exp-log-lower-bracket (point index))
                 (:instance lw-exp-lipschitz-cap-valid (cap index))
                 (:instance lw-exp-bounds-valid (epsilon exp-error))
                 (:instance lw-exp-bounds-width (epsilon exp-error))
                 (:instance lw-exp-bounds-valid
                   (value (car (lw-log-bounds index log-error))) (epsilon exp-error))
                 (:instance lw-exp-bounds-width
                   (value (car (lw-log-bounds index log-error))) (epsilon exp-error))
                 (:instance lw-exp-bounds-monotone-overlap
                   (left value) (right (car (lw-log-bounds index log-error)))
                   (left-error exp-error) (right-error exp-error))
                 (:instance lw-exp-bounds-monotone-overlap
                   (left (car (lw-log-bounds index log-error))) (right value)
                   (left-error exp-error) (right-error exp-error))
                 (:instance lw-elr-multiply-order (a 0) (b log-error)
                   (factor (lw-exp-lipschitz-cap index)))
                 (:instance lw-elr-threshold-error (threshold index)
                   (below (< value (car (lw-log-bounds index log-error))))
                   (radius (+ (* (lw-exp-lipschitz-cap index) log-error) (* 3 exp-error) slack))))
           :in-theory
           (e/d (lw-log-ramp-extension lw-intervalp)
                (lw-elr-log-data lw-exp-log-inverse-error lw-exp-log-lower-bracket
                 lw-exp-lipschitz-cap-valid))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-elr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-elr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(defthm lw-log-signal-ramp-cutpoint-error
  (implies
   (and (rationalp index) (< 1 index)
        (rationalp log-error) (< 0 log-error) (<= log-error 1)
        (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error))
   (<= (abs (- (lw-ramp (lw-log-signal-point value signal-error) index)
               (lw-log-ramp-extension value (lw-log-signal-point value signal-error) index log-error)))
       (* (+ (* (lw-exp-lipschitz-cap index) log-error)
             (* 4 (lw-log-signal-delta value signal-error))) (/ index))))
  :hints (("Goal"
           :use ((:instance lw-log-signal-point-valid (error signal-error))
                 (:instance lw-log-signal-delta-valid (error signal-error))
                 (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value signal-error)))
                 (:instance lw-log-ramp-cutpoint-error
                   (point (lw-log-signal-point value signal-error))
                   (exp-error (lw-log-signal-delta value signal-error))
                   (slack (lw-log-signal-delta value signal-error))))
           :in-theory (e/d (lw-log-signal-point lw-intervalp)
                           (lw-log-signal-point-valid lw-log-signal-delta-valid lw-log-ramp-cutpoint-error
                            lw-log-signal-cap lw-log-signal-margin lw-log-signal-lipschitz
                            lw-log-signal-budget))
           :nonlinearp nil :do-not-induct t)))
