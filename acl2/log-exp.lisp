(in-package "ACL2")

(include-book "rpow-kernel")
(include-book "log-growth")
(include-book "kernel-window")

; Finite inverse comparisons for the actual logarithm/exponential evaluators.
; The rectangle endpoint ratios telescope; Taylor products carry the order.
(local (in-theory
        (disable lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-band lw-exp-index lw-rational-power lw-exp-term-scale-argument
                 lw-exp-bounds-valid lw-exp-bounds-overlap lw-exp-bounds-monotone-overlap
                 lw-exp-sum-at-least-one lw-exp-sum-monotone-argument
                 lw-log-rectangles lw-log-rectangles-interval lw-log-rectangles-nonnegative
                 lw-log-bounds lw-log-count lw-log-count-positive lw-ceiling-rational
                 lw-log-step-adequate lw-log-step-positive lw-log-grid-endpoint
                 lw-log-signal-point lw-log-signal-delta lw-log-signal-point-valid
                 lw-log-signal-delta-valid lw-log-signal-point-exp-cap)))

(local (defthm lw-le-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-le-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-le-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-le-zero-times (equal (* 0 a) 0)))
(local (defthm lw-le-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-le-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-le-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-le-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-le-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defun lw-le-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) nil (lw-le-countdown (- index 1)))))
(local (defthm lw-le-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-le-sum-zero
         (implies (zp index) (equal (lw-exp-sum value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-sum)))))
(local (defthm lw-le-sum-one
         (implies (rationalp value) (equal (lw-exp-sum value 1) (+ 1 value)))
         :hints (("Goal" :in-theory (enable lw-exp-sum lw-exp-term)))))
(local (defthm lw-le-term-zero-value
         (implies (posp index) (equal (lw-exp-term 0 index) 0))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-le-sum-zero-value
         (equal (lw-exp-sum 0 index) 1)
         :hints (("Goal" :induct (lw-exp-sum 0 index) :in-theory (enable lw-exp-sum)))))

(local (defthm lw-le-term-geometric
         (implies (and (rationalp value) (<= 0 value) (posp index))
                  (<= (lw-exp-term value index) (* value (lw-exp-term value (- index 1)))))
         :hints (("Goal" :use ((:instance lw-exp-term-nonnegative (index (- index 1)))
                              (:instance lw-positive-division-bound
                                (numerator (* value (lw-exp-term value (- index 1)))) (divisor index)
                                (bound (* value (lw-exp-term value (- index 1))))))
                         :expand ((lw-exp-term value index)) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-le-geometric-barrier
         (implies (and (rationalp value) (<= 0 value) (< value 1) (natp index))
                  (<= (+ (* (- 1 value) (lw-exp-sum value index)) (* value (lw-exp-term value index))) 1))
         :hints (("Goal" :induct (lw-le-countdown index))
                 (and stable-under-simplificationp
                      '(:use (lw-le-term-geometric)
                        :expand ((lw-exp-sum value index))
                        :do-not-induct t)))))

(defthm lw-exp-sum-unit-geometric
  (implies (and (rationalp value) (<= 0 value) (< value 1) (natp index))
           (<= (lw-exp-sum value index) (/ (- 1 value))))
  :hints (("Goal" :use (lw-le-geometric-barrier lw-exp-term-nonnegative
                        (:instance lw-le-multiply-order
                          (a (+ (* (- 1 value) (lw-exp-sum value index)) (* value (lw-exp-term value index))))
                          (b 1) (factor (/ (- 1 value))))
                        (:instance inverse-of-* (x (- 1 value))))
                  :in-theory (disable inverse-of-*) :nonlinearp t)))

(local (defthm lw-le-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-le-left-commutes)))))
(local (defthm lw-le-rectangles-zero
         (implies (zp count) (equal (lw-log-rectangles start step count) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-log-rectangles)))))

(defthm lw-log-upper-rectangles-taylor
  (implies (and (rationalp start) (< 0 start) (rationalp step) (<= 0 step) (natp count))
           (<= (+ start (* count step))
               (* start (lw-exp-sum (cdr (lw-log-rectangles start step count)) count))))
  :hints (("Goal" :induct (lw-log-rectangles start step count)
                  :in-theory (enable (:induction lw-log-rectangles)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-log-rectangles-interval (start (+ start step)) (count (- count 1)))
                       (:instance lw-log-rectangles-nonnegative (start (+ start step)) (count (- count 1)))
                       (:instance lw-positive-division-lower-bound (numerator step) (divisor start) (bound 0))
                       (:instance lw-exp-sum-product-upper
                         (left (/ step start)) (right (cdr (lw-log-rectangles (+ start step) step (- count 1))))
                         (left-index 1) (right-index (- count 1)))
                       (:instance lw-le-multiply-order
                         (a (* (lw-exp-sum (/ step start) 1) (lw-exp-sum (cdr (lw-log-rectangles (+ start step) step (- count 1))) (- count 1))))
                         (b (lw-exp-sum (+ (/ step start) (cdr (lw-log-rectangles (+ start step) step (- count 1)))) count))
                         (factor start)))
                 :expand ((lw-log-rectangles start step count))
                 :do-not-induct t :nonlinearp t))))

(local (defthm lw-le-cell-ratio
         (implies (and (rationalp start) (< 0 start) (rationalp step) (<= 0 step))
                  (and (rationalp (/ step (+ start step))) (<= 0 (/ step (+ start step))) (< (/ step (+ start step)) 1)))
         :hints (("Goal" :use ((:instance inverse-of-* (x (+ start step))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))))

(local (defthm lw-le-equal-times
         (implies (equal a b) (equal (* a factor) (* b factor))) :rule-classes nil))
(local (defthm lw-le-cell-scale
         (implies (and (rationalp start) (< 0 start) (rationalp step) (<= 0 step))
                  (equal (* (+ start step) (- 1 (/ step (+ start step)))) start))
         :hints (("Goal" :use ((:instance lw-le-inverse-factor (divisor (+ start step)) (coefficient step)))
                         :in-theory (disable lw-le-inverse-factor) :nonlinearp t))
         :rule-classes nil))

(local (in-theory (disable lw-le-cell-ratio)))
(local (defthm lw-le-cell-exp-bound
         (implies (and (rationalp start) (< 0 start) (rationalp step) (<= 0 step) (natp index))
                  (<= (* start (lw-exp-sum (/ step (+ start step)) index)) (+ start step)))
         :hints (("Goal" :use (lw-le-cell-ratio
                              lw-le-cell-scale
                              (:instance lw-le-equal-times
                                (a (* (+ start step) (- 1 (/ step (+ start step))))) (b start)
                                (factor (lw-exp-sum (/ step (+ start step)) index)))
                              (:instance lw-le-geometric-barrier (value (/ step (+ start step))))
                              (:instance lw-exp-term-nonnegative (value (/ step (+ start step))))
                              (:instance lw-le-multiply-order
                                (a (+ (* (- 1 (/ step (+ start step))) (lw-exp-sum (/ step (+ start step)) index))
                                      (* (/ step (+ start step)) (lw-exp-term (/ step (+ start step)) index))))
                                (b 1) (factor (+ start step))))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-log-lower-rectangles-taylor
  (implies (and (rationalp start) (< 0 start) (rationalp step) (<= 0 step) (natp count) (natp index))
           (<= (* start (lw-exp-sum (car (lw-log-rectangles start step count)) index))
               (+ start (* count step))))
  :hints (("Goal" :induct (lw-log-rectangles start step count)
                  :in-theory (enable (:induction lw-log-rectangles)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-log-rectangles-interval (start (+ start step)) (count (- count 1)))
                       (:instance lw-log-rectangles-nonnegative (start (+ start step)) (count (- count 1)))
                       lw-le-cell-ratio lw-le-cell-exp-bound
                       (:instance lw-exp-sum-addition-upper
                         (left (/ step (+ start step))) (right (car (lw-log-rectangles (+ start step) step (- count 1)))))
                       (:instance lw-exp-sum-at-least-one (value (car (lw-log-rectangles (+ start step) step (- count 1)))))
                       (:instance lw-le-multiply-order
                         (a (lw-exp-sum (+ (/ step (+ start step)) (car (lw-log-rectangles (+ start step) step (- count 1)))) index))
                         (b (* (lw-exp-sum (/ step (+ start step)) index) (lw-exp-sum (car (lw-log-rectangles (+ start step) step (- count 1))) index)))
                         (factor start))
                       (:instance lw-le-multiply-order
                         (a (* start (lw-exp-sum (/ step (+ start step)) index))) (b (+ start step))
                         (factor (lw-exp-sum (car (lw-log-rectangles (+ start step) step (- count 1))) index))))
                 :expand ((lw-log-rectangles start step count))
                 :do-not-induct t :nonlinearp t))))

(local (in-theory (disable lw-log-upper-rectangles-taylor lw-log-lower-rectangles-taylor lw-log-bounds-interval)))

(defthm lw-log-bounds-nonnegative
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error))
           (<= 0 (car (lw-log-bounds point log-error))))
  :hints (("Goal" :use ((:instance lw-log-step-adequate (value point) (epsilon log-error))
                        (:instance lw-log-rectangles-nonnegative (start 1)
                          (step (/ (- point 1) (lw-log-count point log-error))) (count (lw-log-count point log-error))))
                  :in-theory (enable lw-log-bounds))))

(local (in-theory (disable lw-log-bounds-nonnegative)))

(defthm lw-log-lower-bounds-taylor
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error) (natp index))
           (<= (lw-exp-sum (car (lw-log-bounds point log-error)) index) point))
  :hints (("Goal" :use ((:instance lw-log-step-adequate (value point) (epsilon log-error))
                        (:instance lw-log-grid-endpoint (value point) (epsilon log-error))
                        (:instance lw-log-count-positive (value point) (epsilon log-error))
                        (:instance lw-log-lower-rectangles-taylor (start 1)
                          (step (/ (- point 1) (lw-log-count point log-error))) (count (lw-log-count point log-error))))
                  :in-theory (enable lw-log-bounds))))

(defthm lw-log-upper-bounds-exp
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error)
                (rationalp value) (<= (cdr (lw-log-bounds point log-error)) value))
           (<= point (cdr (lw-exp-bounds value exp-error))))
  :hints (("Goal"
           :use ((:instance lw-log-step-adequate (value point) (epsilon log-error))
                 (:instance lw-log-grid-endpoint (value point) (epsilon log-error))
                 (:instance lw-log-count-positive (value point) (epsilon log-error))
                 (:instance lw-log-bounds-interval (value point) (epsilon log-error))
                 lw-log-bounds-nonnegative
                 (:instance lw-log-upper-rectangles-taylor (start 1)
                   (step (/ (- point 1) (lw-log-count point log-error))) (count (lw-log-count point log-error)))
                 (:instance lw-exp-sum-monotone-argument (left (cdr (lw-log-bounds point log-error))) (right value) (index (lw-log-count point log-error)))
                 (:instance lw-exp-partial-sum-upper (index (lw-log-count point log-error)) (error exp-error)))
           :in-theory (enable lw-log-bounds))))

(defthm lw-log-signal-point-above-upper-exp
  (implies (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error))
           (<= (cdr (lw-exp-bounds value (lw-log-signal-delta value signal-error))) (lw-log-signal-point value signal-error)))
  :hints (("Goal" :use ((:instance lw-log-signal-delta-valid (error signal-error))
                        (:instance lw-exp-bounds-width (epsilon (lw-log-signal-delta value signal-error))))
                  :in-theory (enable lw-log-signal-point))))

(local (in-theory (disable lw-log-upper-bounds-exp lw-log-signal-point-above-upper-exp lw-log-lower-bounds-taylor)))

(defthm lw-log-signal-left-window-test
  (implies (and (rationalp start) (<= 1 start) (rationalp value) (<= 0 value)
                (rationalp signal-error) (< 0 signal-error) (< (lw-log-signal-point value signal-error) start))
           (< value (cdr (lw-log-bounds start 1/1000))))
  :hints (("Goal" :use (lw-log-signal-point-above-upper-exp
                        (:instance lw-log-upper-bounds-exp (point start) (log-error 1/1000)
                          (exp-error (lw-log-signal-delta value signal-error)))))))

(local (defthm lw-le-power-two
         (implies (rationalp base) (equal (lw-rational-power base 2) (* base base)))
         :hints (("Goal" :expand ((lw-rational-power base 2) (lw-rational-power base 1) (lw-rational-power base 0))))))
(local (defthm lw-le-power-three
         (implies (rationalp base) (equal (lw-rational-power base 3) (* base base base)))
         :hints (("Goal" :expand ((lw-rational-power base 3) (lw-rational-power base 2) (lw-rational-power base 1) (lw-rational-power base 0))))))

(defthm lw-log-lower-threehalves-taylor
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error)
                (rationalp value) (<= 0 value) (<= value (- (* 3/2 (car (lw-log-bounds point log-error))) 1))
                (natp index))
           (<= (* 4 (lw-exp-sum value index) (lw-exp-sum value index)) (* point point point)))
  :hints (("Goal"
           :use (lw-log-bounds-nonnegative
                 (:instance lw-log-bounds-interval (value point) (epsilon log-error))
                 (:instance lw-exp-sum-mixed-integer-powers (left value) (right 1) (left-copies 2) (right-copies 2)
                   (left-index index) (right-index 1))
                 (:instance lw-exp-sum-monotone-argument (left (+ (* 2 value) 2)) (right (* 3 (car (lw-log-bounds point log-error)))) (index (+ (* 2 index) 2)))
                 (:instance lw-exp-sum-integer-upper (value (car (lw-log-bounds point log-error))) (copies 3) (index (+ (* 2 index) 2)))
                 (:instance lw-log-lower-bounds-taylor (index (+ (* 2 index) 2)))
                 (:instance lw-exp-sum-at-least-one (value (car (lw-log-bounds point log-error))) (index (+ (* 2 index) 2)))
                 (:instance lw-rational-power-monotone-base
                   (left (lw-exp-sum (car (lw-log-bounds point log-error)) (+ (* 2 index) 2))) (right point) (exponent 3))))))

(local (in-theory (disable lw-log-lower-threehalves-taylor)))

(defthm lw-log-lower-threehalves-exp
  (implies (and (rationalp point) (<= 1 point) (rationalp log-error) (< 0 log-error)
                (rationalp value) (<= 0 value) (<= value (- (* 3/2 (car (lw-log-bounds point log-error))) 1)))
           (<= (* 4 (car (lw-exp-bounds value exp-error)) (car (lw-exp-bounds value exp-error))) (* point point point)))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (epsilon exp-error))
                        (:instance lw-log-lower-threehalves-taylor (index (lw-exp-index value exp-error))))
                  :in-theory (enable lw-exp-bounds lw-exp-band))))

(local (in-theory (disable lw-log-lower-threehalves-exp)))

(defthm lw-log-signal-right-window-test
  (implies (and (rationalp start) (<= 1 start) (rationalp value) (<= 0 value)
                (rationalp signal-error) (< 0 signal-error)
                (<= value (- (* 3/2 (car (lw-log-bounds start 1/1000))) 1)))
           (<= (* (lw-log-signal-point value signal-error) (lw-log-signal-point value signal-error)) (* start start start)))
  :hints (("Goal" :use ((:instance lw-log-signal-point-valid (error signal-error))
                        (:instance lw-log-signal-point-exp-cap (error signal-error))
                        (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value signal-error)))
                        (:instance lw-log-lower-threehalves-exp (point start) (log-error 1/1000)
                          (exp-error (lw-log-signal-delta value signal-error))))
                  :nonlinearp t)))

(local (in-theory (disable lw-log-signal-left-window-test lw-log-signal-right-window-test)))

(defthm lw-log-signal-outside-window
  (implies (and (rationalp start) (<= 1 start) (rationalp value) (<= 0 value)
                (rationalp signal-error) (< 0 signal-error)
                (not (and (<= start (lw-log-signal-point value signal-error))
                          (<= (* (lw-log-signal-point value signal-error) (lw-log-signal-point value signal-error)) (* start start start)))))
           (or (< value (cdr (lw-log-bounds start 1/1000)))
               (< (- (* 3/2 (car (lw-log-bounds start 1/1000))) 1) value)))
  :hints (("Goal" :use (lw-log-signal-left-window-test lw-log-signal-right-window-test))))

(local (defthm lw-le-multiply-strict
         (implies (and (rationalp a) (rationalp b) (< a b) (rationalp factor) (< 0 factor))
                  (< (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-ceiling-rational-grid-separation
  (implies (and (rationalp cutoff) (<= 0 cutoff) (rationalp step) (< 0 step) (natp address))
           (equal (< (* address step) cutoff) (< address (lw-ceiling-rational (/ cutoff step)))))
  :hints (("Goal"
           :cases ((< (* address step) cutoff) (< address (lw-ceiling-rational (/ cutoff step))))
           :use ((:instance lw-ceiling-rational-bracket (value (/ cutoff step)))
                 (:instance lw-le-inverse-factor (divisor step) (coefficient cutoff))
                 (:instance lw-le-multiply-order (a (/ cutoff step)) (b (lw-ceiling-rational (/ cutoff step))) (factor step))
                 (:instance lw-le-multiply-order (a (lw-ceiling-rational (/ cutoff step))) (b address) (factor step))
                 (:instance lw-le-multiply-order (a (+ address 1)) (b (lw-ceiling-rational (/ cutoff step))) (factor step))
                 (:instance lw-le-multiply-strict (a (lw-ceiling-rational (/ cutoff step))) (b (+ (/ cutoff step) 1)) (factor step)))
           :in-theory (disable lw-ceiling-rational-bracket lw-le-inverse-factor) :nonlinearp t))
  :rule-classes nil)

(local (in-theory (disable lw-log-signal-outside-window)))

(defthm lw-log-signal-grid-outside-window
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp address) (rationalp step) (< 0 step) (rationalp signal-error) (< 0 signal-error)
                (not (and (<= start (lw-log-signal-point (* address step) signal-error))
                          (<= (* (lw-log-signal-point (* address step) signal-error) (lw-log-signal-point (* address step) signal-error)) (* start start start)))))
           (or (< address (lw-kernel-window-left-count (cdr (lw-log-bounds start 1/1000)) step))
               (<= (lw-kernel-window-right-address (car (lw-log-bounds start 1/1000)) step) address)))
  :hints (("Goal"
           :use ((:instance lw-log-signal-outside-window (value (* address step)))
                 (:instance lw-log-bounds-interval (value start) (epsilon 1/1000))
                 (:instance lw-ceiling-rational-grid-separation (cutoff (cdr (lw-log-bounds start 1/1000))))
                 (:instance lw-ceiling-rational-grid-separation (cutoff (- (* 3/2 (car (lw-log-bounds start 1/1000))) 1))))
           :in-theory (enable lw-kernel-window-left-count lw-kernel-window-right-address) :nonlinearp t)))
