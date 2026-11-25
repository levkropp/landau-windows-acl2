(in-package "ACL2")

(include-book "complex-exp-multiply")

; Match the complex Taylor evaluator at -x to the reciprocal bands used
; by the existing negative-exponential kernel, with computed precision.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-start-index lw-exp-depth lw-exp-initial-width
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cen-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cen-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cen-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cen-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cen-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cen-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cen-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cen-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cen-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-cen-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* (/ divisor) (* divisor coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x (/ divisor)) (y divisor) (z coefficient))
                              (:instance commutativity-of-* (x (/ divisor)) (y divisor))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cen-left-commutes)))))
(local (defthm lw-cen-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cen-real-complex
         (implies (rationalp value) (lw-complexp (cons value 0)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-cen-real-product
         (implies (and (rationalp factor) (lw-complexp point))
                  (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))
(local (defthm lw-cen-real-cancel
         (implies (rationalp value)
                  (equal (lw-complex-add (cons value 0) (cons (- value) 0)) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complex-add)))))

(local (defun lw-cen-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-cen-countdown (- index 1)))))
(local (defthm lw-cen-real-zero-term
         (implies (posp index) (equal (lw-exp-term 0 index) 0))
         :hints (("Goal" :expand ((lw-exp-term 0 index))))))
(local (defthm lw-cen-real-zero-sum
         (implies (natp index) (equal (lw-exp-sum 0 index) 1))
         :hints (("Goal" :induct (lw-cen-countdown index)
                         :expand ((lw-exp-sum 0 index))))))
(local (defthm lw-cen-zero-term
         (implies (natp index)
                  (equal (lw-complex-exp-term (cons 0 0) index) (if (zp index) (cons 1 0) (cons 0 0))))
         :hints (("Goal" :expand ((lw-complex-exp-term (cons 0 0) index))))))
(local (defthm lw-cen-zero-sum
         (implies (natp index) (equal (lw-complex-exp-sum (cons 0 0) index) (cons 1 0)))
         :hints (("Goal" :induct (lw-cen-countdown index)
                         :expand ((lw-complex-exp-sum (cons 0 0) index))))))

(defthm lw-complex-exp-value-zero
  (implies (and (rationalp error) (< 0 error))
           (equal (lw-complex-exp-value (cons 0 0) error) (cons 1 0)))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (value 0) (epsilon error)))
                  :in-theory (e/d (lw-complex-exp-value lw-complex-l1 lw-exp-bounds lw-exp-band)
                                  (lw-exp-index-adequate)))))

(local (defthm lw-cen-negative-cap
         (implies (and (rationalp value) (<= 0 value))
                  (equal (lw-complex-exp-cap (cons (- value) 0))
                         (lw-complex-exp-cap (cons value 0))))
         :hints (("Goal" :in-theory (enable lw-complex-exp-cap lw-complex-l1)))))

(defthm lw-complex-exp-negative-product
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-scale (car (lw-exp-bounds value error))
                               (lw-complex-exp-value (cons (- value) 0) error))
             (cons 1 0))
            (* (+ 2 (* 2 (lw-complex-exp-cap (cons value 0)))) error)))
  :hints (("Goal" :use ((:instance lw-complex-exp-value-multiplication
                          (left (cons value 0)) (right (cons (- value) 0))
                          (left-error error) (right-error error) (sum-error error))
                        (:instance lw-exp-bounds-valid (epsilon error)))
                  :in-theory (disable lw-complex-exp-value-multiplication lw-exp-bounds-valid))))

(local (defthm lw-cen-inverse-error-identity
         (implies (and (rationalp factor) (<= 1 factor) (lw-complexp point))
                  (equal (lw-complex-scale (/ factor)
                          (lw-complex-sub (lw-complex-scale factor point) (cons 1 0)))
                         (lw-complex-sub point (cons (/ factor) 0))))
         :hints (("Goal" :use ((:instance lw-cen-inverse-factor (divisor factor) (coefficient (car point)))
                              (:instance lw-cen-inverse-factor (divisor factor) (coefficient (cdr point))))
                         :in-theory (e/d (lw-complexp lw-complex-scale lw-complex-sub)
                                         (lw-cen-inverse-factor))))))

(defthm lw-complex-real-inverse-error
  (implies (and (rationalp factor) (<= 1 factor) (lw-complexp point)
                (lw-complex-diskp (lw-complex-sub (lw-complex-scale factor point) (cons 1 0)) radius))
           (lw-complex-diskp (lw-complex-sub point (cons (/ factor) 0)) radius))
  :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left 1) (right factor))
                        (:instance lw-complex-scale-disk
                          (point (lw-complex-sub (lw-complex-scale factor point) (cons 1 0))) (factor (/ factor)))
                        (:instance lw-cen-multiply-order (a (/ factor)) (b 1) (factor radius))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub point (cons (/ factor) 0)))
                          (radius (* (/ factor) radius)) (cap radius)))
                  :in-theory (disable lw-reciprocal-antitone lw-complex-scale-disk))))

(defthm lw-complex-exp-negative-reciprocal
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-value (cons (- value) 0) error)
                            (cons (/ (car (lw-exp-bounds value error))) 0))
            (* (+ 2 (* 2 (lw-complex-exp-cap (cons value 0)))) error)))
  :hints (("Goal" :use (lw-complex-exp-negative-product
                        (:instance lw-exp-bounds-valid (epsilon error))
                        (:instance lw-complex-real-inverse-error
                          (factor (car (lw-exp-bounds value error)))
                          (point (lw-complex-exp-value (cons (- value) 0) error))
                          (radius (* (+ 2 (* 2 (lw-complex-exp-cap (cons value 0)))) error))))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-complex-exp-negative-product lw-exp-bounds-valid
                                   lw-complex-real-inverse-error)))))

(defthm lw-exp-neg-upper-lower-comparison
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (cdr (lw-exp-neg-bounds value left-error))
                       (car (lw-exp-neg-bounds value right-error)))) (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-exp-neg-bounds-valid (epsilon left-error))
                        (:instance lw-exp-neg-bounds-valid (epsilon right-error))
                        lw-exp-neg-bounds-overlap
                        (:instance lw-exp-neg-bounds-overlap (left-error right-error) (right-error left-error))
                        (:instance lw-exp-neg-bounds-width (epsilon left-error))
                        (:instance lw-exp-neg-bounds-width (epsilon right-error)))
                  :in-theory (e/d (lw-intervalp)
                                  (lw-exp-neg-bounds-valid lw-exp-neg-bounds-overlap lw-exp-neg-bounds-width)))))

(local (defthm lw-cen-real-difference-disk
         (implies (and (rationalp a) (rationalp b) (rationalp error) (<= 0 error)
                       (<= (abs (- a b)) error))
                  (lw-complex-diskp (lw-complex-sub (cons a 0) (cons b 0)) error))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-diskp lw-diskp)
                         :cases ((<= b a)) :nonlinearp t))
         :rule-classes nil))

(defthm lw-complex-exp-negative-agreement
  (implies (and (rationalp value) (<= 0 value)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-value (cons (- value) 0) left-error)
                            (cons (car (lw-exp-neg-bounds value right-error)) 0))
            (+ (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0)))) left-error) right-error)))
  :hints (("Goal" :use ((:instance lw-complex-exp-negative-reciprocal (error left-error))
                        lw-exp-neg-upper-lower-comparison
                        (:instance lw-exp-neg-bounds-valid (epsilon left-error))
                        (:instance lw-exp-neg-bounds-valid (epsilon right-error))
                        (:instance lw-cen-real-difference-disk
                          (a (cdr (lw-exp-neg-bounds value left-error)))
                          (b (car (lw-exp-neg-bounds value right-error))) (error (+ left-error right-error)))
                        (:instance lw-complex-difference-triangle
                          (left (lw-complex-exp-value (cons (- value) 0) left-error))
                          (middle (cons (cdr (lw-exp-neg-bounds value left-error)) 0))
                          (right (cons (car (lw-exp-neg-bounds value right-error)) 0))
                          (radius (* (+ 2 (* 2 (lw-complex-exp-cap (cons value 0)))) left-error))
                          (other-radius (+ left-error right-error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-complex-exp-value (cons (- value) 0) left-error)
                                                 (cons (car (lw-exp-neg-bounds value right-error)) 0)))
                          (radius (+ (* (+ 2 (* 2 (lw-complex-exp-cap (cons value 0)))) left-error)
                                     left-error right-error))
                          (cap (+ (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0)))) left-error) right-error))))
                  :in-theory (e/d (lw-exp-neg-bounds)
                                  (lw-complex-exp-negative-reciprocal lw-exp-neg-upper-lower-comparison
                                   lw-exp-neg-bounds-valid lw-complex-difference-triangle)))))

(defun lw-complex-exp-negative-precision (value error)
  (/ error (+ 5 (* 2 (lw-complex-exp-cap (cons value 0))))))

(defthm lw-complex-exp-negative-precision-adequate
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (rationalp (lw-complex-exp-negative-precision value error))
                (< 0 (lw-complex-exp-negative-precision value error))
                (<= (* (+ 4 (* 2 (lw-complex-exp-cap (cons value 0))))
                       (lw-complex-exp-negative-precision value error)) error)))
  :hints (("Goal" :use ((:instance lw-complex-exp-cap-valid (point (cons value 0)))
                        (:instance lw-positive-division-bound
                          (numerator (* (+ 4 (* 2 (lw-complex-exp-cap (cons value 0)))) error))
                          (divisor (+ 5 (* 2 (lw-complex-exp-cap (cons value 0))))) (bound error)))
                  :in-theory (disable lw-complex-exp-cap-valid) :nonlinearp t)))

(local (in-theory (disable lw-complex-exp-negative-precision)))

(defthm lw-complex-exp-computed-negative-agreement
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-exp-value (cons (- value) 0) (lw-complex-exp-negative-precision value error))
             (cons (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error))) 0))
            error))
  :hints (("Goal" :use (lw-complex-exp-negative-precision-adequate
                        (:instance lw-complex-exp-negative-agreement
                          (left-error (lw-complex-exp-negative-precision value error))
                          (right-error (lw-complex-exp-negative-precision value error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-exp-value (cons (- value) 0) (lw-complex-exp-negative-precision value error))
                                  (cons (car (lw-exp-neg-bounds value (lw-complex-exp-negative-precision value error))) 0)))
                          (radius (+ (* (+ 3 (* 2 (lw-complex-exp-cap (cons value 0))))
                                        (lw-complex-exp-negative-precision value error))
                                     (lw-complex-exp-negative-precision value error))) (cap error)))
                  :in-theory (disable lw-complex-exp-negative-precision-adequate
                                      lw-complex-exp-negative-agreement))))

; At this precision the computed order is 7. Independently,
; E_7(-1)=103/280 and 1/(E_7(1)+2/8!)=2240/6089.
(assert-event
 (and (equal (lw-complex-exp-value (cons -1 0) 1/100) (cons 103/280 0))
      (equal (car (lw-exp-neg-bounds 1 1/100)) 2240/6089)))
