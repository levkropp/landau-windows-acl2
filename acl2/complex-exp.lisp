(in-package "ACL2")

(include-book "cauchy-polynomials")
(include-book "exp-bounds")

; Rational complex Taylor sums for the exponential. Tail bounds are
; proved for every later finite sum before defining an evaluator.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-conjugate lw-complex-norm-square lw-complex-diskp lw-diskp
                 lw-complex-reciprocal lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-coefficient-at lw-complex-l1
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-cauchy-moment-count lw-cauchy-orbit-moment
                 lw-cauchy-moment-expansion lw-cauchy-correlation-expansion lw-cauchy-residual-expansion
                 lw-complex-correlation-sum lw-complex-signed-power lw-complex-geometric-average
                 lw-complex-geometric-sum lw-cauchy-evaluation-sum lw-cauchy-polynomial-average
                 lw-complex-conjugate-power lw-complex-power-power lw-complex-power-add
                 lw-complex-scale-add lw-complex-scale-product
                 lw-exp-term lw-exp-sum lw-exp-band lw-exp-index lw-exp-bounds
                 lw-exp-start-index lw-exp-depth lw-exp-initial-width)))

(local (defthm lw-cx-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cx-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cx-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cx-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cx-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cx-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defun lw-cx-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-cx-countdown (- index 1)))))

(defun lw-complex-exp-term (point index)
  (if (zp index) (cons 1 0)
    (lw-complex-scale (/ index)
                      (lw-complex-mul point (lw-complex-exp-term point (- index 1))))))

(defthm lw-complex-exp-term-rational
  (implies (and (lw-complexp point) (natp index))
           (lw-complexp (lw-complex-exp-term point index))))

(local (defthm lw-cx-real-term-zero
         (implies (zp index) (equal (lw-exp-term value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-term)))))
(local (defthm lw-cx-term-zero
         (implies (zp index) (equal (lw-complex-exp-term point index) (cons 1 0)))))

(defthm lw-complex-exp-term-majorant
  (implies (and (lw-complex-diskp point radius) (natp index))
           (lw-complex-diskp (lw-complex-exp-term point index) (lw-exp-term radius index)))
  :hints (("Goal" :induct (lw-cx-countdown index)
                  :expand ((lw-complex-exp-term point index) (lw-exp-term radius index)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-mul-disk
                          (left point) (radius radius)
                          (right (lw-complex-exp-term point (- index 1)))
                          (other-radius (lw-exp-term radius (- index 1))))
                        (:instance lw-complex-scale-disk
                          (point (lw-complex-mul point (lw-complex-exp-term point (- index 1))))
                          (radius (* radius (lw-exp-term radius (- index 1)))) (factor (/ index))))
                 :in-theory (disable lw-complex-exp-term lw-exp-term
                                     lw-complex-mul-disk lw-complex-scale-disk)))))

(defun lw-complex-exp-sum (point index)
  (if (zp index) (cons 1 0)
    (lw-complex-add (lw-complex-exp-term point index)
                    (lw-complex-exp-sum point (- index 1)))))

(defthm lw-complex-exp-sum-rational
  (implies (and (lw-complexp point) (natp index))
           (lw-complexp (lw-complex-exp-sum point index))))

(local (defthm lw-cx-real-sum-zero
         (implies (zp index) (equal (lw-exp-sum value index) 1))
         :hints (("Goal" :in-theory (enable lw-exp-sum)))))
(local (defthm lw-cx-sum-zero
         (implies (zp index) (equal (lw-complex-exp-sum point index) (cons 1 0)))))

(local (in-theory (disable lw-complex-exp-term lw-complex-exp-sum)))

(local (defun lw-cx-range (large small)
         (declare (xargs :measure (nfix large)))
         (if (or (zp large) (<= large small)) 0 (lw-cx-range (- large 1) small))))

(local (defthm lw-cx-add-sub-cancel
         (implies (and (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-add a (lw-complex-sub b (lw-complex-add a b))) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(defthm lw-complex-exp-sum-difference-majorant
  (implies (and (lw-complex-diskp point radius) (natp small) (natp large) (<= small large))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-sum point large) (lw-complex-exp-sum point small))
            (- (lw-exp-sum radius large) (lw-exp-sum radius small))))
  :hints (("Goal" :induct (lw-cx-range large small)
                  :expand ((lw-complex-exp-sum point large) (lw-exp-sum radius large))
                  :in-theory (disable lw-complex-add-commutative lw-complex-add-left-commutes))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-exp-term-majorant (index large))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-exp-term point large)) (radius (lw-exp-term radius large))
                          (right (lw-complex-sub (lw-complex-exp-sum point (- large 1))
                                                 (lw-complex-exp-sum point small)))
                          (other-radius (- (lw-exp-sum radius (- large 1)) (lw-exp-sum radius small)))))
                 :in-theory (disable lw-complex-add-commutative lw-complex-add-left-commutes
                                     lw-complex-add-disk lw-complex-exp-term-majorant)))))

(defthm lw-complex-exp-sum-tail
  (implies (and (lw-complex-diskp point radius) (natp small) (natp large) (<= small large)
                (<= (* 2 radius) (+ 2 small)))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-sum point large) (lw-complex-exp-sum point small))
            (* 2 (lw-exp-term radius (+ 1 small)))))
  :hints (("Goal" :use (lw-complex-exp-sum-difference-majorant
                        (:instance lw-exp-later-partial-sum-enclosed (value radius))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-complex-exp-sum point large)
                                                 (lw-complex-exp-sum point small)))
                          (radius (- (lw-exp-sum radius large) (lw-exp-sum radius small)))
                          (cap (* 2 (lw-exp-term radius (+ 1 small))))))
                  :in-theory (e/d (lw-exp-band)
                                  (lw-complex-exp-sum-difference-majorant lw-complex-disk-enlarge)))))

(defthm lw-exp-index-tail-budget
  (implies (and (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (<= (* 2 (lw-exp-term radius (+ 1 (lw-exp-index radius error)))) error))
  :hints (("Goal" :use ((:instance lw-exp-bounds-width (value radius) (epsilon error))
                        (:instance lw-exp-index-adequate (value radius) (epsilon error)))
                  :in-theory (enable lw-exp-bounds lw-exp-band))))

(defun lw-complex-exp-value (point error)
  (lw-complex-exp-sum point (lw-exp-index (lw-complex-l1 point) error)))

(defthm lw-complex-exp-value-rational
  (implies (and (lw-complexp point) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-value point error)))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 point)) (epsilon error))))))

(defthm lw-complex-exp-value-tail
  (implies (and (lw-complexp point) (rationalp error) (< 0 error) (natp large)
                (<= (lw-exp-index (lw-complex-l1 point) error) large))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-sum point large) (lw-complex-exp-value point error)) error))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 point)) (epsilon error))
                        (:instance lw-exp-index-tail-budget (radius (lw-complex-l1 point)))
                        (:instance lw-complex-exp-sum-tail (radius (lw-complex-l1 point))
                          (small (lw-exp-index (lw-complex-l1 point) error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-complex-exp-sum point large)
                                                 (lw-complex-exp-value point error)))
                          (radius (* 2 (lw-exp-term (lw-complex-l1 point)
                                                   (+ 1 (lw-exp-index (lw-complex-l1 point) error)))))
                          (cap error)))
                  :in-theory (disable lw-complex-exp-sum-tail lw-complex-disk-enlarge
                                      lw-complex-l1-bound lw-exp-index-tail-budget lw-exp-index-adequate))))

(defthm lw-complex-scale-compose
  (implies (and (rationalp left) (rationalp right) (lw-complexp point))
           (equal (lw-complex-scale left (lw-complex-scale right point))
                  (lw-complex-scale (* left right) point)))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale))))

(local (defthm lw-cx-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(defthm lw-complex-mul-scales
  (implies (and (rationalp left) (rationalp right) (lw-complexp a) (lw-complexp b))
           (equal (lw-complex-mul (lw-complex-scale left a) (lw-complex-scale right b))
                  (lw-complex-scale (* left right) (lw-complex-mul a b))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale lw-complex-mul))))

(local (defthm lw-cx-power-zero
         (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-power)))))

(defthm lw-complex-exp-term-scaled-power
  (implies (and (rationalp value) (lw-complexp point) (natp index))
           (equal (lw-complex-exp-term (lw-complex-scale value point) index)
                  (lw-complex-scale (lw-exp-term value index) (lw-complex-power point index))))
  :hints (("Goal" :induct (lw-cx-countdown index)
                  :expand ((lw-complex-exp-term (lw-complex-scale value point) index)
                           (lw-complex-power point index) (lw-exp-term value index)))))

(local (defthm lw-cx-scale-one-pair
         (implies (rationalp factor) (equal (lw-complex-scale factor (cons 1 0)) (cons factor 0)))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-cx-one-power
         (equal (lw-complex-power (cons 1 0) index) (cons 1 0))
         :hints (("Goal" :induct (lw-cx-countdown index)
                         :in-theory (enable lw-complex-power)))))

(defthm lw-complex-exp-term-real
  (implies (and (rationalp value) (natp index))
           (equal (lw-complex-exp-term (cons value 0) index) (cons (lw-exp-term value index) 0)))
  :hints (("Goal" :use ((:instance lw-complex-exp-term-scaled-power (point (cons 1 0))))
                  :in-theory (disable lw-complex-exp-term-scaled-power))))

(defthm lw-complex-exp-sum-real
  (implies (and (rationalp value) (natp index))
           (equal (lw-complex-exp-sum (cons value 0) index) (cons (lw-exp-sum value index) 0)))
  :hints (("Goal" :induct (lw-cx-countdown index)
                  :expand ((lw-complex-exp-sum (cons value 0) index) (lw-exp-sum value index))
                  :in-theory (enable lw-complex-add))))

(defthm lw-complex-exp-value-real
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (equal (lw-complex-exp-value (cons value 0) error)
                  (cons (car (lw-exp-bounds value error)) 0)))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (epsilon error)))
                  :in-theory (enable lw-complex-l1 lw-exp-bounds lw-exp-band))))

(local (in-theory (disable lw-complex-exp-value)))

(defthm lw-complex-exp-value-cauchy
  (implies (and (lw-complexp point) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-value point left-error) (lw-complex-exp-value point right-error))
            (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 point)) (epsilon left-error))
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 point)) (epsilon right-error))
                        (:instance lw-complex-exp-value-tail (error left-error)
                          (large (max (lw-exp-index (lw-complex-l1 point) left-error)
                                      (lw-exp-index (lw-complex-l1 point) right-error))))
                        (:instance lw-complex-exp-value-tail (error right-error)
                          (large (max (lw-exp-index (lw-complex-l1 point) left-error)
                                      (lw-exp-index (lw-complex-l1 point) right-error))))
                        (:instance lw-complex-difference-symmetric
                          (left (lw-complex-exp-sum
                                 point (max (lw-exp-index (lw-complex-l1 point) left-error)
                                             (lw-exp-index (lw-complex-l1 point) right-error))))
                          (right (lw-complex-exp-value point left-error)) (radius left-error))
                        (:instance lw-complex-difference-triangle
                          (left (lw-complex-exp-value point left-error))
                          (middle (lw-complex-exp-sum
                                   point (max (lw-exp-index (lw-complex-l1 point) left-error)
                                               (lw-exp-index (lw-complex-l1 point) right-error))))
                          (right (lw-complex-exp-value point right-error))
                          (radius left-error) (other-radius right-error)))
                  :in-theory (disable lw-complex-exp-value-tail lw-complex-l1-bound lw-exp-index-adequate
                                      lw-complex-difference-triangle))))

; Exact low-degree values independently check imaginary signs and factorials.
(assert-event
 (and (equal (lw-complex-exp-sum (cons 0 1) 4) (cons 13/24 5/6))
      (equal (lw-complex-exp-term (cons 0 2) 3) (cons 0 -4/3))))

; The Taylor order below depends only on a disk radius, even though the
; exponential evaluator uses its own L1 cap for each individual point.
(defthm lw-complex-exp-prefix-error
  (implies (and (lw-complex-diskp point radius) (natp small)
                (<= (* 2 radius) (+ 2 small)) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-exp-sum point small) (lw-complex-exp-value point error))
            (+ (* 2 (lw-exp-term radius (+ 1 small))) error)))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound)
                        (:instance lw-exp-index-adequate (value (lw-complex-l1 point)) (epsilon error))
                        (:instance lw-complex-exp-sum-tail
                          (large (max small (lw-exp-index (lw-complex-l1 point) error))))
                        (:instance lw-complex-exp-value-tail
                          (large (max small (lw-exp-index (lw-complex-l1 point) error))))
                        (:instance lw-complex-difference-symmetric
                          (left (lw-complex-exp-sum point (max small (lw-exp-index (lw-complex-l1 point) error))))
                          (right (lw-complex-exp-sum point small))
                          (radius (* 2 (lw-exp-term radius (+ 1 small)))))
                        (:instance lw-complex-difference-triangle
                          (left (lw-complex-exp-sum point small))
                          (middle (lw-complex-exp-sum point (max small (lw-exp-index (lw-complex-l1 point) error))))
                          (right (lw-complex-exp-value point error))
                          (radius (* 2 (lw-exp-term radius (+ 1 small)))) (other-radius error)))
                  :in-theory (disable lw-complex-l1-bound lw-exp-index-adequate
                                      lw-complex-exp-sum-tail lw-complex-exp-value-tail
                                      lw-complex-difference-triangle))))

(defthm lw-complex-exp-computed-uniform-taylor
  (implies (and (lw-complex-diskp point radius) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-exp-sum point (lw-exp-index radius (/ error 2)))
             (lw-complex-exp-value point (/ error 2))) error))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (value radius) (epsilon (/ error 2)))
                        (:instance lw-exp-index-tail-budget (error (/ error 2)))
                        (:instance lw-complex-exp-prefix-error
                          (small (lw-exp-index radius (/ error 2))) (error (/ error 2)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-exp-sum point (lw-exp-index radius (/ error 2)))
                                  (lw-complex-exp-value point (/ error 2))))
                          (radius (+ (* 2 (lw-exp-term radius (+ 1 (lw-exp-index radius (/ error 2)))))
                                     (/ error 2))) (cap error)))
                  :in-theory (disable lw-exp-index-adequate lw-exp-index-tail-budget
                                      lw-complex-exp-prefix-error lw-complex-disk-enlarge))))
