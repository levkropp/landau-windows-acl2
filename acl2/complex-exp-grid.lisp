(in-package "ACL2")

(include-book "complex-exp-increment")
(include-book "complex-quotients")

; Finite left-rectangle sums for the actual complex exponential.
; Sum the first-order defects exactly; the error is explicit in the
; count, step, compact argument cap and primitive evaluation precision.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-l1 lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-reciprocal lw-complex-norm-square lw-complex-quotient
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract)))

(local (defthm lw-ceg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ceg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ceg-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ceg-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-ceg-zero-times (equal (* 0 a) 0)))
(local (defthm lw-ceg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-ceg-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-ceg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-ceg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-ceg-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-ceg-sub-self
         (implies (lw-complexp point) (equal (lw-complex-sub point point) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))
(local (defthm lw-ceg-scale-add-factors
         (implies (and (lw-complexp point) (rationalp a) (rationalp b))
                  (equal (lw-complex-add (lw-complex-scale a point) (lw-complex-scale b point))
                         (lw-complex-scale (+ a b) point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-scale)))))
(local (defthm lw-ceg-scale-product-swap
         (implies (and (lw-complexp a) (lw-complexp b) (rationalp factor))
                  (equal (lw-complex-mul (lw-complex-scale factor a) b)
                         (lw-complex-mul a (lw-complex-scale factor b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))

(defun lw-complex-exp-grid (point start step count error)
  (if (zp count) (cons 0 0)
    (lw-complex-add
      (lw-complex-exp-grid point start step (- count 1) error)
      (lw-complex-scale step
        (lw-complex-exp-value (lw-complex-scale (+ start (* (- count 1) step)) point) error)))))

(defthm lw-complex-exp-grid-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp step)
                (natp count) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-grid point start step count error))))

(defun lw-complex-exp-grid-step-budget (point step argument-cap error)
  (+ (* (lw-complex-exp-uniform-cap argument-cap)
        (lw-complex-l1 point) (lw-complex-l1 point) step step)
     (* (+ (lw-complex-exp-uniform-cap 1)
           (* 2 (lw-complex-exp-uniform-cap argument-cap)) 2) error)))

(defthm lw-complex-exp-rectangle-defect
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp bound) (<= start bound) (rationalp step) (< 0 step)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) step) 1)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-exp-value (lw-complex-scale (+ start step) point) error)
      (lw-complex-add (lw-complex-exp-value (lw-complex-scale start point) error)
        (lw-complex-mul point
          (lw-complex-scale step
            (lw-complex-exp-value (lw-complex-scale start point) error)))))
    (lw-complex-exp-grid-step-budget point step argument-cap error)))
  :hints (("Goal"
           :use ((:instance lw-complex-l1-bound)
                 (:instance lw-complex-l1-bound (point (lw-complex-scale step point)))
                 (:instance lw-complex-exp-increment-error
                   (left (lw-complex-scale start point)) (right (lw-complex-scale step point))
                   (left-cap argument-cap) (right-cap 1)
                   (radius (* (lw-complex-l1 point) step))))
           :in-theory (disable lw-complex-l1-bound lw-complex-exp-increment-error)
           :nonlinearp t :do-not-induct t)))

(local (defthm lw-ceg-telescope-step
         (implies (and (lw-complexp end) (lw-complexp previous) (lw-complexp initial)
                       (lw-complexp point) (lw-complexp total) (lw-complexp cell))
                  (equal
                   (lw-complex-sub (lw-complex-sub end initial)
                     (lw-complex-mul point (lw-complex-add total cell)))
                   (lw-complex-add
                     (lw-complex-sub (lw-complex-sub previous initial) (lw-complex-mul point total))
                     (lw-complex-sub end (lw-complex-add previous (lw-complex-mul point cell))))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul)))
         :rule-classes nil))

(local (defthm lw-ceg-last-range
         (implies (and (rationalp start) (<= 0 start) (rationalp step) (< 0 step)
                       (posp count) (rationalp bound) (<= (+ start (* count step)) bound))
                  (and (<= 0 (+ start (* (- count 1) step)))
                       (<= (+ start (* (- count 1) step)) bound)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-exp-grid-telescope
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp bound) (rationalp step) (< 0 step) (natp count)
        (<= (+ start (* count step)) bound)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) step) 1)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-sub
        (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error)
        (lw-complex-exp-value (lw-complex-scale start point) error))
      (lw-complex-mul point (lw-complex-exp-grid point start step count error)))
    (* count (lw-complex-exp-grid-step-budget point step argument-cap error))))
  :hints (("Goal" :induct (lw-complex-exp-grid point start step count error)
                  :in-theory (disable lw-complex-exp-rectangle-defect lw-complex-add-disk))
          (and stable-under-simplificationp
               '(:use (lw-ceg-last-range
                       (:instance lw-complex-exp-rectangle-defect
                          (start (+ start (* (- count 1) step))))
                       (:instance lw-ceg-telescope-step
                         (end (lw-complex-exp-value
                                (lw-complex-scale (+ start (* count step)) point) error))
                         (previous (lw-complex-exp-value
                                     (lw-complex-scale (+ start (* (- count 1) step)) point) error))
                         (initial (lw-complex-exp-value (lw-complex-scale start point) error))
                         (total (lw-complex-exp-grid point start step (- count 1) error))
                         (cell (lw-complex-scale step
                                 (lw-complex-exp-value
                                   (lw-complex-scale (+ start (* (- count 1) step)) point) error))))
                       (:instance lw-complex-add-disk
                         (left (lw-complex-sub
                           (lw-complex-sub
                             (lw-complex-exp-value
                               (lw-complex-scale (+ start (* (- count 1) step)) point) error)
                             (lw-complex-exp-value (lw-complex-scale start point) error))
                           (lw-complex-mul point
                             (lw-complex-exp-grid point start step (- count 1) error))))
                         (radius (* (- count 1)
                                    (lw-complex-exp-grid-step-budget point step argument-cap error)))
                         (right (lw-complex-sub
                           (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error)
                           (lw-complex-add
                             (lw-complex-exp-value
                               (lw-complex-scale (+ start (* (- count 1) step)) point) error)
                             (lw-complex-mul point
                               (lw-complex-scale step
                                 (lw-complex-exp-value
                                   (lw-complex-scale (+ start (* (- count 1) step)) point) error))))))
                         (other-radius (lw-complex-exp-grid-step-budget point step argument-cap error))))
                 :in-theory (disable lw-complex-sub-add-first)
                 :do-not-induct t))))

(defun lw-complex-exp-primitive-value (point start end error)
  (lw-complex-quotient
    (lw-complex-sub (lw-complex-exp-value (lw-complex-scale end point) error)
                    (lw-complex-exp-value (lw-complex-scale start point) error)) point))

(defthm lw-complex-exp-primitive-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-primitive-value point start end error))))

(local (in-theory (disable lw-complex-exp-primitive-value lw-complex-exp-grid-step-budget)))

(local (defthm lw-ceg-last-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a (cons 0 0))))
                  (equal (lw-complex-mul a
                           (lw-complex-mul b (lw-complex-reciprocal a))) b))
         :hints (("Goal" :use ((:instance lw-complex-mul-left-commutes
                                (c (lw-complex-reciprocal a))))
                         :in-theory (disable lw-complex-mul-commutative
                                             lw-complex-mul-left-commutes)))))

(local (defthm lw-ceg-quotient-defect
         (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                       (lw-complexp value) (lw-complexp total))
                  (equal
                   (lw-complex-quotient (lw-complex-sub value (lw-complex-mul point total)) point)
                   (lw-complex-sub (lw-complex-quotient value point) total)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient lw-complex-mul-subtract
                                          lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(local (defthm lw-ceg-quotient-disk
         (implies (and (lw-complex-diskp numerator radius) (lw-complexp denominator)
                       (rationalp clearance) (< 0 clearance)
                       (<= (* clearance clearance) (lw-complex-norm-square denominator)))
                  (lw-complex-diskp (lw-complex-quotient numerator denominator)
                                    (* radius (/ clearance))))
         :hints (("Goal"
                  :use ((:instance lw-complex-reciprocal-disk-bound
                          (point denominator) (lower clearance))
                        (:instance lw-complex-mul-disk
                          (left numerator) (right (lw-complex-reciprocal denominator))
                          (other-radius (/ clearance))))
                  :in-theory (e/d (lw-complex-quotient)
                                  (lw-complex-reciprocal-disk-bound lw-complex-mul-disk))))))

(defthm lw-complex-exp-grid-primitive-error
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp bound) (rationalp step) (< 0 step) (natp count)
        (<= (+ start (* count step)) bound)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) step) 1)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-exp-primitive-value point start (+ start (* count step)) error)
      (lw-complex-exp-grid point start step count error))
    (* count (lw-complex-exp-grid-step-budget point step argument-cap error) (/ clearance))))
  :hints (("Goal"
           :use (lw-complex-exp-grid-telescope
                 (:instance lw-complex-norm-lower-nonzero (lower clearance))
                 (:instance lw-ceg-quotient-defect
                   (value (lw-complex-sub
                     (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error)
                     (lw-complex-exp-value (lw-complex-scale start point) error)))
                   (total (lw-complex-exp-grid point start step count error)))
                 (:instance lw-ceg-quotient-disk
                   (numerator (lw-complex-sub
                     (lw-complex-sub
                       (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error)
                       (lw-complex-exp-value (lw-complex-scale start point) error))
                     (lw-complex-mul point (lw-complex-exp-grid point start step count error))))
                   (denominator point)
                   (radius (* count (lw-complex-exp-grid-step-budget point step argument-cap error)))))
           :in-theory (e/d (lw-complex-exp-primitive-value)
                           (lw-complex-exp-grid-telescope lw-ceg-quotient-defect
                            lw-ceg-quotient-disk lw-complex-sub-add-first))
           :do-not-induct t)))

(local (defthm lw-ceg-quotient-subtract
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp denominator))
                  (equal (lw-complex-sub (lw-complex-quotient a denominator)
                                         (lw-complex-quotient b denominator))
                         (lw-complex-quotient (lw-complex-sub a b) denominator)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient)))))

(local (defthm lw-ceg-difference-differences
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
                  (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-sub c d))
                         (lw-complex-sub (lw-complex-sub a c) (lw-complex-sub b d))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(local (defthm lw-ceg-double
         (implies (rationalp a) (equal (+ a a) (* 2 a)))))
(local (defthm lw-ceg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(defthm lw-complex-exp-primitive-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (rationalp end)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-exp-primitive-value point start end left-error)
                    (lw-complex-exp-primitive-value point start end right-error))
    (* 2 (+ left-error right-error) (/ clearance))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-value-cauchy
                   (point (lw-complex-scale end point)))
                 (:instance lw-complex-exp-value-cauchy
                   (point (lw-complex-scale start point)))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-sub
                     (lw-complex-exp-value (lw-complex-scale end point) left-error)
                     (lw-complex-exp-value (lw-complex-scale end point) right-error)))
                   (radius (+ left-error right-error))
                   (right (lw-complex-sub
                     (lw-complex-exp-value (lw-complex-scale start point) left-error)
                     (lw-complex-exp-value (lw-complex-scale start point) right-error)))
                   (other-radius (+ left-error right-error)))
                 (:instance lw-ceg-quotient-disk
                   (numerator (lw-complex-sub
                     (lw-complex-sub
                       (lw-complex-exp-value (lw-complex-scale end point) left-error)
                       (lw-complex-exp-value (lw-complex-scale start point) left-error))
                     (lw-complex-sub
                       (lw-complex-exp-value (lw-complex-scale end point) right-error)
                       (lw-complex-exp-value (lw-complex-scale start point) right-error))))
                   (denominator point) (radius (* 2 (+ left-error right-error)))))
           :in-theory (e/d (lw-complex-exp-primitive-value)
                           (lw-complex-exp-value-cauchy lw-ceg-quotient-disk
                            lw-complex-sub-disk lw-complex-sub-add-first))
           :do-not-induct t)))
