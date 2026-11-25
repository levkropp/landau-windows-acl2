(in-package "ACL2")

(include-book "complex-exp-grid")

; First-moment rectangle sums. Derive finite integration by parts from
; the actual exponential increment estimate, retaining every mesh and
; evaluation error.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-reciprocal lw-complex-quotient
                 lw-complex-exp-value lw-complex-exp-grid lw-complex-exp-primitive-value
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract)))

(local (defthm lw-cemg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cemg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cemg-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cemg-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cemg-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cemg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cemg-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cemg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cemg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cemg-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-cemg-sub-self
         (implies (lw-complexp point) (equal (lw-complex-sub point point) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))
(local (defthm lw-cemg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-exp-moment-grid (point start step count error)
  (if (zp count) (cons 0 0)
    (lw-complex-add
      (lw-complex-exp-moment-grid point start step (- count 1) error)
      (lw-complex-scale (* step (+ start (* (- count 1) step)))
        (lw-complex-exp-value (lw-complex-scale (+ start (* (- count 1) step)) point) error)))))

(defthm lw-complex-exp-moment-grid-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp step)
                (natp count) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-moment-grid point start step count error))))

(defun lw-complex-exp-moment-step-budget (point step bound argument-cap error)
  (+ (* bound (lw-complex-exp-grid-step-budget point step argument-cap error))
     (* (lw-complex-exp-uniform-cap argument-cap) (lw-complex-l1 point) step step)))

(local (defthm lw-cemg-weighted-step
         (implies (and (lw-complexp point) (lw-complexp current) (lw-complexp next)
                       (rationalp start) (rationalp step))
                  (equal
                   (lw-complex-sub (lw-complex-scale (+ start step) next)
                     (lw-complex-add (lw-complex-scale start current)
                       (lw-complex-add (lw-complex-scale step current)
                         (lw-complex-mul point (lw-complex-scale (* step start) current)))))
                   (lw-complex-add
                     (lw-complex-scale (+ start step)
                       (lw-complex-sub next
                         (lw-complex-add current
                           (lw-complex-mul point (lw-complex-scale step current)))))
                     (lw-complex-scale (* step step) (lw-complex-mul point current)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul lw-complex-scale)))
         :rule-classes nil))

(defthm lw-complex-exp-moment-rectangle-defect
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp bound) (rationalp step) (< 0 step) (<= (+ start step) bound)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) step) 1)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-scale (+ start step)
        (lw-complex-exp-value (lw-complex-scale (+ start step) point) error))
      (lw-complex-add
        (lw-complex-scale start (lw-complex-exp-value (lw-complex-scale start point) error))
        (lw-complex-add
          (lw-complex-scale step (lw-complex-exp-value (lw-complex-scale start point) error))
          (lw-complex-mul point
            (lw-complex-scale (* step start)
              (lw-complex-exp-value (lw-complex-scale start point) error))))))
    (lw-complex-exp-moment-step-budget point step bound argument-cap error)))
  :hints (("Goal"
           :use (lw-complex-exp-rectangle-defect
                 (:instance lw-complex-l1-bound)
                 (:instance lw-cemg-multiply-order
                   (a start) (b bound) (factor (lw-complex-l1 point)))
                 (:instance lw-complex-exp-value-uniform-bound
                   (point (lw-complex-scale start point)))
                 (:instance lw-cemg-weighted-step
                   (current (lw-complex-exp-value (lw-complex-scale start point) error))
                   (next (lw-complex-exp-value (lw-complex-scale (+ start step) point) error)))
                 (:instance lw-complex-scale-disk
                   (factor (+ start step))
                   (point (lw-complex-sub
                     (lw-complex-exp-value (lw-complex-scale (+ start step) point) error)
                     (lw-complex-add (lw-complex-exp-value (lw-complex-scale start point) error)
                       (lw-complex-mul point
                         (lw-complex-scale step
                           (lw-complex-exp-value (lw-complex-scale start point) error))))))
                   (radius (lw-complex-exp-grid-step-budget point step argument-cap error)))
                 (:instance lw-complex-mul-disk (left point) (radius (lw-complex-l1 point))
                   (right (lw-complex-exp-value (lw-complex-scale start point) error))
                   (other-radius (lw-complex-exp-uniform-cap argument-cap)))
                 (:instance lw-complex-scale-disk
                   (factor (* step step))
                   (point (lw-complex-mul point
                     (lw-complex-exp-value (lw-complex-scale start point) error)))
                   (radius (* (lw-complex-l1 point) (lw-complex-exp-uniform-cap argument-cap))))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-scale (+ start step)
                     (lw-complex-sub
                       (lw-complex-exp-value (lw-complex-scale (+ start step) point) error)
                       (lw-complex-add (lw-complex-exp-value (lw-complex-scale start point) error)
                         (lw-complex-mul point
                           (lw-complex-scale step
                             (lw-complex-exp-value (lw-complex-scale start point) error)))))))
                   (radius (* (+ start step)
                              (lw-complex-exp-grid-step-budget point step argument-cap error)))
                   (right (lw-complex-scale (* step step)
                     (lw-complex-mul point
                       (lw-complex-exp-value (lw-complex-scale start point) error))))
                   (other-radius (* step step (lw-complex-l1 point)
                                    (lw-complex-exp-uniform-cap argument-cap))))
                 (:instance lw-cemg-multiply-order (a (+ start step)) (b bound)
                   (factor (lw-complex-exp-grid-step-budget point step argument-cap error)))
                 (:instance lw-complex-disk-enlarge
                   (point
                    (lw-complex-sub
                     (lw-complex-scale (+ start step)
                       (lw-complex-exp-value (lw-complex-scale (+ start step) point) error))
                     (lw-complex-add
                       (lw-complex-scale start
                         (lw-complex-exp-value (lw-complex-scale start point) error))
                       (lw-complex-add
                         (lw-complex-scale step
                           (lw-complex-exp-value (lw-complex-scale start point) error))
                         (lw-complex-mul point
                           (lw-complex-scale (* step start)
                             (lw-complex-exp-value (lw-complex-scale start point) error)))))))
                   (radius (+ (* (+ start step)
                                 (lw-complex-exp-grid-step-budget point step argument-cap error))
                              (* step step (lw-complex-l1 point)
                                 (lw-complex-exp-uniform-cap argument-cap))))
                   (cap (lw-complex-exp-moment-step-budget point step bound argument-cap error))))
           :in-theory (disable lw-complex-exp-rectangle-defect lw-complex-l1-bound
                               lw-complex-exp-value-uniform-bound lw-complex-scale-disk
                               lw-complex-mul-disk lw-complex-add-disk lw-complex-sub-add-first)
           :do-not-induct t)))

(local (defthm lw-cemg-last-range
         (implies (and (rationalp start) (<= 0 start) (rationalp step) (< 0 step)
                       (posp count) (rationalp bound) (<= (+ start (* count step)) bound))
                  (and (<= 0 (+ start (* (- count 1) step)))
                       (<= (+ start (* (- count 1) step) step) bound)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cemg-telescope-step
         (implies
          (and (lw-complexp end) (lw-complexp previous) (lw-complexp initial)
               (lw-complexp point) (lw-complexp total0) (lw-complexp total1)
               (lw-complexp cell0) (lw-complexp cell1))
          (equal
           (lw-complex-sub (lw-complex-sub end initial)
             (lw-complex-add (lw-complex-add total0 cell0)
               (lw-complex-mul point (lw-complex-add total1 cell1))))
           (lw-complex-add
             (lw-complex-sub (lw-complex-sub previous initial)
               (lw-complex-add total0 (lw-complex-mul point total1)))
             (lw-complex-sub end
               (lw-complex-add previous (lw-complex-add cell0 (lw-complex-mul point cell1)))))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul)))
         :rule-classes nil))

(local (defthm lw-cemg-grid-zero
         (equal (lw-complex-exp-grid point start step 0 error) (cons 0 0))
         :hints (("Goal" :expand ((lw-complex-exp-grid point start step 0 error))))))

(defthm lw-complex-exp-moment-grid-telescope
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
        (lw-complex-scale (+ start (* count step))
          (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error))
        (lw-complex-scale start (lw-complex-exp-value (lw-complex-scale start point) error)))
      (lw-complex-add (lw-complex-exp-grid point start step count error)
        (lw-complex-mul point (lw-complex-exp-moment-grid point start step count error))))
    (* count (lw-complex-exp-moment-step-budget point step bound argument-cap error))))
  :hints (("Goal" :induct (lw-complex-exp-moment-grid point start step count error)
                  :expand ((lw-complex-exp-grid point start step count error))
                  :in-theory (disable lw-complex-exp-moment-rectangle-defect lw-complex-add-disk))
          (and stable-under-simplificationp
               '(:use (lw-cemg-last-range
                       (:instance lw-complex-exp-moment-rectangle-defect
                         (start (+ start (* (- count 1) step))))
                       (:instance lw-cemg-telescope-step
                         (end (lw-complex-scale (+ start (* count step))
                           (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error)))
                         (previous (lw-complex-scale (+ start (* (- count 1) step))
                           (lw-complex-exp-value
                             (lw-complex-scale (+ start (* (- count 1) step)) point) error)))
                         (initial (lw-complex-scale start
                           (lw-complex-exp-value (lw-complex-scale start point) error)))
                         (total0 (lw-complex-exp-grid point start step (- count 1) error))
                         (total1 (lw-complex-exp-moment-grid point start step (- count 1) error))
                         (cell0 (lw-complex-scale step
                           (lw-complex-exp-value
                             (lw-complex-scale (+ start (* (- count 1) step)) point) error)))
                         (cell1 (lw-complex-scale (* step (+ start (* (- count 1) step)))
                           (lw-complex-exp-value
                             (lw-complex-scale (+ start (* (- count 1) step)) point) error))))
                       (:instance lw-complex-add-disk
                         (left (lw-complex-sub
                           (lw-complex-sub
                             (lw-complex-scale (+ start (* (- count 1) step))
                               (lw-complex-exp-value
                                 (lw-complex-scale (+ start (* (- count 1) step)) point) error))
                             (lw-complex-scale start
                               (lw-complex-exp-value (lw-complex-scale start point) error)))
                           (lw-complex-add (lw-complex-exp-grid point start step (- count 1) error)
                             (lw-complex-mul point
                               (lw-complex-exp-moment-grid point start step (- count 1) error)))))
                         (radius (* (- count 1)
                           (lw-complex-exp-moment-step-budget point step bound argument-cap error)))
                         (right (lw-complex-sub
                           (lw-complex-scale (+ start (* count step))
                             (lw-complex-exp-value
                               (lw-complex-scale (+ start (* count step)) point) error))
                           (lw-complex-add
                             (lw-complex-scale (+ start (* (- count 1) step))
                               (lw-complex-exp-value
                                 (lw-complex-scale (+ start (* (- count 1) step)) point) error))
                             (lw-complex-add
                               (lw-complex-scale step
                                 (lw-complex-exp-value
                                   (lw-complex-scale (+ start (* (- count 1) step)) point) error))
                               (lw-complex-mul point
                                 (lw-complex-scale (* step (+ start (* (- count 1) step)))
                                   (lw-complex-exp-value
                                     (lw-complex-scale (+ start (* (- count 1) step)) point) error)))))))
                         (other-radius (lw-complex-exp-moment-step-budget
                                         point step bound argument-cap error))))
                 :in-theory (disable lw-complex-sub-add-first)
                 :do-not-induct t))))

(defun lw-complex-exp-moment-primitive (point start end error)
  (lw-complex-quotient
    (lw-complex-sub
      (lw-complex-sub
        (lw-complex-scale end (lw-complex-exp-value (lw-complex-scale end point) error))
        (lw-complex-scale start (lw-complex-exp-value (lw-complex-scale start point) error)))
      (lw-complex-exp-primitive-value point start end error)) point))

(defthm lw-complex-exp-moment-primitive-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-moment-primitive point start end error))))

(local (in-theory
        (disable lw-complex-exp-moment-grid lw-complex-exp-moment-primitive
                 lw-complex-exp-grid-step-budget lw-complex-exp-moment-step-budget)))

(local (defthm lw-cemg-last-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a (cons 0 0))))
                  (equal (lw-complex-mul a (lw-complex-mul b (lw-complex-reciprocal a))) b))
         :hints (("Goal" :use ((:instance lw-complex-mul-left-commutes
                                (c (lw-complex-reciprocal a))))
                         :in-theory (disable lw-complex-mul-commutative
                                             lw-complex-mul-left-commutes)))))

(local (defthm lw-cemg-quotient-defect
         (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                       (lw-complexp value) (lw-complexp total))
                  (equal
                   (lw-complex-quotient (lw-complex-sub value (lw-complex-mul point total)) point)
                   (lw-complex-sub (lw-complex-quotient value point) total)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient lw-complex-mul-subtract
                                          lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(local (defthm lw-cemg-residual-combine
         (implies (and (lw-complexp weighted) (lw-complexp total0) (lw-complexp total1)
                       (lw-complexp primitive0) (lw-complexp point))
                  (equal
                   (lw-complex-add
                     (lw-complex-sub weighted (lw-complex-add total0 (lw-complex-mul point total1)))
                     (lw-complex-sub total0 primitive0))
                   (lw-complex-sub (lw-complex-sub weighted primitive0)
                                   (lw-complex-mul point total1))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul)))))

(local (defthm lw-cemg-quotient-disk
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

(defun lw-complex-exp-moment-grid-budget (point step bound argument-cap count clearance error)
  (* count
     (+ (lw-complex-exp-moment-step-budget point step bound argument-cap error)
        (* (lw-complex-exp-grid-step-budget point step argument-cap error) (/ clearance)))
     (/ clearance)))

(defthm lw-complex-exp-moment-grid-primitive-error
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
      (lw-complex-exp-moment-primitive point start (+ start (* count step)) error)
      (lw-complex-exp-moment-grid point start step count error))
    (lw-complex-exp-moment-grid-budget point step bound argument-cap count clearance error)))
  :hints (("Goal"
           :use (lw-complex-exp-moment-grid-telescope lw-complex-exp-grid-primitive-error
                 (:instance lw-complex-norm-lower-nonzero (lower clearance))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-exp-primitive-value point start (+ start (* count step)) error))
                   (right (lw-complex-exp-grid point start step count error))
                   (radius (* count (lw-complex-exp-grid-step-budget point step argument-cap error)
                              (/ clearance))))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-sub
                     (lw-complex-sub
                       (lw-complex-scale (+ start (* count step))
                         (lw-complex-exp-value (lw-complex-scale (+ start (* count step)) point) error))
                       (lw-complex-scale start
                         (lw-complex-exp-value (lw-complex-scale start point) error)))
                     (lw-complex-add (lw-complex-exp-grid point start step count error)
                       (lw-complex-mul point (lw-complex-exp-moment-grid point start step count error)))))
                   (radius (* count (lw-complex-exp-moment-step-budget
                                     point step bound argument-cap error)))
                   (right (lw-complex-sub (lw-complex-exp-grid point start step count error)
                            (lw-complex-exp-primitive-value point start (+ start (* count step)) error)))
                   (other-radius (* count (lw-complex-exp-grid-step-budget point step argument-cap error)
                                    (/ clearance))))
                 (:instance lw-cemg-quotient-disk
                   (numerator (lw-complex-add
                     (lw-complex-sub
                       (lw-complex-sub
                         (lw-complex-scale (+ start (* count step))
                           (lw-complex-exp-value
                             (lw-complex-scale (+ start (* count step)) point) error))
                         (lw-complex-scale start
                           (lw-complex-exp-value (lw-complex-scale start point) error)))
                       (lw-complex-add (lw-complex-exp-grid point start step count error)
                         (lw-complex-mul point
                           (lw-complex-exp-moment-grid point start step count error))))
                     (lw-complex-sub (lw-complex-exp-grid point start step count error)
                       (lw-complex-exp-primitive-value point start (+ start (* count step)) error))))
                   (denominator point)
                   (radius (+ (* count (lw-complex-exp-moment-step-budget
                                        point step bound argument-cap error))
                              (* count (lw-complex-exp-grid-step-budget point step argument-cap error)
                                 (/ clearance))))))
           :in-theory
           (e/d (lw-complex-exp-moment-primitive)
                (lw-complex-exp-moment-grid-telescope lw-complex-exp-grid-primitive-error
                 lw-cemg-quotient-disk lw-complex-add-disk lw-complex-sub-add-first))
           :do-not-induct t)))

(local (defthm lw-cemg-quotient-subtract
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp denominator))
                  (equal (lw-complex-sub (lw-complex-quotient a denominator)
                                         (lw-complex-quotient b denominator))
                         (lw-complex-quotient (lw-complex-sub a b) denominator)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient)))))

(local (defthm lw-cemg-scale-subtract
         (implies (and (lw-complexp a) (lw-complexp b) (rationalp factor))
                  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                         (lw-complex-scale factor (lw-complex-sub a b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-cemg-difference-differences
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
                  (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-sub c d))
                         (lw-complex-sub (lw-complex-sub a c) (lw-complex-sub b d))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(local (defthm lw-cemg-weighted-error-identity
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (lw-complexp d) (lw-complexp p) (lw-complexp q)
                       (rationalp start) (rationalp end))
                  (equal
                   (lw-complex-sub
                    (lw-complex-sub (lw-complex-sub (lw-complex-scale end a)
                                                     (lw-complex-scale start b)) p)
                    (lw-complex-sub (lw-complex-sub (lw-complex-scale end c)
                                                     (lw-complex-scale start d)) q))
                   (lw-complex-sub
                    (lw-complex-sub (lw-complex-scale end (lw-complex-sub a c))
                                     (lw-complex-scale start (lw-complex-sub b d)))
                    (lw-complex-sub p q))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(defthm lw-complex-exp-moment-primitive-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (rationalp bound) (<= end bound)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-exp-moment-primitive point start end left-error)
                    (lw-complex-exp-moment-primitive point start end right-error))
    (* 2 (+ bound (/ clearance)) (+ left-error right-error) (/ clearance))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-value-cauchy (point (lw-complex-scale end point)))
                 (:instance lw-complex-exp-value-cauchy (point (lw-complex-scale start point)))
                 lw-complex-exp-primitive-cauchy
                 (:instance lw-complex-scale-disk
                   (factor end)
                   (point (lw-complex-sub
                     (lw-complex-exp-value (lw-complex-scale end point) left-error)
                     (lw-complex-exp-value (lw-complex-scale end point) right-error)))
                   (radius (+ left-error right-error)))
                 (:instance lw-complex-scale-disk
                   (factor start)
                   (point (lw-complex-sub
                     (lw-complex-exp-value (lw-complex-scale start point) left-error)
                     (lw-complex-exp-value (lw-complex-scale start point) right-error)))
                   (radius (+ left-error right-error)))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-scale end
                     (lw-complex-sub
                       (lw-complex-exp-value (lw-complex-scale end point) left-error)
                       (lw-complex-exp-value (lw-complex-scale end point) right-error))))
                   (radius (* end (+ left-error right-error)))
                   (right (lw-complex-scale start
                     (lw-complex-sub
                       (lw-complex-exp-value (lw-complex-scale start point) left-error)
                       (lw-complex-exp-value (lw-complex-scale start point) right-error))))
                   (other-radius (* start (+ left-error right-error))))
                 (:instance lw-complex-sub-disk
                   (left (lw-complex-sub
                     (lw-complex-scale end
                       (lw-complex-sub
                         (lw-complex-exp-value (lw-complex-scale end point) left-error)
                         (lw-complex-exp-value (lw-complex-scale end point) right-error)))
                     (lw-complex-scale start
                       (lw-complex-sub
                         (lw-complex-exp-value (lw-complex-scale start point) left-error)
                         (lw-complex-exp-value (lw-complex-scale start point) right-error)))))
                   (radius (+ (* end (+ left-error right-error)) (* start (+ left-error right-error))))
                   (right (lw-complex-sub (lw-complex-exp-primitive-value point start end left-error)
                                          (lw-complex-exp-primitive-value point start end right-error)))
                   (other-radius (* 2 (+ left-error right-error) (/ clearance))))
                 (:instance lw-cemg-multiply-order
                   (a (+ start end)) (b (* 2 bound)) (factor (+ left-error right-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-sub
                       (lw-complex-sub
                         (lw-complex-scale end
                           (lw-complex-exp-value (lw-complex-scale end point) left-error))
                         (lw-complex-scale start
                           (lw-complex-exp-value (lw-complex-scale start point) left-error)))
                       (lw-complex-exp-primitive-value point start end left-error))
                     (lw-complex-sub
                       (lw-complex-sub
                         (lw-complex-scale end
                           (lw-complex-exp-value (lw-complex-scale end point) right-error))
                         (lw-complex-scale start
                           (lw-complex-exp-value (lw-complex-scale start point) right-error)))
                       (lw-complex-exp-primitive-value point start end right-error))))
                   (radius (+ (* end (+ left-error right-error))
                              (* start (+ left-error right-error))
                              (* 2 (+ left-error right-error) (/ clearance))))
                   (cap (* 2 (+ bound (/ clearance)) (+ left-error right-error))))
                 (:instance lw-cemg-quotient-disk
                   (numerator (lw-complex-sub
                     (lw-complex-sub
                       (lw-complex-sub
                         (lw-complex-scale end
                           (lw-complex-exp-value (lw-complex-scale end point) left-error))
                         (lw-complex-scale start
                           (lw-complex-exp-value (lw-complex-scale start point) left-error)))
                       (lw-complex-exp-primitive-value point start end left-error))
                     (lw-complex-sub
                       (lw-complex-sub
                         (lw-complex-scale end
                           (lw-complex-exp-value (lw-complex-scale end point) right-error))
                         (lw-complex-scale start
                           (lw-complex-exp-value (lw-complex-scale start point) right-error)))
                       (lw-complex-exp-primitive-value point start end right-error))))
                   (denominator point)
                   (radius (* 2 (+ bound (/ clearance)) (+ left-error right-error)))))
           :in-theory (e/d (lw-complex-exp-moment-primitive)
                           (lw-complex-exp-value-cauchy lw-complex-exp-primitive-cauchy
                            lw-cemg-quotient-disk lw-complex-scale-disk lw-complex-sub-disk
                            lw-complex-sub-add-first lw-cemg-difference-differences))
           :do-not-induct t)))
