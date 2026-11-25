(in-package "ACL2")

(include-book "mellin-integrand")
(include-book "kernel-continuity")
(include-book "log-signal-continuity")
(include-book "phase-continuity")

(local (in-theory
        (disable lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-log-signal-bounds-valid lw-log-signal-bounds-width
                 lw-log-signal-bounds-overlap lw-log-signal-lower-spatial-bound
                 lw-log-signal-spatial-slope lw-log-signal-spatial-slope-valid
                 lw-exp-lipschitz-cap lw-exp-lipschitz-cap-valid
                 lw-kernel-weight-bounds lw-kernel-weight-bounds-valid lw-kernel-weight-bounds-width
                 lw-kernel-weight-bounds-overlap lw-kernel-weight-scale lw-kernel-weight-scale-spatial-cap
                 lw-kernel-weight-lower-spatial-bound lw-kernel-spatial-cap lw-kernel-spatial-slope
                 lw-kernel-spatial-parameters
                 lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid lw-mellin-error-budgets
                 lw-mellin-signal-bounded lw-mellin-weight-bounded lw-mellin-product-difference
                 lw-phase-value lw-phase-value-transport
                 lw-complexp lw-complex-diskp lw-complex-sub lw-complex-scale
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mc-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mc-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))
         :hints (("Goal" :use ((:instance lw-mc-times-negative (a b) (b a)))
                         :in-theory (disable lw-mc-times-negative)))))
(local (defthm lw-mc-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mc-times-zero (equal (* 0 a) 0)))
(local (defthm lw-mc-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-mc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c))
                  (<= (* a c) (* b c)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mc-abs-argument
         (implies (and (rationalp a) (rationalp b) (rationalp factor))
                  (equal (abs (- (- (* factor a)) (- (* factor b)))) (* (abs factor) (abs (- a b)))))
         :hints (("Goal" :cases ((<= a b) (<= 0 factor)) :nonlinearp t))))
(local (defthm lw-mc-anchor-bound
         (implies (and (rationalp x) (rationalp a) (rationalp r) (<= (abs (- x a)) r))
                  (<= (abs x) (+ (abs a) r)))
         :rule-classes nil))

(defun lw-mellin-signal-spatial-slope (cap)
  (* (lw-log-signal-spatial-slope cap) (lw-exp-lipschitz-cap cap)))
(defun lw-mellin-signal-spatial-cap (cap)
  (+ 2 (abs (car (lw-log-signal-bounds 0 1))) (abs (cdr (lw-log-signal-bounds 0 1)))
     (* (lw-mellin-signal-spatial-slope cap) cap)))
(defun lw-mellin-spatial-slope (cap sigma height step)
  (+ (* (lw-kernel-spatial-cap cap step) (lw-mellin-signal-spatial-slope cap))
     (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-slope cap sigma step))
     (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-cap cap step) (abs height))))
(defun lw-mellin-spatial-error-factor (cap step)
  (+ 1 (lw-kernel-spatial-cap cap step) (lw-mellin-signal-spatial-cap cap)
     (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-cap cap step))))

(defthm lw-mellin-signal-spatial-parameters
  (implies (and (rationalp cap) (<= 0 cap))
           (and (rationalp (lw-mellin-signal-spatial-slope cap)) (<= 0 (lw-mellin-signal-spatial-slope cap))
                (rationalp (lw-mellin-signal-spatial-cap cap)) (<= 2 (lw-mellin-signal-spatial-cap cap))))
  :hints (("Goal" :use (lw-log-signal-spatial-slope-valid lw-exp-lipschitz-cap-valid
                        (:instance lw-log-signal-bounds-valid (value 0) (error 1)))
                  :nonlinearp t)))

(local (in-theory (disable lw-mellin-signal-spatial-slope lw-mellin-signal-spatial-cap
                           lw-mellin-signal-spatial-parameters)))

(defthm lw-mellin-spatial-parameters
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step))
           (and (rationalp (lw-mellin-signal-spatial-slope cap)) (<= 0 (lw-mellin-signal-spatial-slope cap))
                (rationalp (lw-mellin-signal-spatial-cap cap)) (<= 2 (lw-mellin-signal-spatial-cap cap))
                (rationalp (lw-mellin-spatial-slope cap sigma height step))
                (<= 0 (lw-mellin-spatial-slope cap sigma height step))
                (rationalp (lw-mellin-spatial-error-factor cap step))
                (<= 1 (lw-mellin-spatial-error-factor cap step))))
  :hints (("Goal" :use (lw-mellin-signal-spatial-parameters lw-kernel-spatial-parameters)
                  :nonlinearp t)))

(defthm lw-mellin-component-error-at-most-request
  (implies (and (rationalp error) (< 0 error) (rationalp factor) (<= 0 factor))
           (<= (lw-mellin-component-error error factor) error))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator error) (divisor (* 3 (+ 1 factor))) (bound error)))
                  :in-theory (enable lw-mellin-component-error) :nonlinearp t)))

(defthm lw-mellin-component-errors-small
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (<= (lw-mellin-signal-error value sigma index step error) error)
                (<= (lw-mellin-kernel-error value error) error)
                (<= (lw-mellin-phase-error value sigma index step error) error)))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid
                        (:instance lw-mellin-component-error-at-most-request (factor (lw-mellin-signal-cap value)))
                        (:instance lw-mellin-component-error-at-most-request (factor (lw-mellin-kernel-cap value sigma index step)))
                        (:instance lw-mellin-component-error-at-most-request
                          (factor (* (lw-mellin-signal-cap value) (lw-mellin-kernel-cap value sigma index step)))))
                  :in-theory (e/d (lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error)
                                  (lw-mellin-component-error-at-most-request)) :nonlinearp t)))

(defthm lw-mellin-signal-uniform-bound
  (implies (and (rationalp value) (rationalp cap) (<= 0 value) (<= value cap)
                (rationalp sigma) (<= 0 sigma) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error))
           (<= (abs (lw-mellin-signal value sigma index step error)) (lw-mellin-signal-spatial-cap cap)))
  :hints (("Goal"
           :use (lw-mellin-error-budgets
                 (:instance lw-mellin-spatial-parameters (height 0))
                 (:instance lw-log-signal-lower-spatial-bound
                   (left value) (right 0) (left-error (lw-mellin-signal-error value sigma index step error)) (right-error 1))
                 (:instance lw-log-signal-bounds-valid (error (lw-mellin-signal-error value sigma index step error)))
                 (:instance lw-log-signal-bounds-valid (value 0) (error 1))
                 (:instance lw-mc-anchor-bound
                   (x (lw-mellin-signal value sigma index step error)) (a (car (lw-log-signal-bounds 0 1)))
                   (r (+ (* (lw-mellin-signal-spatial-slope cap) value) 2))))
           :in-theory (enable lw-mellin-signal lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope)
           :nonlinearp t)))

(defthm lw-mellin-weight-uniform-bound
  (implies (and (rationalp value) (rationalp cap) (<= 0 value) (<= value cap)
                (rationalp sigma) (<= 0 sigma) (rationalp step) (<= 0 step) (natp index)
                (rationalp error) (< 0 error))
           (and (<= 0 (lw-mellin-weight value sigma index step error))
                (<= (lw-mellin-weight value sigma index step error) (lw-kernel-spatial-cap cap step))))
  :hints (("Goal" :use ((:instance lw-kernel-weight-bounds-valid (error (lw-mellin-kernel-error value error)))
                        lw-kernel-weight-scale-spatial-cap)
                  :in-theory (enable lw-mellin-weight))))

(defthm lw-mellin-components-spatial-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (and
            (<= (abs (- (lw-mellin-signal left sigma index step left-error)
                        (lw-mellin-signal right sigma index step right-error)))
                (+ (* (lw-mellin-signal-spatial-slope cap) (abs (- left right)))
                   (lw-mellin-signal-error left sigma index step left-error)
                   (lw-mellin-signal-error right sigma index step right-error)))
            (<= (abs (- (lw-mellin-weight left sigma index step left-error)
                        (lw-mellin-weight right sigma index step right-error)))
                (+ (* (lw-kernel-spatial-slope cap sigma step) (abs (- left right)))
                   (lw-mellin-kernel-error left left-error) (lw-mellin-kernel-error right right-error)))
            (lw-complex-diskp
             (lw-complex-sub (lw-mellin-phase left sigma height index step left-error)
                             (lw-mellin-phase right sigma height index step right-error))
             (+ (* (abs height) (abs (- left right)))
                (lw-mellin-phase-error left sigma index step left-error)
                (lw-mellin-phase-error right sigma index step right-error)))))
  :hints (("Goal"
           :use ((:instance lw-mellin-error-budgets (value left) (error left-error))
                 (:instance lw-mellin-error-budgets (value right) (error right-error))
                 (:instance lw-log-signal-lower-spatial-bound
                   (left-error (lw-mellin-signal-error left sigma index step left-error))
                   (right-error (lw-mellin-signal-error right sigma index step right-error)))
                 (:instance lw-kernel-weight-lower-spatial-bound
                   (left-error (lw-mellin-kernel-error left left-error)) (right-error (lw-mellin-kernel-error right right-error)))
                 (:instance lw-phase-value-transport (left (- (* height left))) (right (- (* height right)))
                   (left-error (lw-mellin-phase-error left sigma index step left-error))
                   (right-error (lw-mellin-phase-error right sigma index step right-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-phase left sigma height index step left-error)
                                          (lw-mellin-phase right sigma height index step right-error)))
                   (radius (+ (* (abs height) (abs (- left right)))
                              (/ (lw-mellin-phase-error left sigma index step left-error) 2)
                              (/ (lw-mellin-phase-error right sigma index step right-error) 2)))
                   (cap (+ (* (abs height) (abs (- left right)))
                           (lw-mellin-phase-error left sigma index step left-error)
                           (lw-mellin-phase-error right sigma index step right-error)))))
           :in-theory (enable lw-mellin-signal lw-mellin-weight lw-mellin-phase lw-mellin-signal-spatial-slope)
           :nonlinearp t)))

(defun lw-mellin-spatial-pair-error (left right cap sigma height index step left-error right-error)
  (+ (* (lw-kernel-spatial-cap cap step)
        (+ (* (lw-mellin-signal-spatial-slope cap) (abs (- left right)))
           (lw-mellin-signal-error left sigma index step left-error)
           (lw-mellin-signal-error right sigma index step right-error)))
     (* (lw-mellin-signal-spatial-cap cap)
        (+ (* (lw-kernel-spatial-slope cap sigma step) (abs (- left right)))
           (lw-mellin-kernel-error left left-error) (lw-mellin-kernel-error right right-error)))
     (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-cap cap step)
        (+ (* (abs height) (abs (- left right)))
           (lw-mellin-phase-error left sigma index step left-error)
           (lw-mellin-phase-error right sigma index step right-error)))))

(local (in-theory (disable lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                           lw-mellin-spatial-parameters lw-mellin-components-spatial-transport
                           lw-mellin-signal-uniform-bound lw-mellin-weight-uniform-bound)))

(defthm lw-mellin-sample-spatial-pair-bound
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample left sigma height index step left-error)
                            (lw-mellin-sample right sigma height index step right-error))
            (lw-mellin-spatial-pair-error left right cap sigma height index step left-error right-error)))
  :hints (("Goal"
           :use (lw-mellin-spatial-parameters lw-kernel-spatial-parameters
                 lw-mellin-components-spatial-transport
                 (:instance lw-mellin-error-budgets (value left) (error left-error))
                 (:instance lw-mellin-error-budgets (value right) (error right-error))
                 (:instance lw-mellin-signal-bounded (value left) (error left-error))
                 (:instance lw-mellin-signal-bounded (value right) (error right-error))
                 (:instance lw-mellin-weight-bounded (value left) (error left-error))
                 (:instance lw-mellin-weight-bounded (value right) (error right-error))
                 (:instance lw-mellin-signal-uniform-bound (value right) (error right-error))
                 (:instance lw-mellin-weight-uniform-bound (value left) (error left-error))
                 (:instance lw-mellin-weight-uniform-bound (value right) (error right-error))
                 (:instance lw-mellin-product-difference
                   (g1 (lw-mellin-signal left sigma index step left-error))
                   (g2 (lw-mellin-signal right sigma index step right-error))
                   (w1 (lw-mellin-weight left sigma index step left-error))
                   (w2 (lw-mellin-weight right sigma index step right-error))
                   (m (lw-mellin-signal-spatial-cap cap)) (k (lw-kernel-spatial-cap cap step))
                   (g-error (+ (* (lw-mellin-signal-spatial-slope cap) (abs (- left right)))
                               (lw-mellin-signal-error left sigma index step left-error)
                               (lw-mellin-signal-error right sigma index step right-error)))
                   (w-error (+ (* (lw-kernel-spatial-slope cap sigma step) (abs (- left right)))
                               (lw-mellin-kernel-error left left-error) (lw-mellin-kernel-error right right-error)))
                   (left (lw-mellin-phase left sigma height index step left-error))
                   (right (lw-mellin-phase right sigma height index step right-error))
                   (phase-error (+ (* (abs height) (abs (- left right)))
                                   (lw-mellin-phase-error left sigma index step left-error)
                                   (lw-mellin-phase-error right sigma index step right-error)))))
           :in-theory (enable lw-mellin-sample)
           :nonlinearp t)))

(local
 (defthm lw-mc-budget-scalar
   (implies (and (rationalp m) (<= 0 m) (rationalp k) (<= 0 k)
                 (rationalp lg) (rationalp lw) (rationalp h) (rationalp d)
                 (rationalp eg) (rationalp ew) (rationalp ep)
                 (rationalp error) (<= 0 error) (<= eg error) (<= ew error) (<= ep error))
            (<= (+ (* k (+ (* lg d) eg)) (* m (+ (* lw d) ew)) (* m k (+ (* h d) ep)))
                (+ (* (+ (* k lg) (* m lw) (* m k h)) d) (* (+ 1 k m (* m k)) error))))
   :hints (("Goal" :use ((:instance lw-mc-multiply-order (a eg) (b error) (c k))
                         (:instance lw-mc-multiply-order (a ew) (b error) (c m))
                         (:instance lw-mc-multiply-order (a ep) (b error) (c (* m k))))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-mellin-spatial-pair-error-budget
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (lw-mellin-spatial-pair-error left right cap sigma height index step left-error right-error)
               (+ (* (lw-mellin-spatial-slope cap sigma height step) (abs (- left right)))
                  (* (lw-mellin-spatial-error-factor cap step) (+ left-error right-error)))))
  :hints (("Goal"
           :use (lw-mellin-spatial-parameters lw-kernel-spatial-parameters
                 (:instance lw-mellin-component-errors-small (value left) (error left-error))
                 (:instance lw-mellin-component-errors-small (value right) (error right-error))
                 (:instance lw-mellin-error-budgets (value left) (error left-error))
                 (:instance lw-mellin-error-budgets (value right) (error right-error))
                 (:instance lw-mc-budget-scalar
                   (m (lw-mellin-signal-spatial-cap cap)) (k (lw-kernel-spatial-cap cap step))
                   (lg (lw-mellin-signal-spatial-slope cap)) (lw (lw-kernel-spatial-slope cap sigma step))
                   (h (abs height)) (d (abs (- left right)))
                   (eg (+ (lw-mellin-signal-error left sigma index step left-error)
                          (lw-mellin-signal-error right sigma index step right-error)))
                   (ew (+ (lw-mellin-kernel-error left left-error) (lw-mellin-kernel-error right right-error)))
                   (ep (+ (lw-mellin-phase-error left sigma index step left-error)
                          (lw-mellin-phase-error right sigma index step right-error)))
                   (error (+ left-error right-error))))
           :in-theory (e/d (lw-mellin-spatial-slope lw-mellin-spatial-error-factor)
                           (lw-mellin-component-errors-small)))))

(defthm lw-mellin-sample-spatial-transport
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample left sigma height index step left-error)
                            (lw-mellin-sample right sigma height index step right-error))
            (+ (* (lw-mellin-spatial-slope cap sigma height step) (abs (- left right)))
               (* (lw-mellin-spatial-error-factor cap step) (+ left-error right-error)))))
  :hints (("Goal" :use (lw-mellin-spatial-parameters lw-mellin-sample-spatial-pair-bound
                        lw-mellin-spatial-pair-error-budget
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-mellin-sample left sigma height index step left-error)
                                                (lw-mellin-sample right sigma height index step right-error)))
                          (radius (lw-mellin-spatial-pair-error left right cap sigma height index step left-error right-error))
                          (cap (+ (* (lw-mellin-spatial-slope cap sigma height step) (abs (- left right)))
                                  (* (lw-mellin-spatial-error-factor cap step) (+ left-error right-error))))))
                  :in-theory (disable lw-mellin-spatial-pair-error lw-mellin-sample-spatial-pair-bound
                                      lw-mellin-spatial-pair-error-budget))))

(defun lw-mellin-spatial-modulus (cap sigma height step error)
  (/ error (* 4 (+ 1 (lw-mellin-spatial-slope cap sigma height step) (lw-mellin-spatial-error-factor cap step)))))

(defthm lw-mellin-spatial-modulus-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-spatial-modulus cap sigma height step error))
                (< 0 (lw-mellin-spatial-modulus cap sigma height step error))
                (<= (* (+ (lw-mellin-spatial-slope cap sigma height step)
                          (* 2 (lw-mellin-spatial-error-factor cap step)))
                       (lw-mellin-spatial-modulus cap sigma height step error)) error)))
  :hints (("Goal" :use (lw-mellin-spatial-parameters
                        (:instance lw-positive-division-bound
                          (numerator (* (+ (lw-mellin-spatial-slope cap sigma height step)
                                           (* 2 (lw-mellin-spatial-error-factor cap step))) error))
                          (divisor (* 4 (+ 1 (lw-mellin-spatial-slope cap sigma height step)
                                           (lw-mellin-spatial-error-factor cap step)))) (bound error)))
                  :nonlinearp t)))

(defthm lw-mellin-sample-computed-spatial-modulus
  (implies (and (rationalp left) (rationalp right) (rationalp cap)
                (<= 0 left) (<= 0 right) (<= left cap) (<= right cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp step) (<= 0 step) (natp index)
                (rationalp error) (< 0 error)
                (rationalp left-error) (< 0 left-error)
                (<= left-error (lw-mellin-spatial-modulus cap sigma height step error))
                (rationalp right-error) (< 0 right-error)
                (<= right-error (lw-mellin-spatial-modulus cap sigma height step error))
                (<= (abs (- left right)) (lw-mellin-spatial-modulus cap sigma height step error)))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample left sigma height index step left-error)
                            (lw-mellin-sample right sigma height index step right-error)) error))
  :hints (("Goal" :use (lw-mellin-spatial-parameters lw-mellin-spatial-modulus-valid
                        lw-mellin-sample-spatial-transport
                        (:instance lw-mc-multiply-order
                          (a (abs (- left right))) (b (lw-mellin-spatial-modulus cap sigma height step error))
                          (c (lw-mellin-spatial-slope cap sigma height step)))
                        (:instance lw-mc-multiply-order
                          (a (+ left-error right-error)) (b (* 2 (lw-mellin-spatial-modulus cap sigma height step error)))
                          (c (lw-mellin-spatial-error-factor cap step)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-mellin-sample left sigma height index step left-error)
                                                (lw-mellin-sample right sigma height index step right-error)))
                          (radius (+ (* (lw-mellin-spatial-slope cap sigma height step) (abs (- left right)))
                                     (* (lw-mellin-spatial-error-factor cap step) (+ left-error right-error)))) (cap error)))
                  :in-theory (disable lw-mellin-spatial-modulus lw-mellin-spatial-modulus-valid
                                      lw-mellin-sample-spatial-transport)
                  :nonlinearp t)))
