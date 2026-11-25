(in-package "ACL2")

(include-book "log-signal")
(include-book "kernel-bounds")
(include-book "phase-bounds")

(local (defthm lw-mi-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mi-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mi-sum-left-distribute
         (implies (and (rationalp left) (rationalp right) (rationalp factor))
                  (equal (* (+ left right) factor) (+ (* left factor) (* right factor))))
         :hints (("Goal" :use ((:instance distributivity (x factor) (y left) (z right)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mi-zero-product (equal (* 0 value) 0)))
(local (defthm lw-mi-minus-one-product
         (implies (rationalp value) (equal (* -1 value) (- value)))))
(local (defthm lw-mi-add-cancel
         (implies (and (rationalp value) (rationalp rest))
                  (equal (+ value (- value) rest) rest))))

(local (in-theory
        (disable lw-log-signal-bounds lw-log-signal-bounds-valid lw-log-signal-bounds-width
                 lw-log-signal-bounds-overlap lw-log-signal-lower-cauchy
                 lw-kernel-weight-bounds lw-kernel-weight-bounds-valid lw-kernel-weight-bounds-width
                 lw-kernel-weight-bounds-overlap lw-kernel-weight-lower-cauchy
                 lw-phase-value lw-phase-value-unit lw-phase-value-rational lw-phase-value-cauchy
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-add-disk lw-complex-scale-disk lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mi-abs-product
         (implies (and (rationalp left) (rationalp right))
                  (equal (abs (* left right)) (* (abs left) (abs right))))
         :hints (("Goal" :cases ((<= 0 left) (<= 0 right)) :nonlinearp t))))
(local (defthm lw-mi-abs-add
         (implies (and (rationalp left) (rationalp right))
                  (<= (abs (+ left right)) (+ (abs left) (abs right))))
         :rule-classes nil))
(local (defthm lw-mi-multiply-order
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

; Coarse caps are computed once per abscissa and weight, independently of
; the requested final precision. This prevents a circular precision choice.
(defun lw-mellin-signal-cap (value)
  (let ((bounds (lw-log-signal-bounds value 1)))
    (+ 1 (abs (car bounds)) (abs (cdr bounds)))))
(defun lw-mellin-kernel-cap (value sigma index step)
  (+ 1 (cdr (lw-kernel-weight-bounds value sigma index step 1))))

(defun lw-mellin-component-error (error factor) (/ error (* 3 (+ 1 factor))))
(defun lw-mellin-signal-error (value sigma index step error)
  (min 1 (lw-mellin-component-error error (lw-mellin-kernel-cap value sigma index step))))
(defun lw-mellin-kernel-error (value error)
  (lw-mellin-component-error error (lw-mellin-signal-cap value)))
(defun lw-mellin-phase-error (value sigma index step error)
  (lw-mellin-component-error error (* (lw-mellin-signal-cap value) (lw-mellin-kernel-cap value sigma index step))))

(defun lw-mellin-signal (value sigma index step error)
  (car (lw-log-signal-bounds value (lw-mellin-signal-error value sigma index step error))))
(defun lw-mellin-weight (value sigma index step error)
  (car (lw-kernel-weight-bounds value sigma index step (lw-mellin-kernel-error value error))))
(defun lw-mellin-phase (value sigma height index step error)
  (lw-phase-value (- (* height value)) (lw-mellin-phase-error value sigma index step error)))
(defun lw-mellin-sample (value sigma height index step error)
  (lw-complex-scale (* (lw-mellin-signal value sigma index step error)
                       (lw-mellin-weight value sigma index step error))
                    (lw-mellin-phase value sigma height index step error)))

(defthm lw-mellin-signal-cap-valid
  (implies (and (rationalp value) (<= 0 value))
           (and (rationalp (lw-mellin-signal-cap value)) (<= 1 (lw-mellin-signal-cap value))))
  :hints (("Goal" :use ((:instance lw-log-signal-bounds-valid (error 1))))))

(defthm lw-mellin-kernel-cap-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step))
           (and (rationalp (lw-mellin-kernel-cap value sigma index step))
                (<= 1 (lw-mellin-kernel-cap value sigma index step))))
  :hints (("Goal" :use ((:instance lw-kernel-weight-bounds-valid (error 1))))))

(defthm lw-mellin-component-error-valid
  (implies (and (rationalp error) (< 0 error) (rationalp factor) (<= 0 factor))
           (and (rationalp (lw-mellin-component-error error factor))
                (< 0 (lw-mellin-component-error error factor))
                (<= (* factor (lw-mellin-component-error error factor)) (/ error 3))))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* factor error)) (divisor (* 3 (+ 1 factor))) (bound (/ error 3))))
                  :nonlinearp t)))

(defthm lw-mellin-error-budgets
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-signal-error value sigma index step error))
                (< 0 (lw-mellin-signal-error value sigma index step error))
                (<= (lw-mellin-signal-error value sigma index step error) 1)
                (rationalp (lw-mellin-kernel-error value error)) (< 0 (lw-mellin-kernel-error value error))
                (rationalp (lw-mellin-phase-error value sigma index step error))
                (< 0 (lw-mellin-phase-error value sigma index step error))
                (<= (+ (* (lw-mellin-kernel-cap value sigma index step)
                           (lw-mellin-signal-error value sigma index step error))
                        (* (lw-mellin-signal-cap value) (lw-mellin-kernel-error value error))
                        (* (lw-mellin-signal-cap value) (lw-mellin-kernel-cap value sigma index step)
                           (lw-mellin-phase-error value sigma index step error))) error)))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid
                        (:instance lw-mellin-component-error-valid (factor (lw-mellin-signal-cap value)))
                        (:instance lw-mellin-component-error-valid (factor (lw-mellin-kernel-cap value sigma index step)))
                        (:instance lw-mellin-component-error-valid
                          (factor (* (lw-mellin-signal-cap value) (lw-mellin-kernel-cap value sigma index step)))))
                  :in-theory (disable lw-mellin-component-error lw-mellin-signal-cap lw-mellin-kernel-cap
                                      lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid lw-mellin-component-error-valid)
                  :nonlinearp t)))

(local
 (defthm lw-mi-interval-lower-cap
   (implies (and (lw-intervalp coarse) (lw-intervalp fine)
                 (<= (car coarse) (cdr fine)) (<= (car fine) (cdr coarse))
                 (<= (- (cdr fine) (car fine)) 1))
            (<= (abs (car fine)) (+ 1 (abs (car coarse)) (abs (cdr coarse)))))
   :rule-classes nil))

(defthm lw-mellin-signal-bounded
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-signal value sigma index step error))
                (<= (abs (lw-mellin-signal value sigma index step error)) (lw-mellin-signal-cap value))))
  :hints (("Goal"
           :use (lw-mellin-error-budgets
                 (:instance lw-log-signal-bounds-valid (error (lw-mellin-signal-error value sigma index step error)))
                 (:instance lw-log-signal-bounds-valid (error 1))
                 (:instance lw-log-signal-bounds-width (error (lw-mellin-signal-error value sigma index step error)))
                 (:instance lw-log-signal-bounds-overlap
                   (left-error (lw-mellin-signal-error value sigma index step error)) (right-error 1))
                 (:instance lw-log-signal-bounds-overlap
                   (left-error 1) (right-error (lw-mellin-signal-error value sigma index step error)))
                 (:instance lw-mi-interval-lower-cap (coarse (lw-log-signal-bounds value 1))
                   (fine (lw-log-signal-bounds value (lw-mellin-signal-error value sigma index step error)))))
           :in-theory (disable lw-mellin-signal-error lw-mellin-error-budgets))))

(defthm lw-mellin-weight-bounded
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-weight value sigma index step error))
                (<= 0 (lw-mellin-weight value sigma index step error))
                (<= (lw-mellin-weight value sigma index step error) (lw-mellin-kernel-cap value sigma index step))))
  :hints (("Goal"
           :use (lw-mellin-error-budgets
                 (:instance lw-kernel-weight-bounds-valid (error (lw-mellin-kernel-error value error)))
                 (:instance lw-kernel-weight-bounds-valid (error 1))
                 (:instance lw-kernel-weight-bounds-overlap
                   (left-error (lw-mellin-kernel-error value error)) (right-error 1)))
           :in-theory (disable lw-mellin-kernel-error lw-mellin-error-budgets))))

(local
 (defthm lw-mi-product-difference-identity
   (implies (and (rationalp g1) (rationalp g2) (rationalp w1) (rationalp w2))
            (equal (- (* g1 w1) (* g2 w2)) (+ (* (- g1 g2) w1) (* g2 (- w1 w2)))))
   :rule-classes nil))

(local
 (defthm lw-mi-product-difference-bound
   (implies (and (rationalp g1) (rationalp g2) (rationalp w1) (rationalp w2)
                 (rationalp g-error) (<= 0 g-error) (rationalp w-error) (<= 0 w-error)
                 (rationalp m) (<= 0 m) (rationalp k) (<= 0 k)
                 (<= (abs (- g1 g2)) g-error) (<= (abs (- w1 w2)) w-error)
                 (<= (abs g2) m) (<= 0 w1) (<= w1 k))
            (<= (abs (- (* g1 w1) (* g2 w2))) (+ (* k g-error) (* m w-error))))
   :hints (("Goal"
            :use (lw-mi-product-difference-identity
                  (:instance lw-mi-abs-add (left (* (- g1 g2) w1)) (right (* g2 (- w1 w2))))
                  (:instance lw-mi-multiply-order (left (abs (- g1 g2))) (right g-error) (factor w1))
                  (:instance lw-mi-multiply-order (left w1) (right k) (factor g-error))
                  (:instance lw-mi-multiply-order (left (abs g2)) (right m) (factor (abs (- w1 w2))))
                  (:instance lw-mi-multiply-order (left (abs (- w1 w2))) (right w-error) (factor m)))
            :in-theory (disable distributivity lw-mi-sum-left-distribute)))
   :rule-classes nil))

(local
 (defthm lw-mi-scale-difference-identity
   (implies (and (lw-complexp left) (lw-complexp right) (rationalp h1) (rationalp h2))
            (equal (lw-complex-sub (lw-complex-scale h1 left) (lw-complex-scale h2 right))
                   (lw-complex-add (lw-complex-scale (- h1 h2) left)
                                   (lw-complex-scale h2 (lw-complex-sub left right)))))
   :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-add lw-complex-scale)))
   :rule-classes nil))

(local
 (defthm lw-mi-scale-difference-bound
   (implies (and (lw-complex-diskp left 1) (lw-complex-diskp right 1)
                 (lw-complex-diskp (lw-complex-sub left right) phase-error)
                 (rationalp h1) (rationalp h2) (rationalp h-error) (<= 0 h-error)
                 (rationalp h-cap) (<= 0 h-cap) (<= (abs (- h1 h2)) h-error) (<= (abs h2) h-cap))
            (lw-complex-diskp (lw-complex-sub (lw-complex-scale h1 left) (lw-complex-scale h2 right))
                              (+ h-error (* h-cap phase-error))))
   :hints (("Goal"
            :use (lw-mi-scale-difference-identity
                  (:instance lw-complex-disk-data (point left) (radius 1))
                  (:instance lw-complex-disk-data (point right) (radius 1))
                  (:instance lw-complex-disk-data (point (lw-complex-sub left right)) (radius phase-error))
                  (:instance lw-complex-scale-disk (point left) (radius 1) (factor (- h1 h2)))
                  (:instance lw-complex-scale-disk (point (lw-complex-sub left right)) (radius phase-error) (factor h2))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale (- h1 h2) left))
                    (radius (abs (- h1 h2))) (cap h-error))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-scale h2 (lw-complex-sub left right)))
                    (radius (* (abs h2) phase-error)) (cap (* h-cap phase-error)))
                  (:instance lw-mi-multiply-order (left (abs h2)) (right h-cap) (factor phase-error))
                  (:instance lw-complex-add-disk
                    (left (lw-complex-scale (- h1 h2) left)) (right (lw-complex-scale h2 (lw-complex-sub left right)))
                    (radius h-error) (other-radius (* h-cap phase-error))))
            :in-theory (disable lw-complex-disk-data)))
   :rule-classes nil))

(defthm lw-mellin-product-difference
  (implies (and (rationalp g1) (rationalp g2) (rationalp w1) (rationalp w2)
                (rationalp m) (<= 0 m) (rationalp k) (<= 0 k)
                (rationalp g-error) (<= 0 g-error) (rationalp w-error) (<= 0 w-error)
                (<= (abs (- g1 g2)) g-error) (<= (abs (- w1 w2)) w-error)
                (<= (abs g2) m) (<= 0 w1) (<= w1 k) (<= 0 w2) (<= w2 k)
                (lw-complex-diskp left 1) (lw-complex-diskp right 1)
                (lw-complex-diskp (lw-complex-sub left right) phase-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-scale (* g1 w1) left) (lw-complex-scale (* g2 w2) right))
            (+ (* k g-error) (* m w-error) (* m k phase-error))))
  :hints (("Goal"
           :use (lw-mi-product-difference-bound
                 (:instance lw-mi-multiply-order (left (abs g2)) (right m) (factor w2))
                 (:instance lw-mi-multiply-order (left w2) (right k) (factor m))
                 (:instance lw-mi-scale-difference-bound (h1 (* g1 w1)) (h2 (* g2 w2))
                   (h-error (+ (* k g-error) (* m w-error))) (h-cap (* m k))))
           :nonlinearp t)))

(local (in-theory (disable lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                           lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error)))

(defthm lw-mellin-phase-unit
  (implies (and (rationalp value) (rationalp height))
           (lw-complex-diskp (lw-mellin-phase value sigma height index step error) 1))
  :hints (("Goal" :use ((:instance lw-phase-value-unit
                          (value (- (* height value))) (error (lw-mellin-phase-error value sigma index step error)))))))

(defthm lw-mellin-phase-rational
  (implies (and (rationalp value) (rationalp height))
           (lw-complexp (lw-mellin-phase value sigma height index step error)))
  :hints (("Goal" :use ((:instance lw-phase-value-rational
                          (value (- (* height value))) (error (lw-mellin-phase-error value sigma index step error)))))))

(defthm lw-mellin-sample-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-sample value sigma height index step error)))
  :hints (("Goal" :use (lw-mellin-signal-bounded lw-mellin-weight-bounded lw-mellin-phase-rational)
                  :in-theory (e/d (lw-complexp lw-complex-scale)
                                  (lw-mellin-signal lw-mellin-weight lw-mellin-phase
                                   lw-mellin-signal-bounded lw-mellin-weight-bounded lw-mellin-phase-rational)))))

; These are rational endpoint/budget checks, not an assumed analytic
; coefficient estimate. The next theorem proves every one for the constructor.
(defun lw-mellin-sample-check (value sigma index step error)
  (let* ((m (lw-mellin-signal-cap value)) (k (lw-mellin-kernel-cap value sigma index step))
         (ge (lw-mellin-signal-error value sigma index step error))
         (we (lw-mellin-kernel-error value error)) (pe (lw-mellin-phase-error value sigma index step error)))
    (and (<= 1 m) (<= 1 k) (< 0 ge) (<= ge 1) (< 0 we) (< 0 pe)
         (<= (lw-interval-width (lw-log-signal-bounds value ge)) ge)
         (<= (- (cdr (lw-kernel-weight-bounds value sigma index step we))
                (car (lw-kernel-weight-bounds value sigma index step we))) we)
         (<= (abs (lw-mellin-signal value sigma index step error)) m)
         (<= 0 (lw-mellin-weight value sigma index step error))
         (<= (lw-mellin-weight value sigma index step error) k)
         (<= (+ (* k ge) (* m we) (* m k pe)) error))))

(defthm lw-mellin-sample-check-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (lw-mellin-sample-check value sigma index step error))
  :hints (("Goal"
           :use (lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid lw-mellin-error-budgets
                 lw-mellin-signal-bounded lw-mellin-weight-bounded
                 (:instance lw-log-signal-bounds-width (error (lw-mellin-signal-error value sigma index step error)))
                 (:instance lw-kernel-weight-bounds-width (error (lw-mellin-kernel-error value error))))
           :in-theory (disable lw-mellin-signal lw-mellin-weight lw-mellin-signal-cap-valid
                               lw-mellin-kernel-cap-valid lw-mellin-error-budgets
                               lw-mellin-signal-bounded lw-mellin-weight-bounded))))

(defthm lw-mellin-components-cauchy
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (and (<= (abs (- (lw-mellin-signal value sigma index step left-error)
                           (lw-mellin-signal value sigma index step right-error)))
                    (+ (lw-mellin-signal-error value sigma index step left-error)
                       (lw-mellin-signal-error value sigma index step right-error)))
                (<= (abs (- (lw-mellin-weight value sigma index step left-error)
                            (lw-mellin-weight value sigma index step right-error)))
                    (+ (lw-mellin-kernel-error value left-error) (lw-mellin-kernel-error value right-error)))
                (lw-complex-diskp
                 (lw-complex-sub (lw-mellin-phase value sigma height index step left-error)
                                 (lw-mellin-phase value sigma height index step right-error))
                 (+ (lw-mellin-phase-error value sigma index step left-error)
                    (lw-mellin-phase-error value sigma index step right-error)))))
  :hints (("Goal"
           :use ((:instance lw-mellin-error-budgets (error left-error))
                 (:instance lw-mellin-error-budgets (error right-error))
                 (:instance lw-log-signal-lower-cauchy
                   (left-error (lw-mellin-signal-error value sigma index step left-error))
                   (right-error (lw-mellin-signal-error value sigma index step right-error)))
                 (:instance lw-kernel-weight-lower-cauchy
                   (left-error (lw-mellin-kernel-error value left-error)) (right-error (lw-mellin-kernel-error value right-error)))
                 (:instance lw-phase-value-cauchy (value (- (* height value)))
                   (left-error (lw-mellin-phase-error value sigma index step left-error))
                   (right-error (lw-mellin-phase-error value sigma index step right-error))))
           :in-theory (disable lw-mellin-error-budgets))))

(defun lw-mellin-pair-error (value sigma index step left-error right-error)
  (+ (* (lw-mellin-kernel-cap value sigma index step)
        (+ (lw-mellin-signal-error value sigma index step left-error) (lw-mellin-signal-error value sigma index step right-error)))
     (* (lw-mellin-signal-cap value) (+ (lw-mellin-kernel-error value left-error) (lw-mellin-kernel-error value right-error)))
     (* (lw-mellin-signal-cap value) (lw-mellin-kernel-cap value sigma index step)
        (+ (lw-mellin-phase-error value sigma index step left-error) (lw-mellin-phase-error value sigma index step right-error)))))

(defthm lw-mellin-pair-error-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (and (rationalp (lw-mellin-pair-error value sigma index step left-error right-error))
                (<= (lw-mellin-pair-error value sigma index step left-error right-error) (+ left-error right-error))))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid
                        (:instance lw-mellin-error-budgets (error left-error))
                        (:instance lw-mellin-error-budgets (error right-error)))
                  :in-theory (disable lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid lw-mellin-error-budgets))))

(defthm lw-mellin-sample-cauchy
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample value sigma height index step left-error)
                            (lw-mellin-sample value sigma height index step right-error))
            (+ left-error right-error)))
  :hints (("Goal"
           :use (lw-mellin-pair-error-budget lw-mellin-components-cauchy
                 lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid
                 (:instance lw-mellin-signal-bounded (error left-error))
                 (:instance lw-mellin-signal-bounded (error right-error))
                 (:instance lw-mellin-weight-bounded (error left-error))
                 (:instance lw-mellin-weight-bounded (error right-error))
                 (:instance lw-mellin-error-budgets (error left-error))
                 (:instance lw-mellin-error-budgets (error right-error))
                 (:instance lw-mellin-phase-unit (error left-error))
                 (:instance lw-mellin-phase-unit (error right-error))
                 (:instance lw-mellin-product-difference
                   (g1 (lw-mellin-signal value sigma index step left-error)) (g2 (lw-mellin-signal value sigma index step right-error))
                   (w1 (lw-mellin-weight value sigma index step left-error)) (w2 (lw-mellin-weight value sigma index step right-error))
                   (m (lw-mellin-signal-cap value)) (k (lw-mellin-kernel-cap value sigma index step))
                   (left (lw-mellin-phase value sigma height index step left-error))
                   (right (lw-mellin-phase value sigma height index step right-error))
                   (g-error (+ (lw-mellin-signal-error value sigma index step left-error) (lw-mellin-signal-error value sigma index step right-error)))
                   (w-error (+ (lw-mellin-kernel-error value left-error) (lw-mellin-kernel-error value right-error)))
                   (phase-error (+ (lw-mellin-phase-error value sigma index step left-error) (lw-mellin-phase-error value sigma index step right-error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-sample value sigma height index step left-error)
                                          (lw-mellin-sample value sigma height index step right-error)))
                   (radius (lw-mellin-pair-error value sigma index step left-error right-error)) (cap (+ left-error right-error))))
           :in-theory (disable lw-mellin-signal lw-mellin-weight lw-mellin-phase lw-mellin-pair-error-budget
                               lw-mellin-components-cauchy lw-mellin-signal-cap-valid lw-mellin-kernel-cap-valid
                               lw-mellin-signal-bounded lw-mellin-weight-bounded lw-mellin-error-budgets
                               lw-mellin-phase-unit lw-mellin-product-difference))))

(assert-event
 (lw-complex-diskp
  (lw-complex-sub (lw-complex-scale -6 (cons 3/5 4/5)) (lw-complex-scale 4 (cons 0 1)))
  (+ (* 3 4) (* 2 1) (* 2 3 1))))
