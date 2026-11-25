(in-package "ACL2")

(include-book "mellin-dyadic-cells")
(include-book "mellin-shift-bounds")

; One computed mesh controls every abscissa and height in a checked
; rectangle, hence every complex shift in the prescribed disk.

(local (in-theory
        (disable lw-exp-bounds lw-exp-sum lw-exp-term lw-exp-index lw-exp-band lw-exp-lipschitz-cap
                 lw-kernel-spatial-cap lw-kernel-spatial-slope lw-mellin-spatial-slope
                 lw-mellin-spatial-error-factor lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope
                 lw-log-signal-bounds lw-mellin-sample lw-mellin-sample-kernel-form
                 lw-mellin-bounded-integral lw-mellin-sum lw-mellin-sum-raw
                 lw-mellin-dyadic-cells lw-halved-width lw-halving-depth lw-precision-fuel
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mum-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mum-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mum-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mum-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mum-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-exp-lipschitz-cap-transport
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= left right))
           (<= (lw-exp-lipschitz-cap left) (+ 1 (lw-exp-lipschitz-cap right))))
  :hints (("Goal" :use ((:instance lw-exp-bounds-monotone-overlap (left-error 1) (right-error 1))
                        (:instance lw-exp-bounds-width (value left) (epsilon 1)))
                  :in-theory (e/d (lw-exp-lipschitz-cap)
                                  (lw-exp-bounds-monotone-overlap lw-exp-bounds-width)))))

(defun lw-kernel-uniform-slope (cap sigma-max step)
  (* (lw-kernel-spatial-cap cap step)
     (+ 1 (* sigma-max (+ 1 (lw-exp-lipschitz-cap (* sigma-max cap)))))))

(defthm lw-kernel-uniform-slope-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma-max) (<= 0 sigma-max)
                (rationalp step) (<= 0 step))
           (and (rationalp (lw-kernel-uniform-slope cap sigma-max step))
                (<= 0 (lw-kernel-uniform-slope cap sigma-max step))))
  :hints (("Goal" :use ((:instance lw-kernel-spatial-parameters (sigma sigma-max))
                        (:instance lw-mum-product-nonnegative (a sigma-max) (b cap))
                        (:instance lw-exp-lipschitz-cap-valid (cap (* sigma-max cap)))
                        (:instance lw-mum-product-nonnegative
                          (a (lw-kernel-spatial-cap cap step))
                          (b (+ 1 (* sigma-max (+ 1 (lw-exp-lipschitz-cap (* sigma-max cap))))))))
                  :in-theory (disable lw-kernel-spatial-parameters lw-exp-lipschitz-cap-valid)
                  :nonlinearp t)))

(defthm lw-kernel-spatial-slope-uniform
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp sigma-max) (<= sigma sigma-max) (rationalp step) (<= 0 step))
           (<= (lw-kernel-spatial-slope cap sigma step)
               (lw-kernel-uniform-slope cap sigma-max step)))
  :hints (("Goal" :use (
    lw-kernel-spatial-parameters
    (:instance lw-mum-product-nonnegative (a sigma) (b cap))
    (:instance lw-mum-product-nonnegative (a sigma-max) (b cap))
    (:instance lw-mum-multiply-order (a sigma) (b sigma-max) (factor cap))
    (:instance lw-exp-lipschitz-cap-transport (left (* sigma cap)) (right (* sigma-max cap)))
    (:instance lw-exp-lipschitz-cap-valid (cap (* sigma cap)))
    (:instance lw-exp-lipschitz-cap-valid (cap (* sigma-max cap)))
    (:instance lw-mum-multiply-order
      (a (lw-exp-lipschitz-cap (* sigma cap))) (b (+ 1 (lw-exp-lipschitz-cap (* sigma-max cap)))) (factor sigma))
    (:instance lw-mum-multiply-order (a sigma) (b sigma-max)
      (factor (+ 1 (lw-exp-lipschitz-cap (* sigma-max cap)))))
    (:instance lw-mum-multiply-order
      (a (+ 1 (* sigma (lw-exp-lipschitz-cap (* sigma cap)))))
      (b (+ 1 (* sigma-max (+ 1 (lw-exp-lipschitz-cap (* sigma-max cap))))))
      (factor (lw-kernel-spatial-cap cap step))))
    :in-theory (e/d (lw-kernel-spatial-slope lw-kernel-uniform-slope)
                    (lw-kernel-spatial-parameters lw-exp-lipschitz-cap-transport lw-exp-lipschitz-cap-valid)))))

(local (in-theory (disable lw-kernel-uniform-slope)))

(defun lw-mellin-uniform-spatial-slope (cap sigma-max height-max)
  (+ (* (lw-kernel-spatial-cap cap 1) (lw-mellin-signal-spatial-slope cap))
     (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-uniform-slope cap sigma-max 1))
     (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-cap cap 1) height-max)))

(defthm lw-mellin-uniform-spatial-slope-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma-max) (<= 0 sigma-max)
                (rationalp height-max) (<= 0 height-max))
           (and (rationalp (lw-mellin-uniform-spatial-slope cap sigma-max height-max))
                (<= 0 (lw-mellin-uniform-spatial-slope cap sigma-max height-max))))
  :hints (("Goal" :use (
    lw-mellin-signal-spatial-parameters
    (:instance lw-kernel-spatial-parameters (sigma sigma-max) (step 1))
    (:instance lw-kernel-uniform-slope-valid (step 1))
    (:instance lw-mum-product-nonnegative
      (a (lw-kernel-spatial-cap cap 1)) (b (lw-mellin-signal-spatial-slope cap)))
    (:instance lw-mum-product-nonnegative
      (a (lw-mellin-signal-spatial-cap cap)) (b (lw-kernel-uniform-slope cap sigma-max 1)))
    (:instance lw-mum-product-nonnegative
      (a (lw-mellin-signal-spatial-cap cap)) (b (lw-kernel-spatial-cap cap 1)))
    (:instance lw-mum-product-nonnegative
      (a (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-cap cap 1))) (b height-max)))
    :in-theory (disable lw-mellin-signal-spatial-parameters lw-kernel-spatial-parameters
                        lw-kernel-uniform-slope-valid))))

(defthm lw-mellin-spatial-slope-uniform
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp sigma-max) (<= sigma sigma-max)
                (rationalp height) (rationalp height-max) (<= (abs height) height-max))
           (<= (lw-mellin-spatial-slope cap sigma height 1)
               (lw-mellin-uniform-spatial-slope cap sigma-max height-max)))
  :hints (("Goal" :use (
    lw-mellin-signal-spatial-parameters
    (:instance lw-kernel-spatial-parameters (step 1))
    (:instance lw-kernel-spatial-slope-uniform (step 1))
    (:instance lw-mum-product-nonnegative
      (a (lw-mellin-signal-spatial-cap cap)) (b (lw-kernel-spatial-cap cap 1)))
    (:instance lw-mum-multiply-order
      (a (lw-kernel-spatial-slope cap sigma 1)) (b (lw-kernel-uniform-slope cap sigma-max 1))
      (factor (lw-mellin-signal-spatial-cap cap)))
    (:instance lw-mum-multiply-order (a (abs height)) (b height-max)
      (factor (* (lw-mellin-signal-spatial-cap cap) (lw-kernel-spatial-cap cap 1)))))
    :in-theory (e/d (lw-mellin-spatial-slope lw-mellin-uniform-spatial-slope)
                    (lw-mellin-signal-spatial-parameters lw-kernel-spatial-parameters
                     lw-kernel-spatial-slope-uniform)))))


(local (in-theory (disable lw-mellin-uniform-spatial-slope)))

(local (defthm lw-mum-mesh-data
         (implies (and (rationalp width) (<= 0 width) (natp depth))
                  (and (rationalp (lw-halved-width width depth)) (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))))
(local (defthm lw-mum-mesh-scale
         (implies (and (rationalp width) (rationalp factor))
                  (equal (lw-halved-width (* factor width) depth)
                         (* factor (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))
         :rule-classes nil))

(defun lw-mellin-uniform-depth (cap sigma-max height-max error)
  (let ((width (* cap cap (lw-mellin-uniform-spatial-slope cap sigma-max height-max))))
    (lw-halving-depth width (* 1/4 error) (lw-precision-fuel width (* 1/4 error)))))

(defthm lw-mellin-uniform-depth-adequate
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma-max) (<= 0 sigma-max)
                (rationalp height-max) (<= 0 height-max) (rationalp error) (< 0 error))
           (and (natp (lw-mellin-uniform-depth cap sigma-max height-max error))
                (<= (* cap (lw-mellin-uniform-spatial-slope cap sigma-max height-max)
                       (lw-halved-width cap (lw-mellin-uniform-depth cap sigma-max height-max error))) (* 1/4 error))))
  :hints (("Goal" :use (
    lw-mellin-uniform-spatial-slope-valid
    (:instance lw-mum-product-nonnegative (a cap) (b cap))
    (:instance lw-mum-product-nonnegative
      (a (* cap cap)) (b (lw-mellin-uniform-spatial-slope cap sigma-max height-max)))
    (:instance lw-precision-fuel-adequate
      (width (* cap cap (lw-mellin-uniform-spatial-slope cap sigma-max height-max))) (epsilon (* 1/4 error)))
    (:instance lw-halving-depth-adequate
      (width (* cap cap (lw-mellin-uniform-spatial-slope cap sigma-max height-max))) (epsilon (* 1/4 error))
      (fuel (lw-precision-fuel (* cap cap (lw-mellin-uniform-spatial-slope cap sigma-max height-max)) (* 1/4 error))))
    (:instance lw-mum-mesh-scale
      (width cap) (factor (* cap (lw-mellin-uniform-spatial-slope cap sigma-max height-max)))
      (depth (lw-mellin-uniform-depth cap sigma-max height-max error))))
    :in-theory (disable lw-mellin-uniform-spatial-slope-valid lw-precision-fuel-adequate lw-halving-depth-adequate))))

(local (in-theory (disable lw-mellin-uniform-depth)))

(local (defthm lw-mum-components
         (implies (lw-complexp point) (and (rationalp (car point)) (rationalp (cdr point))))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-mum-abs-subtract
         (implies (and (rationalp a) (rationalp b))
                  (<= (abs (- a b)) (+ (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b) (<= b a))))
         :rule-classes nil))

(defun lw-mellin-shift-mesh-depth (cap sigma height radius error)
  (lw-mellin-uniform-depth cap (+ sigma radius) (+ (abs height) radius) error))

(defthm lw-mellin-shift-mesh-data
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (lw-complex-diskp shift radius) (<= radius sigma) (rationalp error) (< 0 error))
           (and (rationalp (- sigma (car shift))) (<= 0 (- sigma (car shift)))
                (rationalp (- height (cdr shift))) (<= (abs (- height (cdr shift))) (+ (abs height) radius))
                (natp (lw-mellin-shift-mesh-depth cap sigma height radius error))
                (<= (* cap (lw-mellin-spatial-slope cap (- sigma (car shift)) (- height (cdr shift)) 1)
                       (lw-halved-width cap (lw-mellin-shift-mesh-depth cap sigma height radius error))) (* 1/4 error))))
  :hints (("Goal" :use (
    (:instance lw-complex-disk-coordinates (point shift))
    (:instance lw-mum-abs-subtract (a height) (b (cdr shift)))
    (:instance lw-mellin-uniform-depth-adequate (sigma-max (+ sigma radius)) (height-max (+ (abs height) radius)))
    (:instance lw-mellin-spatial-slope-uniform
      (sigma (- sigma (car shift))) (height (- height (cdr shift)))
      (sigma-max (+ sigma radius)) (height-max (+ (abs height) radius)))
    (:instance lw-mum-multiply-order
      (a (lw-mellin-spatial-slope cap (- sigma (car shift)) (- height (cdr shift)) 1))
      (b (lw-mellin-uniform-spatial-slope cap (+ sigma radius) (+ (abs height) radius)))
      (factor (* cap (lw-halved-width cap (lw-mellin-shift-mesh-depth cap sigma height radius error)))))
    (:instance lw-mum-product-nonnegative
      (a cap) (b (lw-halved-width cap (lw-mellin-shift-mesh-depth cap sigma height radius error)))))
    :in-theory (disable lw-complex-disk-coordinates lw-mellin-uniform-depth-adequate lw-mellin-spatial-slope-uniform)
    :cases ((<= 0 (car shift)) (<= 0 (cdr shift))))))

(local (in-theory (disable lw-mellin-shift-mesh-depth)))


(defthm lw-mellin-shift-cell-bounded-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp index) (lw-complex-diskp shift radius) (<= radius sigma)
                (rationalp grid-error) (< 0 grid-error) (rationalp mesh-error) (< 0 mesh-error)
                (rationalp bounded-error) (< 0 bounded-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sum
                 (lw-mellin-dyadic-cells
                   0
                   cap
                   (lw-mellin-shift-mesh-depth cap sigma height radius mesh-error))
                 (- sigma (car shift))
                 (- height (cdr shift))
                 index
                 grid-error)
               (lw-mellin-bounded-integral
                 cap
                 (- sigma (car shift))
                 (- height (cdr shift))
                 index
                 bounded-error))
             (+ grid-error (* 1/4 mesh-error) bounded-error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-shift-mesh-data (error mesh-error))
    (:instance lw-mellin-dyadic-cell-bounded-comparison
      (sigma (- sigma (car shift)))
      (height (- height (cdr shift)))
      (depth (lw-mellin-shift-mesh-depth cap sigma height radius mesh-error))
      (left-error grid-error)
      (right-error bounded-error))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sum
            (lw-mellin-dyadic-cells 0 cap (lw-mellin-shift-mesh-depth cap sigma height radius mesh-error))
            (- sigma (car shift))
            (- height (cdr shift))
            index
            grid-error)
          (lw-mellin-bounded-integral cap (- sigma (car shift)) (- height (cdr shift)) index bounded-error)))
      (radius
        (+
          grid-error
          (*
            cap
            (lw-mellin-spatial-slope cap (- sigma (car shift)) (- height (cdr shift)) 1)
            (lw-halved-width cap (lw-mellin-shift-mesh-depth cap sigma height radius mesh-error)))
          bounded-error))
      (cap (+ grid-error (* 1/4 mesh-error) bounded-error))))
    :in-theory (disable lw-mellin-shift-mesh-data lw-mellin-dyadic-cell-bounded-comparison))))

