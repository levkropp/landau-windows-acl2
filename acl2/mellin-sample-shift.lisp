(in-package "ACL2")

(include-book "mellin-shift-bounds")

; A single sample precision works throughout a checked shift disk.
; Keep the signal, the exact moment mass and all approximation errors.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-phase-value lw-log-signal-bounds
                 lw-mellin-sample lw-mellin-sample-kernel-form lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-kernel-weight-scale
                 lw-mellin-exponential-sample lw-mellin-exponential-sample-error
                 lw-mellin-exponential-error-factor lw-mellin-exponent lw-complex-exp-radius-cap
                 lw-mellin-shift-error-factor lw-mellin-shift-precision
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mss-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mss-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mss-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mss-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mss-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-mss-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mss-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mss-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mss-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-mss-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mss-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mss-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-mss-shared-right-identity
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp point))
                  (equal (lw-complex-sub (lw-complex-mul a point) (lw-complex-mul b point))
                         (lw-complex-mul (lw-complex-sub a b) point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-sub)))))
(local (defthm lw-mss-shared-right-bound
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complex-diskp point cap)
                       (lw-complex-diskp (lw-complex-sub a b) error))
                  (lw-complex-diskp (lw-complex-sub (lw-complex-mul a point) (lw-complex-mul b point))
                                    (* cap error)))
         :hints (("Goal" :use ((:instance lw-complex-mul-disk
                                 (left (lw-complex-sub a b)) (right point)
                                 (radius error) (other-radius cap)))
                         :in-theory (disable lw-complex-mul-disk)))
         :rule-classes nil))
(local (defthm lw-mss-scale-product-identity
         (implies (and (rationalp factor) (lw-complexp left) (lw-complexp right))
                  (equal (lw-complex-mul (lw-complex-scale factor left) right)
                         (lw-complex-scale factor (lw-complex-mul left right))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))))
(local (defthm lw-mss-same-factor-sub
         (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                         (lw-complex-scale factor (lw-complex-sub a b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))
(local (defthm lw-mss-same-point-sub
         (implies (and (rationalp a) (rationalp b) (lw-complexp point))
                  (equal (lw-complex-sub (lw-complex-scale a point) (lw-complex-scale b point))
                         (lw-complex-scale (- a b) point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))
(local (defthm lw-mss-scaled-product-error
         (implies (and (rationalp factor) (lw-complexp left) (lw-complexp right) (lw-complexp target)
                       (lw-complex-diskp (lw-complex-sub (lw-complex-mul left right) target) error))
                  (lw-complex-diskp
                   (lw-complex-sub (lw-complex-mul (lw-complex-scale factor left) right)
                                   (lw-complex-scale factor target)) (* (abs factor) error)))
         :hints (("Goal" :use ((:instance lw-complex-scale-disk
                                 (point (lw-complex-sub (lw-complex-mul left right) target))
                                 (radius error)))
                         :in-theory (disable lw-complex-scale-disk)))
         :rule-classes nil))

(defun lw-mellin-frozen-exponential (value base-sigma sigma height index step error)
  (lw-complex-scale
   (* (lw-mellin-signal value base-sigma index step error) (lw-kernel-weight-scale value index step))
   (lw-complex-exp-value (lw-mellin-exponent value sigma height) error)))

(defthm lw-mellin-frozen-exponential-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp base-sigma) (<= 0 base-sigma)
                (rationalp sigma) (rationalp height) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-frozen-exponential value base-sigma sigma height index step error)))
  :hints (("Goal" :use ((:instance lw-mellin-signal-bounded (sigma base-sigma)))
                  :in-theory (disable lw-mellin-signal-bounded))))

(local (in-theory (disable lw-mellin-frozen-exponential)))

(defthm lw-mellin-frozen-signal-comparison
  (implies (and (rationalp value) (<= 0 value)
                (rationalp base-sigma) (<= 0 base-sigma) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-frozen-exponential value base-sigma sigma height index step error)
                            (lw-mellin-exponential-sample value sigma height index step error error))
            (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-signal-bounded (sigma base-sigma))
    lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative
    (:instance lw-mellin-signals-abscissa-cauchy
      (left-sigma base-sigma) (right-sigma sigma) (left-error error) (right-error error))
    lw-mellin-exponential-value-cap
    (:instance lw-complex-scale-disk
      (factor (* (- (lw-mellin-signal value base-sigma index step error)
                    (lw-mellin-signal value sigma index step error)) (lw-kernel-weight-scale value index step)))
      (point (lw-complex-exp-value (lw-mellin-exponent value sigma height) error)) (radius (+ 1 error)))
    (:instance lw-mss-abs-product
      (a (- (lw-mellin-signal value base-sigma index step error)
            (lw-mellin-signal value sigma index step error)))
      (b (lw-kernel-weight-scale value index step)))
    (:instance lw-mss-multiply-order
      (a (abs (- (lw-mellin-signal value base-sigma index step error)
                 (lw-mellin-signal value sigma index step error))))
      (b (* 2 error)) (factor (* (lw-kernel-weight-scale value index step) (+ 1 error))))
    (:instance lw-complex-disk-enlarge
      (point (lw-complex-sub (lw-mellin-frozen-exponential value base-sigma sigma height index step error)
                            (lw-mellin-exponential-sample value sigma height index step error error)))
      (radius (* (abs (- (lw-mellin-signal value base-sigma index step error)
                         (lw-mellin-signal value sigma index step error)))
                 (lw-kernel-weight-scale value index step) (+ 1 error)))
      (cap (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error))))
    :in-theory (e/d (lw-mellin-frozen-exponential lw-mellin-exponential-sample lw-mellin-exponent)
                    (lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative
                     lw-mellin-signals-abscissa-cauchy lw-mellin-exponential-value-cap
                     lw-complex-scale-disk lw-mss-abs-product))
    :nonlinearp t)))


(local (defthm lw-mss-complex-components
         (implies (lw-complexp point) (and (rationalp (car point)) (rationalp (cdr point))))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-mss-scaled-addition-budget
         (implies (and (rationalp amplitude) (<= 0 amplitude) (rationalp signal-cap) (<= amplitude signal-cap)
                       (rationalp mass) (<= 0 mass)
                       (rationalp point-cap) (<= 0 point-cap) (rationalp shift-cap) (<= point-cap shift-cap)
                       (rationalp base-cap) (<= 0 base-cap) (rationalp error) (<= 0 error))
                  (<= (* amplitude mass (+ (* point-cap error) (* base-cap error) (* 2 error)))
                      (* signal-cap mass (+ shift-cap base-cap 2) error)))
         :hints (("Goal" :use (
           (:instance lw-mss-product-nonnegative (a amplitude) (b mass))
           (:instance lw-mss-multiply-order (a amplitude) (b signal-cap) (factor mass))
           (:instance lw-mss-multiply-order (a point-cap) (b shift-cap) (factor error))
           (:instance lw-mss-multiply-order
             (a (+ (* point-cap error) (* base-cap error) (* 2 error)))
             (b (+ (* shift-cap error) (* base-cap error) (* 2 error))) (factor (* amplitude mass)))
           (:instance lw-mss-multiply-order
             (a (* amplitude mass)) (b (* signal-cap mass))
             (factor (+ (* shift-cap error) (* base-cap error) (* 2 error)))))
           :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-mss-common-exponential-form
         (equal (lw-mellin-exponential-sample value sigma height index step error error)
                (lw-complex-scale
                 (* (lw-mellin-signal value sigma index step error)
                    (lw-kernel-weight-scale value index step))
                 (lw-complex-exp-value (lw-mellin-exponent value sigma height) error)))
         :hints (("Goal" :in-theory (enable lw-mellin-exponential-sample lw-mellin-exponent)))))

(defthm lw-mellin-exponential-sample-shift
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (lw-complex-diskp shift radius)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-mul
                 (lw-mellin-exponential-sample value sigma height index step error error)
                 (lw-complex-exp-value (lw-complex-scale value shift) error))
               (lw-mellin-frozen-exponential
                 value
                 sigma
                 (- sigma (car shift))
                 (- height (cdr shift))
                 index
                 step
                 error))
             (*
               (lw-mellin-signal-cap value)
               (lw-kernel-weight-scale value index step)
               (+
                 (lw-complex-exp-radius-cap (* 2 value radius))
                 (lw-complex-exp-cap (lw-mellin-exponent value sigma height))
                 2)
               error)))
  :hints (("Goal" :use (
    lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative lw-mellin-signal-cap-valid
    (:instance lw-complex-exp-cap-valid (point (lw-mellin-exponent value sigma height)))
    (:instance lw-complex-exp-cap-valid (point (lw-complex-scale value shift)))
    (:instance lw-complex-exp-radius-cap-valid (radius (* 2 value radius)))
    (:instance lw-mss-product-nonnegative (a value) (b radius))
    (:instance lw-complex-exp-scaled-disk-cap (point shift) (factor value))
    (:instance lw-complex-exp-value-multiplication
      (left (lw-mellin-exponent value sigma height))
      (right (lw-complex-scale value shift))
      (left-error error)
      (right-error error)
      (sum-error error))
    (:instance lw-mss-scaled-product-error
      (factor (* (lw-mellin-signal value sigma index step error) (lw-kernel-weight-scale value index step)))
      (left (lw-complex-exp-value (lw-mellin-exponent value sigma height) error))
      (right (lw-complex-exp-value (lw-complex-scale value shift) error))
      (target
        (lw-complex-exp-value (lw-mellin-exponent value (- sigma (car shift)) (- height (cdr shift))) error))
      (error
        (+
          (* (lw-complex-exp-cap (lw-complex-scale value shift)) error)
          (* (lw-complex-exp-cap (lw-mellin-exponent value sigma height)) error)
          (* 2 error))))
    (:instance lw-mss-abs-product
      (a (lw-mellin-signal value sigma index step error))
      (b (lw-kernel-weight-scale value index step)))
    (:instance lw-mss-scaled-addition-budget
      (amplitude (abs (lw-mellin-signal value sigma index step error)))
      (signal-cap (lw-mellin-signal-cap value))
      (mass (lw-kernel-weight-scale value index step))
      (point-cap (lw-complex-exp-cap (lw-complex-scale value shift)))
      (shift-cap (lw-complex-exp-radius-cap (* 2 value radius)))
      (base-cap (lw-complex-exp-cap (lw-mellin-exponent value sigma height))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-mul
            (lw-mellin-exponential-sample value sigma height index step error error)
            (lw-complex-exp-value (lw-complex-scale value shift) error))
          (lw-mellin-frozen-exponential
            value
            sigma
            (- sigma (car shift))
            (- height (cdr shift))
            index
            step
            error)))
      (radius
        (*
          (abs (lw-mellin-signal value sigma index step error))
          (lw-kernel-weight-scale value index step)
          (+
            (* (lw-complex-exp-cap (lw-complex-scale value shift)) error)
            (* (lw-complex-exp-cap (lw-mellin-exponent value sigma height)) error)
            (* 2 error))))
      (cap
        (*
          (lw-mellin-signal-cap value)
          (lw-kernel-weight-scale value index step)
          (+
            (lw-complex-exp-radius-cap (* 2 value radius))
            (lw-complex-exp-cap (lw-mellin-exponent value sigma height))
            2)
          error))))
    :in-theory (e/d (lw-mellin-frozen-exponential)
                    (lw-mellin-signal-bounded lw-kernel-weight-scale-nonnegative lw-mellin-signal-cap-valid
                     lw-complex-exp-cap-valid lw-complex-exp-radius-cap-valid lw-complex-exp-scaled-disk-cap
                     lw-complex-exp-value-multiplication lw-mss-abs-product))
    :nonlinearp t)))


(local (defthm lw-mss-composed-budget
         (implies (and (rationalp left-error) (rationalp right-error)
                       (rationalp factor) (<= 0 factor) (rationalp shift-cap) (<= 0 shift-cap)
                       (rationalp signal-cap) (rationalp base-cap)
                       (rationalp mass) (<= 0 mass) (rationalp error) (<= 0 error) (<= error 1)
                       (<= left-error (* factor (+ error error)))
                       (<= right-error (* factor (+ error error))))
                  (<= (+ (* shift-cap left-error)
                         (* signal-cap mass (+ shift-cap base-cap 2) error)
                         (* 2 mass (+ 1 error) error) right-error)
                      (* (+ 1 (* 2 factor (+ 1 shift-cap))
                            (* signal-cap mass (+ shift-cap base-cap 2)) (* 4 mass)) error)))
         :hints (("Goal" :use (
           (:instance lw-mss-multiply-order (a left-error) (b (* factor (+ error error))) (factor shift-cap))
           (:instance lw-mss-product-nonnegative (a mass) (b error))
           (:instance lw-mss-multiply-order (a (+ 1 error)) (b 2) (factor (* 2 mass error))))
           :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-sample-shift-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (lw-complex-diskp shift radius)
                (<= 0 (- sigma (car shift))) (rationalp error) (< 0 error) (<= error 1))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-mul
                 (lw-mellin-sample value sigma height index step error)
                 (lw-complex-exp-value (lw-complex-scale value shift) error))
               (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) index step error))
             (* (lw-mellin-shift-error-factor value sigma height index step radius) error)))
  :hints (("Goal" :use (
    lw-kernel-weight-scale-nonnegative lw-mellin-signal-cap-valid lw-mellin-exponential-error-factor-valid
    (:instance lw-mss-product-nonnegative (a value) (b radius))
    (:instance lw-complex-exp-radius-cap-valid (radius (* 2 value radius)))
    (:instance lw-complex-exp-cap-valid (point (lw-mellin-exponent value sigma height)))
    (:instance lw-complex-exp-scaled-disk-cap (factor value) (point shift))
    (:instance lw-complex-exp-value-cap (point (lw-complex-scale value shift)))
    (:instance lw-complex-disk-enlarge
      (point (lw-complex-exp-value (lw-complex-scale value shift) error))
      (radius (lw-complex-exp-cap (lw-complex-scale value shift)))
      (cap (lw-complex-exp-radius-cap (* 2 value radius))))
    (:instance lw-mellin-sample-exponential-comparison (sample-error error) (complex-error error))
    (:instance lw-mellin-sample-exponential-comparison
      (sigma (- sigma (car shift)))
      (height (- height (cdr shift)))
      (sample-error error)
      (complex-error error))
    (:instance lw-mellin-exponential-sample-error-budget (sample-error error) (complex-error error))
    (:instance lw-mellin-exponential-sample-error-budget
      (sigma (- sigma (car shift)))
      (sample-error error)
      (complex-error error))
    (:instance lw-mss-shared-right-bound
      (a (lw-mellin-sample value sigma height index step error))
      (b (lw-mellin-exponential-sample value sigma height index step error error))
      (point (lw-complex-exp-value (lw-complex-scale value shift) error))
      (cap (lw-complex-exp-radius-cap (* 2 value radius)))
      (error (lw-mellin-exponential-sample-error value sigma index step error error)))
    lw-mellin-exponential-sample-shift
    (:instance lw-mellin-frozen-signal-comparison
      (base-sigma sigma)
      (sigma (- sigma (car shift)))
      (height (- height (cdr shift))))
    (:instance lw-complex-difference-symmetric
      (left (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) index step error))
      (right
        (lw-mellin-exponential-sample
          value
          (- sigma (car shift))
          (- height (cdr shift))
          index
          step
          error
          error))
      (radius (lw-mellin-exponential-sample-error value (- sigma (car shift)) index step error error)))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-mul
          (lw-mellin-sample value sigma height index step error)
          (lw-complex-exp-value (lw-complex-scale value shift) error)))
      (middle
        (lw-complex-mul
          (lw-mellin-exponential-sample value sigma height index step error error)
          (lw-complex-exp-value (lw-complex-scale value shift) error)))
      (right
        (lw-mellin-frozen-exponential
          value
          sigma
          (- sigma (car shift))
          (- height (cdr shift))
          index
          step
          error))
      (radius
        (*
          (lw-complex-exp-radius-cap (* 2 value radius))
          (lw-mellin-exponential-sample-error value sigma index step error error)))
      (other-radius
        (*
          (lw-mellin-signal-cap value)
          (lw-kernel-weight-scale value index step)
          (+
            (lw-complex-exp-radius-cap (* 2 value radius))
            (lw-complex-exp-cap (lw-mellin-exponent value sigma height))
            2)
          error)))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-mul
          (lw-mellin-sample value sigma height index step error)
          (lw-complex-exp-value (lw-complex-scale value shift) error)))
      (middle
        (lw-mellin-frozen-exponential
          value
          sigma
          (- sigma (car shift))
          (- height (cdr shift))
          index
          step
          error))
      (right
        (lw-mellin-exponential-sample
          value
          (- sigma (car shift))
          (- height (cdr shift))
          index
          step
          error
          error))
      (radius
        (+
          (*
            (lw-complex-exp-radius-cap (* 2 value radius))
            (lw-mellin-exponential-sample-error value sigma index step error error))
          (*
            (lw-mellin-signal-cap value)
            (lw-kernel-weight-scale value index step)
            (+
              (lw-complex-exp-radius-cap (* 2 value radius))
              (lw-complex-exp-cap (lw-mellin-exponent value sigma height))
              2)
            error)))
      (other-radius (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-mul
          (lw-mellin-sample value sigma height index step error)
          (lw-complex-exp-value (lw-complex-scale value shift) error)))
      (middle
        (lw-mellin-exponential-sample
          value
          (- sigma (car shift))
          (- height (cdr shift))
          index
          step
          error
          error))
      (right (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) index step error))
      (radius
        (+
          (*
            (lw-complex-exp-radius-cap (* 2 value radius))
            (lw-mellin-exponential-sample-error value sigma index step error error))
          (*
            (lw-mellin-signal-cap value)
            (lw-kernel-weight-scale value index step)
            (+
              (lw-complex-exp-radius-cap (* 2 value radius))
              (lw-complex-exp-cap (lw-mellin-exponent value sigma height))
              2)
            error)
          (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)))
      (other-radius (lw-mellin-exponential-sample-error value (- sigma (car shift)) index step error error)))
    (:instance lw-mss-composed-budget
      (left-error (lw-mellin-exponential-sample-error value sigma index step error error))
      (right-error (lw-mellin-exponential-sample-error value (- sigma (car shift)) index step error error))
      (factor (lw-mellin-exponential-error-factor value index step))
      (shift-cap (lw-complex-exp-radius-cap (* 2 value radius)))
      (signal-cap (lw-mellin-signal-cap value))
      (base-cap (lw-complex-exp-cap (lw-mellin-exponent value sigma height)))
      (mass (lw-kernel-weight-scale value index step)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-mul
            (lw-mellin-sample value sigma height index step error)
            (lw-complex-exp-value (lw-complex-scale value shift) error))
          (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) index step error)))
      (radius
        (+
          (*
            (lw-complex-exp-radius-cap (* 2 value radius))
            (lw-mellin-exponential-sample-error value sigma index step error error))
          (*
            (lw-mellin-signal-cap value)
            (lw-kernel-weight-scale value index step)
            (+
              (lw-complex-exp-radius-cap (* 2 value radius))
              (lw-complex-exp-cap (lw-mellin-exponent value sigma height))
              2)
            error)
          (* 2 (lw-kernel-weight-scale value index step) (+ 1 error) error)
          (lw-mellin-exponential-sample-error value (- sigma (car shift)) index step error error)))
      (cap (* (lw-mellin-shift-error-factor value sigma height index step radius) error))))
    :in-theory (e/d (lw-mellin-shift-error-factor)
                    (lw-mss-common-exponential-form lw-kernel-weight-scale-nonnegative lw-mellin-signal-cap-valid
                     lw-mellin-exponential-error-factor-valid lw-complex-exp-radius-cap-valid lw-complex-exp-cap-valid
                     lw-complex-exp-scaled-disk-cap lw-complex-exp-value-cap
                     lw-mellin-sample-exponential-comparison lw-mellin-exponential-sample-error-budget
                     lw-mellin-exponential-sample-shift lw-mellin-frozen-signal-comparison lw-complex-difference-triangle))
    :nonlinearp t)))


(defthm lw-mellin-sample-computed-shift
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step) (lw-complex-diskp shift radius)
                (<= 0 (- sigma (car shift))) (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-mul
                 (lw-mellin-sample
                   value
                   sigma
                   height
                   index
                   step
                   (lw-mellin-shift-precision value sigma height index step radius error))
                 (lw-complex-exp-value
                   (lw-complex-scale value shift)
                   (lw-mellin-shift-precision value sigma height index step radius error)))
               (lw-mellin-sample
                 value
                 (- sigma (car shift))
                 (- height (cdr shift))
                 index
                 step
                 (lw-mellin-shift-precision value sigma height index step radius error)))
             error))
  :hints (("Goal" :use (lw-mellin-shift-precision-adequate
                        (:instance lw-mellin-sample-shift-bound
                          (error (lw-mellin-shift-precision value sigma height index step radius error)))
                        (:instance lw-complex-disk-enlarge
                          (point
                            (lw-complex-sub
                              (lw-complex-mul
                                (lw-mellin-sample
                                  value
                                  sigma
                                  height
                                  index
                                  step
                                  (lw-mellin-shift-precision value sigma height index step radius error))
                                (lw-complex-exp-value
                                  (lw-complex-scale value shift)
                                  (lw-mellin-shift-precision value sigma height index step radius error)))
                              (lw-mellin-sample
                                value
                                (- sigma (car shift))
                                (- height (cdr shift))
                                index
                                step
                                (lw-mellin-shift-precision value sigma height index step radius error))))
                          (radius
                            (*
                              (lw-mellin-shift-error-factor value sigma height index step radius)
                              (lw-mellin-shift-precision value sigma height index step radius error)))
                          (cap error)))
                  :in-theory (disable lw-mss-common-exponential-form
                                      lw-mellin-shift-precision-adequate lw-mellin-sample-shift-bound))))

