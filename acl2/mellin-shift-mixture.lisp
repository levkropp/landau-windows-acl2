(in-package "ACL2")

(include-book "mellin-sample-shift")
(include-book "exp-mixture-bounds")
(include-book "mellin-quadrature")

; Freeze actual zeroth-moment samples across a whole shift disk.
; The target moment affects precision selection only, not the resulting
; polynomial's consistency across coefficients or evaluation points.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-value lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-phase-value lw-log-signal-bounds
                 lw-mellin-sample lw-mellin-sample-kernel-form lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-kernel-weight-scale
                 lw-mellin-exponential-error-factor lw-mellin-sample-cap
                 lw-mellin-shift-error-factor lw-mellin-shift-precision
                 lw-mellin-moment-precision lw-mellin-moment-error-factor
                 lw-exp-mixture-node-precision lw-exp-mixture-value
                 lw-mellin-sum-raw lw-mellin-sum lw-mellin-sum-error
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-msm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-msm-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-msm-zero-times (equal (* 0 a) 0)))
(local (defthm lw-msm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-msm-components
         (implies (lw-complexp point) (and (rationalp (car point)) (rationalp (cdr point))))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(defun lw-mellin-shift-node-precision (value sigma height target step radius budget)
  (min (lw-mellin-shift-precision value sigma height 0 step radius budget)
       (min (lw-mellin-moment-precision value target step budget)
            (min budget (/ budget (* 4 (+ 1 (lw-mellin-sample-cap value 0 step))))))))

(defthm lw-mellin-shift-node-precision-data
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget))
           (and (rationalp (lw-mellin-shift-node-precision value sigma height target step radius budget))
                (< 0 (lw-mellin-shift-node-precision value sigma height target step radius budget))
                (<= (lw-mellin-shift-node-precision value sigma height target step radius budget) 1)
                (<= (lw-mellin-shift-node-precision value sigma height target step radius budget) budget)
                (<= (lw-mellin-shift-node-precision value sigma height target step radius budget)
                    (lw-mellin-moment-precision value target step budget))
                (<= (* (lw-mellin-shift-error-factor value sigma height 0 step radius)
                       (lw-mellin-shift-node-precision value sigma height target step radius budget)) budget)
                (<= (* (lw-mellin-sample-cap value 0 step)
                       (lw-mellin-shift-node-precision value sigma height target step radius budget)) (* 1/4 budget))))
  :hints (("Goal" :use (
    (:instance lw-mellin-shift-precision-adequate (index 0) (error budget))
    (:instance lw-mellin-shift-error-factor-valid (index 0))
    (:instance lw-mellin-moment-precision-adequate (index target) (error budget))
    (:instance lw-mellin-sample-cap-valid (index 0))
    (:instance lw-positive-division-bound
      (numerator (* (lw-mellin-sample-cap value 0 step) budget))
      (divisor (* 4 (+ 1 (lw-mellin-sample-cap value 0 step)))) (bound (* 1/4 budget))))
    :in-theory (disable lw-mellin-shift-precision-adequate lw-mellin-shift-error-factor-valid
                        lw-mellin-moment-precision-adequate lw-mellin-sample-cap-valid)
    :nonlinearp t)))

(local (in-theory (disable lw-mellin-shift-node-precision)))

(defun lw-mellin-shift-node-base (value sigma height target step radius budget)
  (lw-mellin-sample value sigma height 0 step
                    (lw-mellin-shift-node-precision value sigma height target step radius budget)))

(defthm lw-mellin-shift-node-base-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget))
           (lw-complexp (lw-mellin-shift-node-base value sigma height target step radius budget)))
  :hints (("Goal" :use (lw-mellin-shift-node-precision-data)
                  :in-theory (disable lw-mellin-shift-node-precision-data))))

(defthm lw-mellin-shift-node-base-l1
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget))
           (<= (lw-complex-l1 (lw-mellin-shift-node-base value sigma height target step radius budget))
               (* 2 (lw-mellin-sample-cap value 0 step))))
  :hints (("Goal" :use (lw-mellin-shift-node-precision-data
                        (:instance lw-mellin-sample-l1-cap
                          (index 0) (error (lw-mellin-shift-node-precision value sigma height target step radius budget))))
                  :in-theory (disable lw-mellin-shift-node-precision-data lw-mellin-sample-l1-cap))))

(local (in-theory (disable lw-mellin-shift-node-base)))


(defthm lw-mellin-shift-node-exponential-error
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (lw-complex-diskp shift radius)
                (rationalp budget) (< 0 budget))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-mul
                 (lw-mellin-shift-node-base value sigma height target step radius budget)
                 (lw-complex-exp-value
                   (lw-complex-scale value shift)
                   (lw-exp-mixture-node-precision
                     (lw-mellin-shift-node-base value sigma height target step radius budget)
                     budget)))
               (lw-complex-mul
                 (lw-mellin-shift-node-base value sigma height target step radius budget)
                 (lw-complex-exp-value
                   (lw-complex-scale value shift)
                   (lw-mellin-shift-node-precision value sigma height target step radius budget))))
             budget))
  :hints (("Goal" :use (
    lw-mellin-shift-node-precision-data lw-mellin-shift-node-base-l1
    (:instance lw-complex-l1-bound (point (lw-mellin-shift-node-base value sigma height target step radius budget)))
    (:instance lw-exp-mixture-node-precision-adequate
      (base (lw-mellin-shift-node-base value sigma height target step radius budget)))
    (:instance lw-complex-exp-value-cap
      (point (lw-complex-scale value shift))
      (error
        (lw-exp-mixture-node-precision
          (lw-mellin-shift-node-base value sigma height target step radius budget)
          budget)))
    (:instance lw-complex-exp-value-cauchy
      (point (lw-complex-scale value shift))
      (left-error
        (lw-exp-mixture-node-precision
          (lw-mellin-shift-node-base value sigma height target step radius budget)
          budget))
      (right-error (lw-mellin-shift-node-precision value sigma height target step radius budget)))
    (:instance lw-complex-mul-difference-bound
      (a (lw-mellin-shift-node-base value sigma height target step radius budget))
      (b
        (lw-complex-exp-value
          (lw-complex-scale value shift)
          (lw-exp-mixture-node-precision
            (lw-mellin-shift-node-base value sigma height target step radius budget)
            budget)))
      (c (lw-mellin-shift-node-base value sigma height target step radius budget))
      (d
        (lw-complex-exp-value
          (lw-complex-scale value shift)
          (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (left-cap (lw-complex-l1 (lw-mellin-shift-node-base value sigma height target step radius budget)))
      (right-cap (lw-complex-exp-cap (lw-complex-scale value shift)))
      (left-error 0)
      (right-error
        (+
          (lw-exp-mixture-node-precision
            (lw-mellin-shift-node-base value sigma height target step radius budget)
            budget)
          (lw-mellin-shift-node-precision value sigma height target step radius budget))))
    (:instance lw-msm-multiply-order
      (a (lw-complex-l1 (lw-mellin-shift-node-base value sigma height target step radius budget)))
      (b (* 2 (lw-mellin-sample-cap value 0 step)))
      (factor (lw-mellin-shift-node-precision value sigma height target step radius budget)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-mul
            (lw-mellin-shift-node-base value sigma height target step radius budget)
            (lw-complex-exp-value
              (lw-complex-scale value shift)
              (lw-exp-mixture-node-precision
                (lw-mellin-shift-node-base value sigma height target step radius budget)
                budget)))
          (lw-complex-mul
            (lw-mellin-shift-node-base value sigma height target step radius budget)
            (lw-complex-exp-value
              (lw-complex-scale value shift)
              (lw-mellin-shift-node-precision value sigma height target step radius budget)))))
      (radius
        (*
          (lw-complex-l1 (lw-mellin-shift-node-base value sigma height target step radius budget))
          (+
            (lw-exp-mixture-node-precision
              (lw-mellin-shift-node-base value sigma height target step radius budget)
              budget)
            (lw-mellin-shift-node-precision value sigma height target step radius budget))))
      (cap budget)))
    :in-theory (disable lw-mellin-shift-node-precision-data lw-mellin-shift-node-base-l1 lw-complex-l1-bound
                        lw-exp-mixture-node-precision-adequate lw-complex-exp-value-cap lw-complex-exp-value-cauchy
                        lw-complex-mul-difference-bound)
    :nonlinearp t)))

(defthm lw-mellin-shift-node-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (lw-complex-diskp shift radius)
                (<= 0 (- sigma (car shift))) (rationalp budget) (< 0 budget) (rationalp point-error) (< 0 point-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-mul
                 (lw-mellin-shift-node-base value sigma height target step radius budget)
                 (lw-complex-exp-value
                   (lw-complex-scale value shift)
                   (lw-exp-mixture-node-precision
                     (lw-mellin-shift-node-base value sigma height target step radius budget)
                     budget)))
               (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) 0 step point-error))
             (+ (* 3 budget) point-error)))
  :hints (("Goal" :use (
    lw-mellin-shift-node-precision-data lw-mellin-shift-node-exponential-error
    (:instance lw-mellin-sample-shift-bound
      (index 0)
      (error (lw-mellin-shift-node-precision value sigma height target step radius budget)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-mul
            (lw-mellin-shift-node-base value sigma height target step radius budget)
            (lw-complex-exp-value
              (lw-complex-scale value shift)
              (lw-mellin-shift-node-precision value sigma height target step radius budget)))
          (lw-mellin-sample
            value
            (- sigma (car shift))
            (- height (cdr shift))
            0
            step
            (lw-mellin-shift-node-precision value sigma height target step radius budget))))
      (radius
        (*
          (lw-mellin-shift-error-factor value sigma height 0 step radius)
          (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (cap budget))
    (:instance lw-mellin-sample-cauchy
      (sigma (- sigma (car shift)))
      (height (- height (cdr shift)))
      (index 0)
      (left-error (lw-mellin-shift-node-precision value sigma height target step radius budget))
      (right-error point-error))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-mul
          (lw-mellin-shift-node-base value sigma height target step radius budget)
          (lw-complex-exp-value
            (lw-complex-scale value shift)
            (lw-exp-mixture-node-precision
              (lw-mellin-shift-node-base value sigma height target step radius budget)
              budget))))
      (middle
        (lw-complex-mul
          (lw-mellin-shift-node-base value sigma height target step radius budget)
          (lw-complex-exp-value
            (lw-complex-scale value shift)
            (lw-mellin-shift-node-precision value sigma height target step radius budget))))
      (right
        (lw-mellin-sample
          value
          (- sigma (car shift))
          (- height (cdr shift))
          0
          step
          (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (radius budget)
      (other-radius budget))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-mul
          (lw-mellin-shift-node-base value sigma height target step radius budget)
          (lw-complex-exp-value
            (lw-complex-scale value shift)
            (lw-exp-mixture-node-precision
              (lw-mellin-shift-node-base value sigma height target step radius budget)
              budget))))
      (middle
        (lw-mellin-sample
          value
          (- sigma (car shift))
          (- height (cdr shift))
          0
          step
          (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (right (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) 0 step point-error))
      (radius (+ budget budget))
      (other-radius
        (+ (lw-mellin-shift-node-precision value sigma height target step radius budget) point-error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-mul
            (lw-mellin-shift-node-base value sigma height target step radius budget)
            (lw-complex-exp-value
              (lw-complex-scale value shift)
              (lw-exp-mixture-node-precision
                (lw-mellin-shift-node-base value sigma height target step radius budget)
                budget)))
          (lw-mellin-sample value (- sigma (car shift)) (- height (cdr shift)) 0 step point-error)))
      (radius
        (+
          budget
          budget
          (lw-mellin-shift-node-precision value sigma height target step radius budget)
          point-error))
      (cap (+ (* 3 budget) point-error))))
    :in-theory (e/d (lw-mellin-shift-node-base)
                    (lw-mellin-shift-node-precision-data lw-mellin-shift-node-exponential-error
                     lw-mellin-sample-shift-bound lw-mellin-sample-cauchy lw-complex-difference-triangle))
    :nonlinearp t)))


(defun lw-mellin-shift-mixture-nodes (cells sigma height target radius budget)
  (if (consp cells)
      (cons (cons (caar cells)
                  (lw-mellin-shift-node-base (caar cells) sigma height target (cdar cells) radius budget))
            (lw-mellin-shift-mixture-nodes (cdr cells) sigma height target radius budget))
    nil))

(defthm lw-mellin-shift-mixture-nodes-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp budget) (< 0 budget))
           (and (lw-exp-mixturep (lw-mellin-shift-mixture-nodes cells sigma height target radius budget))
                (equal (len (lw-mellin-shift-mixture-nodes cells sigma height target radius budget)) (len cells))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (enable lw-exp-mixturep))))

(local (in-theory (disable lw-mellin-shift-mixture-nodes)))

(defthm lw-mellin-shift-mixture-raw-comparison
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (lw-complex-diskp shift radius) (<= 0 (- sigma (car shift)))
                (rationalp budget) (< 0 budget) (rationalp point-error) (< 0 point-error))
           (lw-complex-diskp (lw-complex-sub (lw-exp-mixture-value (lw-mellin-shift-mixture-nodes cells sigma height target radius budget) shift budget) (lw-mellin-sum-raw cells (- sigma (car shift)) (- height (cdr shift)) 0 point-error))
                             (* (len cells) (+ (* 3 budget) point-error))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (e/d (lw-mellin-shift-mixture-nodes lw-exp-mixture-value lw-mellin-sum-raw)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))
          (and stable-under-simplificationp
               '(:use (
                 (:instance lw-mellin-shift-node-comparison (value (caar cells)) (step (cdar cells)))
                 (:instance lw-complex-add-disk
                   (left
                     (lw-complex-sub
                       (lw-complex-mul
                         (lw-mellin-shift-node-base
                           (caar cells)
                           sigma
                           height
                           target
                           (cdar cells)
                           radius
                           budget)
                         (lw-complex-exp-value
                           (lw-complex-scale (caar cells) shift)
                           (lw-exp-mixture-node-precision
                             (lw-mellin-shift-node-base
                               (caar cells)
                               sigma
                               height
                               target
                               (cdar cells)
                               radius
                               budget)
                             budget)))
                       (lw-mellin-sample
                         (caar cells)
                         (- sigma (car shift))
                         (- height (cdr shift))
                         0
                         (cdar cells)
                         point-error)))
                   (right
                     (lw-complex-sub
                       (lw-exp-mixture-value
                         (lw-mellin-shift-mixture-nodes (cdr cells) sigma height target radius budget)
                         shift
                         budget)
                       (lw-mellin-sum-raw
                         (cdr cells)
                         (- sigma (car shift))
                         (- height (cdr shift))
                         0
                         point-error)))
                   (radius (+ (* 3 budget) point-error))
                   (other-radius (* (len (cdr cells)) (+ (* 3 budget) point-error)))))
                 :in-theory (disable lw-mellin-shift-mixture-nodes lw-exp-mixture-value lw-mellin-sum-raw
                                     lw-mellin-shift-node-comparison lw-complex-add-disk
                                     lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))))

(defun lw-mellin-shift-mixture-budget (cells error)
  (lw-mellin-sum-error cells (* 1/8 error)))

(defthm lw-mellin-shift-mixture-budget-data
  (implies (and (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-shift-mixture-budget cells error))
                (< 0 (lw-mellin-shift-mixture-budget cells error))
                (<= (* (len cells)
                       (+ (* 3 (lw-mellin-shift-mixture-budget cells error))
                          (lw-mellin-sum-error cells (* 1/4 error)))) error)))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (* 1/8 error)))
                        (:instance lw-mellin-sum-error-budget (error (* 1/8 error)))
                        (:instance lw-mellin-sum-error-budget (error (* 1/4 error))))
                  :in-theory (disable lw-mellin-sum-error-positive lw-mellin-sum-error-budget))))

(local (in-theory (disable lw-mellin-shift-mixture-budget)))

(defthm lw-mellin-computed-shift-mixture-comparison
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (lw-complex-diskp shift radius) (<= radius sigma)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-exp-mixture-value
                 (lw-mellin-shift-mixture-nodes
                   cells
                   sigma
                   height
                   target
                   radius
                   (lw-mellin-shift-mixture-budget cells error))
                 shift
                 (lw-mellin-shift-mixture-budget cells error))
               (lw-mellin-sum cells (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/4 error)))
             error))
  :hints (("Goal" :use (
    lw-mellin-shift-mixture-budget-data
    (:instance lw-complex-disk-coordinates (point shift))
    (:instance lw-mellin-sum-error-positive (error (* 1/4 error)))
    (:instance lw-mellin-shift-mixture-raw-comparison
      (budget (lw-mellin-shift-mixture-budget cells error))
      (point-error (lw-mellin-sum-error cells (* 1/4 error))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-exp-mixture-value
            (lw-mellin-shift-mixture-nodes
              cells
              sigma
              height
              target
              radius
              (lw-mellin-shift-mixture-budget cells error))
            shift
            (lw-mellin-shift-mixture-budget cells error))
          (lw-mellin-sum cells (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/4 error))))
      (radius
        (*
          (len cells)
          (+ (* 3 (lw-mellin-shift-mixture-budget cells error)) (lw-mellin-sum-error cells (* 1/4 error)))))
      (cap error)))
    :in-theory (e/d (lw-mellin-sum)
                    (lw-mellin-shift-mixture-budget-data lw-complex-disk-coordinates
                     lw-mellin-sum-error-positive lw-mellin-shift-mixture-raw-comparison)))))


(defun lw-mellin-shift-polynomial-nodes (cells sigma height target radius error)
  (lw-mellin-shift-mixture-nodes cells sigma height target radius
                                 (lw-mellin-shift-mixture-budget cells (* 1/2 error))))

(defthm lw-mellin-shift-polynomial-nodes-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (and (lw-exp-mixturep (lw-mellin-shift-polynomial-nodes cells sigma height target radius error))
                (equal (len (lw-mellin-shift-polynomial-nodes cells sigma height target radius error)) (len cells))))
  :hints (("Goal" :use ((:instance lw-mellin-shift-mixture-budget-data (error (* 1/2 error))))
                  :in-theory (disable lw-mellin-shift-mixture-budget-data))))

(local (in-theory (disable lw-mellin-shift-polynomial-nodes)))

(local (defthm lw-msm-polynomial-budget
         (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                       (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
                  (equal (lw-exp-mixture-budget
                          (lw-mellin-shift-polynomial-nodes cells sigma height target radius error)
                          (* 1/16 error))
                         (lw-mellin-shift-mixture-budget cells (* 1/2 error))))
         :hints (("Goal" :in-theory (enable lw-exp-mixture-budget lw-mellin-shift-mixture-budget lw-mellin-sum-error)))))

(defun lw-mellin-shift-polynomial-degree (cells sigma height target radius error)
  (lw-exp-mixture-degree (lw-mellin-shift-polynomial-nodes cells sigma height target radius error)
                         radius target (* 1/16 error)))

(defthm lw-mellin-shift-polynomial-degree-data
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (and (natp (lw-mellin-shift-polynomial-degree cells sigma height target radius error))
                (<= target (lw-mellin-shift-polynomial-degree cells sigma height target radius error))))
  :hints (("Goal" :use ((:instance lw-exp-mixture-degree-data
                          (nodes (lw-mellin-shift-polynomial-nodes cells sigma height target radius error))
                          (error (* 1/16 error))))
                  :in-theory (disable lw-exp-mixture-degree-data lw-exp-mixture-degree lw-exp-mixture-degree-raw))))

(local (in-theory (disable lw-mellin-shift-polynomial-degree lw-exp-mixture-degree
                           lw-exp-mixture-degree-raw lw-exp-mixture-budget)))

(defun lw-mellin-shift-polynomial (cells sigma height target radius error)
  (lw-exp-mixture-coefficients
   (lw-mellin-shift-polynomial-nodes cells sigma height target radius error) 0
   (+ 1 (lw-mellin-shift-polynomial-degree cells sigma height target radius error))))

(defthm lw-mellin-shift-polynomial-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-mellin-shift-polynomial cells sigma height target radius error))
                (< target (len (lw-mellin-shift-polynomial cells sigma height target radius error)))))
  :hints (("Goal" :use (lw-mellin-shift-polynomial-degree-data)
                  :in-theory (disable lw-mellin-shift-polynomial-degree-data lw-exp-mixture-coefficients))))

(local (in-theory (disable lw-mellin-shift-polynomial)))

(local (defthm lw-msm-half-quarter
         (implies (rationalp value) (equal (* 1/2 1/4 value) (* 1/8 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/2) (y 1/4) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-msm-left-commutes)))))

(defthm lw-mellin-computed-uniform-shift-polynomial
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (lw-complex-diskp shift radius) (<= radius sigma)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-polynomial
                 (lw-mellin-shift-polynomial cells sigma height target radius error)
                 shift
                 0)
               (lw-mellin-sum cells (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/8 error)))
             error))
  :hints (("Goal" :use (
    lw-mellin-shift-polynomial-valid lw-msm-polynomial-budget
    (:instance lw-mellin-shift-mixture-budget-data (error (* 1/2 error)))
    (:instance lw-complex-disk-coordinates (point shift))
    (:instance lw-exp-mixture-computed-uniform-polynomial
      (nodes (lw-mellin-shift-polynomial-nodes cells sigma height target radius error))
      (point shift)
      (error (* 1/16 error)))
    (:instance lw-mellin-computed-shift-mixture-comparison (error (* 1/2 error)))
    (:instance lw-complex-difference-triangle
      (left
        (lw-complex-polynomial (lw-mellin-shift-polynomial cells sigma height target radius error) shift 0))
      (middle
        (lw-exp-mixture-value
          (lw-mellin-shift-polynomial-nodes cells sigma height target radius error)
          shift
          (lw-mellin-shift-mixture-budget cells (* 1/2 error))))
      (right (lw-mellin-sum cells (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/8 error)))
      (radius (* 1/16 error))
      (other-radius (* 1/2 error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-polynomial (lw-mellin-shift-polynomial cells sigma height target radius error) shift 0)
          (lw-mellin-sum cells (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/8 error))))
      (radius (+ (* 1/16 error) (* 1/2 error)))
      (cap error)))
    :in-theory (e/d (lw-mellin-shift-polynomial lw-mellin-shift-polynomial-degree lw-mellin-shift-polynomial-nodes)
                    (lw-mellin-shift-polynomial-valid lw-msm-polynomial-budget lw-mellin-shift-mixture-budget-data
                     lw-complex-disk-coordinates lw-exp-mixture-computed-uniform-polynomial
                     lw-mellin-computed-shift-mixture-comparison lw-complex-difference-triangle
                     lw-exp-mixture-coefficients lw-complex-polynomial))
    :do-not-induct t)))

