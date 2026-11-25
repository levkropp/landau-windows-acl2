(in-package "ACL2")

(include-book "mellin-shift-mixture")
(include-book "cauchy-extraction")

; The same frozen bases that approximate the shifted quadrature also
; recover its target moment. No coefficient estimate is an input.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-exp-value lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-cap
                 lw-complex-power lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-index lw-exp-band
                 lw-exp-bounds lw-exp-neg-bounds lw-phase-value lw-log-signal-bounds
                 lw-mellin-sample lw-mellin-sample-kernel-form lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-kernel-weight-scale
                 lw-mellin-moment-precision lw-mellin-moment-error-factor lw-mellin-moment-pair-error
                 lw-mellin-shift-node-base lw-mellin-shift-node-precision lw-mellin-shift-mixture-nodes
                 lw-mellin-shift-mixture-budget lw-mellin-shift-polynomial-nodes
                 lw-mellin-shift-polynomial-degree lw-mellin-shift-polynomial
                 lw-exp-mixture-coefficient lw-exp-mixture-coefficients
                 lw-mellin-sum-raw lw-mellin-sum lw-mellin-sum-error
                 lw-cauchy-boundary-check lw-cauchy-orbit-rotation lw-cauchy-coefficient-count
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-msc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-msc-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-msc-zero-times (equal (* 0 a) 0)))
(local (defthm lw-msc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-shift-node-moment-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget))
           (<=
             (*
               2
               (lw-mellin-moment-error-factor value target step)
               (lw-mellin-shift-node-precision value sigma height target step radius budget))
             budget))
  :hints (("Goal" :use (lw-mellin-shift-node-precision-data
                        (:instance lw-mellin-moment-error-factor-valid (index target))
                        (:instance lw-mellin-moment-precision-adequate (index target) (error budget))
                        (:instance lw-msc-multiply-order
                          (a (lw-mellin-shift-node-precision value sigma height target step radius budget))
                          (b (lw-mellin-moment-precision value target step budget))
                          (factor (* 2 (lw-mellin-moment-error-factor value target step)))))
                  :in-theory (disable lw-mellin-shift-node-precision-data lw-mellin-moment-error-factor-valid
                                      lw-mellin-moment-precision-adequate)
                  :nonlinearp t)))

(defthm lw-mellin-shift-node-coefficient-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp step) (<= 0 step) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget) (rationalp point-error) (< 0 point-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sample value sigma height target step point-error)
               (lw-complex-scale
                 (lw-exp-term value target)
                 (lw-mellin-shift-node-base value sigma height target step radius budget)))
             (+ point-error (* 2 budget))))
  :hints (("Goal" :use (lw-mellin-shift-node-precision-data lw-mellin-shift-node-moment-budget
    (:instance lw-mellin-moment-pair-error-budget
      (index target)
      (left-error (lw-mellin-shift-node-precision value sigma height target step radius budget))
      (right-error (lw-mellin-shift-node-precision value sigma height target step radius budget)))
    (:instance lw-mellin-sample-moment-comparison
      (index target)
      (left-error (lw-mellin-shift-node-precision value sigma height target step radius budget))
      (right-error (lw-mellin-shift-node-precision value sigma height target step radius budget)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sample
            value
            sigma
            height
            target
            step
            (lw-mellin-shift-node-precision value sigma height target step radius budget))
          (lw-complex-scale
            (lw-exp-term value target)
            (lw-mellin-shift-node-base value sigma height target step radius budget))))
      (radius
        (lw-mellin-moment-pair-error
          value
          sigma
          target
          step
          (lw-mellin-shift-node-precision value sigma height target step radius budget)
          (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (cap budget))
    (:instance lw-mellin-sample-cauchy
      (index target)
      (left-error point-error)
      (right-error (lw-mellin-shift-node-precision value sigma height target step radius budget)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sample value sigma height target step point-error))
      (middle
        (lw-mellin-sample
          value
          sigma
          height
          target
          step
          (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (right
        (lw-complex-scale
          (lw-exp-term value target)
          (lw-mellin-shift-node-base value sigma height target step radius budget)))
      (radius (+ point-error (lw-mellin-shift-node-precision value sigma height target step radius budget)))
      (other-radius budget))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sample value sigma height target step point-error)
          (lw-complex-scale
            (lw-exp-term value target)
            (lw-mellin-shift-node-base value sigma height target step radius budget))))
      (radius
        (+ point-error (lw-mellin-shift-node-precision value sigma height target step radius budget) budget))
      (cap (+ point-error (* 2 budget)))))
    :in-theory (e/d (lw-mellin-shift-node-base)
                    (lw-mellin-shift-node-precision-data lw-mellin-shift-node-moment-budget
                     lw-mellin-moment-pair-error-budget lw-mellin-sample-moment-comparison
                     lw-mellin-sample-cauchy lw-complex-difference-triangle))
    :nonlinearp t)))

(defthm lw-mellin-shift-coefficient-raw-comparison
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget) (rationalp point-error) (< 0 point-error))
           (lw-complex-diskp (lw-complex-sub (lw-mellin-sum-raw cells sigma height target point-error) (lw-exp-mixture-coefficient (lw-mellin-shift-mixture-nodes cells sigma height target radius budget) target))
                             (* (len cells) (+ point-error (* 2 budget)))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (e/d (lw-mellin-shift-mixture-nodes lw-exp-mixture-coefficient lw-mellin-sum-raw)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))
          (and stable-under-simplificationp
               '(:use (
                 (:instance lw-mellin-shift-node-coefficient-comparison (value (caar cells)) (step (cdar cells)))
                 (:instance lw-complex-add-disk
                   (left
                     (lw-complex-sub
                       (lw-mellin-sample (caar cells) sigma height target (cdar cells) point-error)
                       (lw-complex-scale
                         (lw-exp-term (caar cells) target)
                         (lw-mellin-shift-node-base
                           (caar cells)
                           sigma
                           height
                           target
                           (cdar cells)
                           radius
                           budget))))
                   (right
                     (lw-complex-sub
                       (lw-mellin-sum-raw (cdr cells) sigma height target point-error)
                       (lw-exp-mixture-coefficient
                         (lw-mellin-shift-mixture-nodes (cdr cells) sigma height target radius budget)
                         target)))
                   (radius (+ point-error (* 2 budget)))
                   (other-radius (* (len (cdr cells)) (+ point-error (* 2 budget))))))
                 :in-theory (disable lw-mellin-shift-mixture-nodes lw-exp-mixture-coefficient lw-mellin-sum-raw
                                     lw-mellin-shift-node-coefficient-comparison lw-complex-add-disk
                                     lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))))


(defthm lw-mellin-shift-polynomial-coefficient
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (and (equal (len (lw-mellin-shift-polynomial cells sigma height target radius error)) (+ 1 (lw-mellin-shift-polynomial-degree cells sigma height target radius error)))
                (equal
                  (nth target (lw-mellin-shift-polynomial cells sigma height target radius error))
                  (lw-exp-mixture-coefficient
                    (lw-mellin-shift-polynomial-nodes cells sigma height target radius error)
                    target))))
  :hints (("Goal" :use (lw-mellin-shift-polynomial-degree-data
    (:instance lw-exp-mixture-coefficient-nth
      (nodes (lw-mellin-shift-polynomial-nodes cells sigma height target radius error))
      (offset 0)
      (count (+ 1 (lw-mellin-shift-polynomial-degree cells sigma height target radius error)))
      (index target)))
    :in-theory (e/d (lw-mellin-shift-polynomial)
                    (lw-mellin-shift-polynomial-degree-data lw-exp-mixture-coefficient-nth)))))

(local (defthm lw-msc-half-quarter
         (implies (rationalp value) (equal (* 1/2 1/4 value) (* 1/8 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/2) (y 1/4) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-msc-left-commutes)))))

(defthm lw-mellin-shift-polynomial-moment-comparison
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sum cells sigma height target (* 1/8 error))
               (nth target (lw-mellin-shift-polynomial cells sigma height target radius error)))
             (* 1/2 error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-shift-mixture-budget-data (error (* 1/2 error)))
    (:instance lw-mellin-sum-error-positive (error (* 1/8 error)))
    (:instance lw-mellin-shift-coefficient-raw-comparison
      (budget (lw-mellin-shift-mixture-budget cells (* 1/2 error)))
      (point-error (lw-mellin-sum-error cells (* 1/8 error))))
    (:instance lw-msc-multiply-order
      (a
        (+
          (lw-mellin-sum-error cells (* 1/8 error))
          (* 2 (lw-mellin-shift-mixture-budget cells (* 1/2 error)))))
      (b
        (+
          (lw-mellin-sum-error cells (* 1/8 error))
          (* 3 (lw-mellin-shift-mixture-budget cells (* 1/2 error)))))
      (factor (len cells)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sum cells sigma height target (* 1/8 error))
          (nth target (lw-mellin-shift-polynomial cells sigma height target radius error))))
      (radius
        (*
          (len cells)
          (+
            (lw-mellin-sum-error cells (* 1/8 error))
            (* 2 (lw-mellin-shift-mixture-budget cells (* 1/2 error))))))
      (cap (* 1/2 error))))
    :in-theory (e/d (lw-mellin-shift-polynomial-nodes lw-mellin-sum)
                    (lw-mellin-shift-mixture-budget-data lw-mellin-sum-error-positive
                     lw-mellin-shift-coefficient-raw-comparison))
    :nonlinearp t)))

(defthm lw-mellin-shift-polynomial-cauchy-bound
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp target) (rationalp radius) (<= 0 radius)
                (rationalp error) (< 0 error) (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check (lw-mellin-shift-polynomial cells sigma height target radius error) (lw-cauchy-orbit-rotation (lw-mellin-shift-polynomial-degree cells sigma height target radius error)) 0
                  (lw-cauchy-coefficient-count (lw-mellin-shift-polynomial cells sigma height target radius error) (lw-mellin-shift-polynomial-degree cells sigma height target radius error) (* 1/2 error)) cap))
           (lw-complex-diskp (lw-mellin-sum cells sigma height target (* 1/8 error)) (+ cap error)))
  :hints (("Goal" :use (
    lw-mellin-shift-polynomial-valid lw-mellin-shift-polynomial-degree-data
    lw-mellin-shift-polynomial-coefficient lw-mellin-shift-polynomial-moment-comparison
    (:instance lw-cauchy-finite-coefficient-bound
      (coefficients (lw-mellin-shift-polynomial cells sigma height target radius error))
      (degree (lw-mellin-shift-polynomial-degree cells sigma height target radius error))
      (error (* 1/2 error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sum cells sigma height target (* 1/8 error)))
      (middle (nth target (lw-mellin-shift-polynomial cells sigma height target radius error)))
      (right (cons 0 0))
      (radius (* 1/2 error))
      (other-radius (+ cap (* 1/2 error))))
    (:instance lw-complex-disk-enlarge
      (point (lw-mellin-sum cells sigma height target (* 1/8 error)))
      (radius (+ (* 1/2 error) cap (* 1/2 error)))
      (cap (+ cap error))))
    :in-theory (disable lw-mellin-shift-polynomial-valid lw-mellin-shift-polynomial-degree-data
                        lw-mellin-shift-polynomial-moment-comparison lw-cauchy-finite-coefficient-bound
                        lw-complex-difference-triangle))))

