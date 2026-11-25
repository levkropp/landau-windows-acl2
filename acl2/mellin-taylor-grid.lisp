(in-package "ACL2")

(include-book "mellin-moments")
(include-book "mellin-quadrature")

; The j-th existing quadrature sample is close to the j-th Taylor
; coefficient of zeroth-moment samples, with all node precisions computed.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-error-budgets lw-log-signal-bounds lw-kernel-weight-bounds
                 lw-phase-value lw-kernel-weight-scale lw-exp-term
                 lw-mellin-moment-precision lw-mellin-moment-error-factor lw-mellin-moment-pair-error
                 lw-mellin-sum-raw lw-mellin-sum lw-mellin-sum-error
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mtg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mtg-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mtg-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mtg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mtg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(defun lw-mellin-node-taylor-coefficient (value sigma height index step budget)
  (lw-complex-scale
   (lw-exp-term value index)
   (lw-mellin-sample value sigma height 0 step (lw-mellin-moment-precision value index step budget))))

(defthm lw-mellin-node-taylor-coefficient-rational
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (natp index) (rationalp budget) (< 0 budget))
           (lw-complexp (lw-mellin-node-taylor-coefficient value sigma height index step budget)))
  :hints (("Goal" :use ((:instance lw-mellin-moment-precision-adequate (error budget)))
                  :in-theory (disable lw-mellin-moment-precision-adequate))))

(defthm lw-mellin-node-taylor-comparison
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (natp index)
                (rationalp point-error) (< 0 point-error) (rationalp budget) (< 0 budget))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample value sigma height index step point-error)
                            (lw-mellin-node-taylor-coefficient value sigma height index step budget))
            (+ point-error (* 2 budget))))
  :hints (("Goal" :use ((:instance lw-mellin-moment-precision-adequate (error budget))
                        (:instance lw-mellin-moment-precision-at-most (error budget))
                        (:instance lw-mellin-sample-computed-moment-comparison (error budget))
                        (:instance lw-mellin-sample-cauchy
                          (left-error point-error) (right-error (lw-mellin-moment-precision value index step budget)))
                        (:instance lw-complex-difference-triangle
                          (left (lw-mellin-sample value sigma height index step point-error))
                          (middle (lw-mellin-sample value sigma height index step
                                                    (lw-mellin-moment-precision value index step budget)))
                          (right (lw-mellin-node-taylor-coefficient value sigma height index step budget))
                          (radius (+ point-error (lw-mellin-moment-precision value index step budget)))
                          (other-radius budget))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-mellin-sample value sigma height index step point-error)
                                  (lw-mellin-node-taylor-coefficient value sigma height index step budget)))
                          (radius (+ point-error (lw-mellin-moment-precision value index step budget) budget))
                          (cap (+ point-error (* 2 budget)))))
                  :in-theory (disable lw-mellin-moment-precision-adequate lw-mellin-moment-precision-at-most
                                      lw-mellin-sample-computed-moment-comparison lw-mellin-sample-cauchy
                                      lw-complex-difference-triangle))))

(defun lw-mellin-taylor-sum-raw (cells sigma height index budget)
  (if (consp cells)
      (lw-complex-add
       (lw-mellin-node-taylor-coefficient (caar cells) sigma height index (cdar cells) budget)
       (lw-mellin-taylor-sum-raw (cdr cells) sigma height index budget))
    (cons 0 0)))

(defthm lw-mellin-taylor-sum-raw-rational
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp index) (rationalp budget) (< 0 budget))
           (lw-complexp (lw-mellin-taylor-sum-raw cells sigma height index budget))))

(local (in-theory (disable lw-mellin-node-taylor-coefficient lw-mellin-taylor-sum-raw)))

(defthm lw-mellin-sum-raw-taylor-comparison
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp index) (rationalp point-error) (< 0 point-error) (rationalp budget) (< 0 budget))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sum-raw cells sigma height index point-error)
                            (lw-mellin-taylor-sum-raw cells sigma height index budget))
            (* (len cells) (+ point-error (* 2 budget)))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (e/d (lw-mellin-sum-raw lw-mellin-taylor-sum-raw)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes
                                   lw-complex-sub-add-first)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-node-taylor-comparison (value (caar cells)) (step (cdar cells)))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub
                                 (lw-mellin-sample (caar cells) sigma height index (cdar cells) point-error)
                                 (lw-mellin-node-taylor-coefficient (caar cells) sigma height index (cdar cells) budget)))
                          (radius (+ point-error (* 2 budget)))
                          (right (lw-complex-sub
                                  (lw-mellin-sum-raw (cdr cells) sigma height index point-error)
                                  (lw-mellin-taylor-sum-raw (cdr cells) sigma height index budget)))
                          (other-radius (* (len (cdr cells)) (+ point-error (* 2 budget))))))
                 :in-theory (disable lw-mellin-sum-raw lw-mellin-taylor-sum-raw
                                     lw-mellin-node-taylor-comparison lw-complex-add-disk
                                     lw-complex-add-commutative lw-complex-add-left-commutes
                                     lw-complex-sub-add-first)))))

(defun lw-mellin-taylor-coefficient (cells sigma height index error)
  (lw-mellin-taylor-sum-raw cells sigma height index (lw-mellin-sum-error cells (/ error 4))))

(defthm lw-mellin-taylor-coefficient-rational
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp index) (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-taylor-coefficient cells sigma height index error)))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (/ error 4))))
                  :in-theory (disable lw-mellin-sum-error-positive))))

(defthm lw-mellin-computed-quadrature-taylor-coefficient
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sum cells sigma height index (/ error 2))
                            (lw-mellin-taylor-coefficient cells sigma height index error))
            error))
  :hints (("Goal" :use ((:instance lw-mellin-sum-error-positive (error (/ error 2)))
                        (:instance lw-mellin-sum-error-positive (error (/ error 4)))
                        lw-mellin-sum-error-budget
                        (:instance lw-mellin-sum-raw-taylor-comparison
                          (point-error (lw-mellin-sum-error cells (/ error 2)))
                          (budget (lw-mellin-sum-error cells (/ error 4))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-mellin-sum cells sigma height index (/ error 2))
                                  (lw-mellin-taylor-coefficient cells sigma height index error)))
                          (radius (* (len cells)
                                     (+ (lw-mellin-sum-error cells (/ error 2))
                                        (* 2 (lw-mellin-sum-error cells (/ error 4)))))) (cap error)))
                  :in-theory (e/d (lw-mellin-sum lw-mellin-sum-error)
                                  (lw-mellin-sum-error-positive lw-mellin-sum-error-budget
                                   lw-mellin-sum-raw-taylor-comparison)))))
