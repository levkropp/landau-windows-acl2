(in-package "ACL2")

(include-book "mellin-sample-scaling")
(include-book "mellin-quadrature")
(include-book "mellin-partitions")

; The cell evaluator and the weighted dyadic evaluator now share one
; explicit partition, with an arithmetic comparison of their actual
; precision choices.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-mellin-sample lw-mellin-sample-kernel-form lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-kernel-weight-scale
                 lw-mellin-dyadic-sum lw-mellin-bounded-integral lw-mellin-integral-depth
                 lw-mellin-integral-precision lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                 lw-mellin-signal-spatial-slope lw-mellin-signal-spatial-cap
                 lw-kernel-spatial-slope lw-kernel-spatial-cap lw-exp-lipschitz-cap
                 lw-mellin-sum-raw lw-mellin-sum lw-mellin-sum-error
                 lw-log-signal-bounds lw-exp-bounds lw-phase-value
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mdc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mdc-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mdc-zero-times (equal (* 0 a) 0)))

(defun lw-mellin-cell-mass (cells)
  (if (consp cells) (+ (cdar cells) (lw-mellin-cell-mass (cdr cells))) 0))

(defthm lw-mellin-cell-mass-valid
  (implies (lw-mellin-cellsp cells)
           (and (rationalp (lw-mellin-cell-mass cells)) (<= 0 (lw-mellin-cell-mass cells)))))

(defthm lw-mellin-cellsp-append
  (implies (and (lw-mellin-cellsp left) (lw-mellin-cellsp right))
           (lw-mellin-cellsp (append left right))))

(defthm lw-mellin-cell-mass-append
  (implies (and (lw-mellin-cellsp left) (lw-mellin-cellsp right))
           (equal (lw-mellin-cell-mass (append left right))
                  (+ (lw-mellin-cell-mass left) (lw-mellin-cell-mass right)))))

(defun lw-mellin-weighted-sum-raw (cells sigma height index error)
  (if (consp cells)
      (lw-complex-add
       (lw-complex-scale (cdar cells) (lw-mellin-sample (caar cells) sigma height index 1 error))
       (lw-mellin-weighted-sum-raw (cdr cells) sigma height index error))
    (cons 0 0)))

(defthm lw-mellin-weighted-sum-rational
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-weighted-sum-raw cells sigma height index error))))

(defthm lw-mellin-weighted-sum-append
  (implies (and (lw-mellin-cellsp left) (lw-mellin-cellsp right)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (equal (lw-mellin-weighted-sum-raw (append left right) sigma height index error)
                  (lw-complex-add (lw-mellin-weighted-sum-raw left sigma height index error)
                                  (lw-mellin-weighted-sum-raw right sigma height index error)))))

(local (in-theory (disable lw-mellin-weighted-sum-raw lw-mellin-cell-mass)))


(defthm lw-mellin-cell-weighted-comparison
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp (lw-complex-sub (lw-mellin-sum-raw cells sigma height index left-error) (lw-mellin-weighted-sum-raw cells sigma height index right-error))
                             (+ (* (len cells) left-error) (* (lw-mellin-cell-mass cells) right-error))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (e/d (lw-mellin-sum-raw lw-mellin-weighted-sum-raw lw-mellin-cell-mass)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))
          (and stable-under-simplificationp
               '(:use (
                 (:instance lw-mellin-sample-step-scaling (value (caar cells)) (step (cdar cells)))
                 (:instance lw-complex-add-disk
                   (left
                     (lw-complex-sub
                       (lw-mellin-sample (caar cells) sigma height index (cdar cells) left-error)
                       (lw-complex-scale
                         (cdar cells)
                         (lw-mellin-sample (caar cells) sigma height index 1 right-error))))
                   (right
                     (lw-complex-sub
                       (lw-mellin-sum-raw (cdr cells) sigma height index left-error)
                       (lw-mellin-weighted-sum-raw (cdr cells) sigma height index right-error)))
                   (radius (+ left-error (* (cdar cells) right-error)))
                   (other-radius
                     (+ (* (len (cdr cells)) left-error) (* (lw-mellin-cell-mass (cdr cells)) right-error)))))
                 :in-theory (disable lw-mellin-sum-raw lw-mellin-weighted-sum-raw
                                     lw-mellin-sample-step-scaling lw-complex-add-disk
                                     lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))))

(defun lw-mellin-dyadic-cells (start end depth)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (list (cons start (- end start)))
    (let ((middle (/ (+ start end) 2)))
      (append (lw-mellin-dyadic-cells start middle (- depth 1))
              (lw-mellin-dyadic-cells middle end (- depth 1))))))

(defthm lw-mellin-dyadic-cells-valid
  (implies (and (rationalp start) (<= 0 start) (rationalp end) (<= start end) (natp depth))
           (and (lw-mellin-cellsp (lw-mellin-dyadic-cells start end depth))
                (equal (lw-mellin-cell-mass (lw-mellin-dyadic-cells start end depth)) (- end start))))
  :hints (("Goal" :induct (lw-mellin-dyadic-cells start end depth)
                  :in-theory (enable lw-mellin-cell-mass))))

(defthm lw-mellin-dyadic-cells-weighted-value
  (implies (and (rationalp start) (<= 0 start) (rationalp end) (<= start end) (natp depth)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (equal (lw-mellin-weighted-sum-raw (lw-mellin-dyadic-cells start end depth) sigma height index error)
                  (lw-mellin-dyadic-sum start end depth sigma height index error)))
  :hints (("Goal" :induct (lw-mellin-dyadic-cells start end depth)
                  :in-theory (enable lw-mellin-dyadic-sum lw-mellin-weighted-sum-raw))))

(local (in-theory (disable lw-mellin-dyadic-cells)))

(defthm lw-mellin-dyadic-cell-quadrature-comparison
  (implies (and (rationalp start) (<= 0 start) (rationalp end) (<= start end) (natp depth)
                (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sum (lw-mellin-dyadic-cells start end depth) sigma height index left-error)
               (lw-mellin-dyadic-sum start end depth sigma height index right-error))
             (+ left-error (* (- end start) right-error))))
  :hints (("Goal" :use (
    lw-mellin-dyadic-cells-valid
    (:instance lw-mellin-sum-error-positive (cells (lw-mellin-dyadic-cells start end depth)) (error left-error))
    (:instance lw-mellin-sum-error-budget (cells (lw-mellin-dyadic-cells start end depth)) (error left-error))
    (:instance lw-mellin-cell-weighted-comparison
      (cells (lw-mellin-dyadic-cells start end depth))
      (left-error (lw-mellin-sum-error (lw-mellin-dyadic-cells start end depth) left-error)))
    (:instance lw-mellin-dyadic-cells-weighted-value (error right-error))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sum (lw-mellin-dyadic-cells start end depth) sigma height index left-error)
          (lw-mellin-dyadic-sum start end depth sigma height index right-error)))
      (radius
        (+
          (*
            (len (lw-mellin-dyadic-cells start end depth))
            (lw-mellin-sum-error (lw-mellin-dyadic-cells start end depth) left-error))
          (* (- end start) right-error)))
      (cap (+ left-error (* (- end start) right-error)))))
    :in-theory (e/d (lw-mellin-sum)
                    (lw-mellin-sum-error-positive lw-mellin-sum-error-budget
                     lw-mellin-cell-weighted-comparison)))))


(local (defthm lw-mdc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mdc-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mdc-mesh-data
         (implies (and (rationalp width) (<= 0 width) (natp depth))
                  (and (rationalp (lw-halved-width width depth)) (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable lw-halved-width)))))

(defthm lw-mellin-dyadic-cell-bounded-comparison
  (implies (and (rationalp cap) (<= 0 cap) (natp depth) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sum (lw-mellin-dyadic-cells 0 cap depth) sigma height index left-error)
               (lw-mellin-bounded-integral cap sigma height index right-error))
             (+
               left-error
               (* cap (lw-mellin-spatial-slope cap sigma height 1) (lw-halved-width cap depth))
               right-error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-spatial-parameters (step 1))
    (:instance lw-mellin-integral-depth-adequate (error right-error))
    (:instance lw-mellin-integral-precision-valid (error right-error))
    (:instance lw-mdc-product-nonnegative (a cap) (b (lw-mellin-integral-precision cap right-error)))
    (:instance lw-mdc-multiply-order
      (a 1)
      (b (lw-mellin-spatial-error-factor cap 1))
      (factor (* cap (lw-mellin-integral-precision cap right-error))))
    (:instance lw-mellin-dyadic-cell-quadrature-comparison
      (start 0)
      (end cap)
      (right-error (lw-mellin-integral-precision cap right-error)))
    (:instance lw-mellin-dyadic-cross-depth
      (left-depth depth)
      (right-depth (lw-mellin-integral-depth cap sigma height right-error))
      (left-error (lw-mellin-integral-precision cap right-error))
      (right-error (lw-mellin-integral-precision cap right-error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-sum (lw-mellin-dyadic-cells 0 cap depth) sigma height index left-error))
      (middle
        (lw-mellin-dyadic-sum 0 cap depth sigma height index (lw-mellin-integral-precision cap right-error)))
      (right (lw-mellin-bounded-integral cap sigma height index right-error))
      (radius (+ left-error (* cap (lw-mellin-integral-precision cap right-error))))
      (other-radius
        (*
          cap
          (+
            (*
              (lw-mellin-spatial-slope cap sigma height 1)
              (+
                (lw-halved-width cap depth)
                (lw-halved-width cap (lw-mellin-integral-depth cap sigma height right-error))))
            (*
              (lw-mellin-spatial-error-factor cap 1)
              (+
                (lw-mellin-integral-precision cap right-error)
                (lw-mellin-integral-precision cap right-error)))))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sum (lw-mellin-dyadic-cells 0 cap depth) sigma height index left-error)
          (lw-mellin-bounded-integral cap sigma height index right-error)))
      (radius
        (+
          (+ left-error (* cap (lw-mellin-integral-precision cap right-error)))
          (*
            cap
            (+
              (*
                (lw-mellin-spatial-slope cap sigma height 1)
                (+
                  (lw-halved-width cap depth)
                  (lw-halved-width cap (lw-mellin-integral-depth cap sigma height right-error))))
              (*
                (lw-mellin-spatial-error-factor cap 1)
                (+
                  (lw-mellin-integral-precision cap right-error)
                  (lw-mellin-integral-precision cap right-error)))))))
      (cap
        (+
          left-error
          (* cap (lw-mellin-spatial-slope cap sigma height 1) (lw-halved-width cap depth))
          right-error))))
    :in-theory (e/d (lw-mellin-bounded-integral)
                    (lw-mellin-spatial-parameters lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                     lw-mellin-dyadic-cell-quadrature-comparison lw-mellin-dyadic-cross-depth
                     lw-complex-difference-triangle lw-halved-width)))))

(defthm lw-mellin-canonical-cell-bounded-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sum
                 (lw-mellin-dyadic-cells 0 cap (lw-mellin-integral-depth cap sigma height right-error))
                 sigma
                 height
                 index
                 left-error)
               (lw-mellin-bounded-integral cap sigma height index right-error))
             (+ left-error (* 1/4 right-error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-spatial-parameters (step 1))
    (:instance lw-mellin-integral-depth-adequate (error right-error))
    (:instance lw-mellin-integral-precision-valid (error right-error))
    (:instance lw-mdc-product-nonnegative (a cap) (b (lw-mellin-integral-precision cap right-error)))
    (:instance lw-mdc-multiply-order
      (a 1)
      (b (lw-mellin-spatial-error-factor cap 1))
      (factor (* cap (lw-mellin-integral-precision cap right-error))))
    (:instance lw-mellin-dyadic-cell-quadrature-comparison
      (start 0)
      (end cap)
      (depth (lw-mellin-integral-depth cap sigma height right-error))
      (right-error (lw-mellin-integral-precision cap right-error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sum
            (lw-mellin-dyadic-cells 0 cap (lw-mellin-integral-depth cap sigma height right-error))
            sigma
            height
            index
            left-error)
          (lw-mellin-bounded-integral cap sigma height index right-error)))
      (radius (+ left-error (* cap (lw-mellin-integral-precision cap right-error))))
      (cap (+ left-error (* 1/4 right-error)))))
    :in-theory (e/d (lw-mellin-bounded-integral)
                    (lw-mellin-spatial-parameters lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                     lw-mellin-dyadic-cell-quadrature-comparison)))))

; A non-unit cell width exercises the exact cell/weighted partition link.
(assert-event
 (and (equal (lw-mellin-dyadic-cells 0 3 1) (list (cons 0 3/2) (cons 3/2 3/2)))
      (equal (lw-mellin-cell-mass (lw-mellin-dyadic-cells 0 3 2)) 3)))

