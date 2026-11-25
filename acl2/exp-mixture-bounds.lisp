(in-package "ACL2")

(include-book "exp-polynomials")

; Choose a common polynomial degree for all nodes. The error bound is
; uniform on the input disk, with both truncation and node precision paid.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-power lw-complex-power-add lw-complex-power-power
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value
                 lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-band lw-exp-index
                 lw-exp-bounds lw-complex-polynomial lw-exp-mixture-coefficients
                 lw-exp-mixture-taylor-value lw-exp-mixture-block lw-exp-mixture-coefficient
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-xmb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-xmb-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-xmb-zero-times (equal (* 0 a) 0)))
(local (defthm lw-xmb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-xmb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(defthm lw-exp-index-later-tail-budget
  (implies (and (rationalp radius) (<= 0 radius) (rationalp error) (< 0 error) (natp degree)
                (<= (lw-exp-index radius error) degree))
           (<= (* 2 (lw-exp-term radius (+ 1 degree))) error))
  :hints (("Goal" :use ((:instance lw-exp-index-adequate (value radius) (epsilon error))
                        lw-exp-index-tail-budget
                        (:instance lw-exp-band-nested
                          (value radius) (small (lw-exp-index radius error)) (large degree)))
                  :in-theory (e/d (lw-exp-band)
                                  (lw-exp-index-adequate lw-exp-index-tail-budget)))))

(defun lw-exp-mixture-node-precision (base budget)
  (/ budget (* 2 (+ 1 (lw-complex-l1 base)))))

(defthm lw-exp-mixture-node-precision-adequate
  (implies (and (lw-complexp base) (rationalp budget) (< 0 budget))
           (and (rationalp (lw-exp-mixture-node-precision base budget))
                (< 0 (lw-exp-mixture-node-precision base budget))
                (<= (* 2 (lw-complex-l1 base) (lw-exp-mixture-node-precision base budget)) budget)))
  :hints (("Goal" :use ((:instance lw-complex-l1-bound (point base))
                        (:instance lw-positive-division-bound
                          (numerator (* 2 (lw-complex-l1 base) budget))
                          (divisor (* 2 (+ 1 (lw-complex-l1 base)))) (bound budget)))
                  :in-theory (disable lw-complex-l1-bound) :nonlinearp t)))

(local (in-theory (disable lw-exp-mixture-node-precision)))

(defthm lw-exp-mixture-node-tail
  (implies (and (rationalp value) (<= 0 value) (lw-complexp base)
                (lw-complex-diskp point radius) (rationalp budget) (< 0 budget) (natp degree)
                (<= (lw-exp-index (* value radius) (lw-exp-mixture-node-precision base budget)) degree))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-mul base (lw-complex-exp-sum (lw-complex-scale value point) degree))
             (lw-complex-mul base (lw-complex-exp-value
                                  (lw-complex-scale value point) (lw-exp-mixture-node-precision base budget))))
            budget))
  :hints (("Goal" :use (lw-exp-mixture-node-precision-adequate
                        (:instance lw-complex-l1-bound (point base))
                        (:instance lw-complex-scale-disk (factor value))
                        (:instance lw-exp-index-adequate
                          (value (* value radius)) (epsilon (lw-exp-mixture-node-precision base budget)))
                        (:instance lw-exp-index-later-tail-budget
                          (radius (* value radius)) (error (lw-exp-mixture-node-precision base budget)))
                        (:instance lw-complex-exp-prefix-error
                          (point (lw-complex-scale value point)) (radius (* value radius))
                          (small degree) (error (lw-exp-mixture-node-precision base budget)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-exp-sum (lw-complex-scale value point) degree)
                                  (lw-complex-exp-value (lw-complex-scale value point)
                                                        (lw-exp-mixture-node-precision base budget))))
                          (radius (+ (* 2 (lw-exp-term (* value radius) (+ 1 degree)))
                                     (lw-exp-mixture-node-precision base budget)))
                          (cap (* 2 (lw-exp-mixture-node-precision base budget))))
                        (:instance lw-complex-mul-disk
                          (left base) (radius (lw-complex-l1 base))
                          (right (lw-complex-sub
                                  (lw-complex-exp-sum (lw-complex-scale value point) degree)
                                  (lw-complex-exp-value (lw-complex-scale value point)
                                                        (lw-exp-mixture-node-precision base budget))))
                          (other-radius (* 2 (lw-exp-mixture-node-precision base budget))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-complex-mul base (lw-complex-exp-sum (lw-complex-scale value point) degree))
                                  (lw-complex-mul base (lw-complex-exp-value
                                                       (lw-complex-scale value point)
                                                       (lw-exp-mixture-node-precision base budget)))))
                          (radius (* 2 (lw-complex-l1 base) (lw-exp-mixture-node-precision base budget)))
                          (cap budget)))
                  :in-theory (disable lw-exp-mixture-node-precision-adequate lw-complex-l1-bound
                                      lw-complex-scale-disk lw-exp-index-adequate lw-exp-index-later-tail-budget
                                      lw-complex-exp-prefix-error lw-complex-mul-disk
                                      lw-complex-mul-commutative lw-complex-mul-left-commutes)
                  :nonlinearp t)))

(defun lw-exp-mixture-degree-raw (nodes radius budget)
  (if (consp nodes)
      (max (lw-exp-index (* (caar nodes) radius) (lw-exp-mixture-node-precision (cdar nodes) budget))
           (lw-exp-mixture-degree-raw (cdr nodes) radius budget))
    0))

(defthm lw-exp-mixture-degree-raw-natural
  (implies (and (lw-exp-mixturep nodes) (rationalp radius) (<= 0 radius)
                (rationalp budget) (< 0 budget))
           (natp (lw-exp-mixture-degree-raw nodes radius budget)))
  :hints (("Goal" :induct (lw-exp-mixturep nodes))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-mixture-node-precision-adequate (base (cdar nodes)))
                        (:instance lw-exp-index-adequate
                          (value (* (caar nodes) radius))
                          (epsilon (lw-exp-mixture-node-precision (cdar nodes) budget))))
                 :in-theory (disable lw-exp-mixture-node-precision-adequate lw-exp-index-adequate)
                 :nonlinearp t))))

(defun lw-exp-mixture-value (nodes point budget)
  (if (consp nodes)
      (lw-complex-add
       (lw-complex-mul (cdar nodes)
                        (lw-complex-exp-value (lw-complex-scale (caar nodes) point)
                                              (lw-exp-mixture-node-precision (cdar nodes) budget)))
       (lw-exp-mixture-value (cdr nodes) point budget))
    (cons 0 0)))

(defthm lw-exp-mixture-value-rational
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (rationalp budget) (< 0 budget))
           (lw-complexp (lw-exp-mixture-value nodes point budget)))
  :hints (("Goal" :induct (lw-exp-mixturep nodes))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-mixture-node-precision-adequate (base (cdar nodes))))
                 :in-theory (disable lw-exp-mixture-node-precision-adequate)))))

(defthm lw-exp-mixture-taylor-value-rational
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp degree))
           (lw-complexp (lw-exp-mixture-taylor-value nodes point degree)))
  :hints (("Goal" :induct (lw-exp-mixturep nodes)
                  :in-theory (enable lw-exp-mixture-taylor-value))))

(defthm lw-exp-mixture-uniform-tail-raw
  (implies (and (lw-exp-mixturep nodes) (lw-complex-diskp point radius)
                (rationalp budget) (< 0 budget) (natp degree)
                (<= (lw-exp-mixture-degree-raw nodes radius budget) degree))
           (lw-complex-diskp
            (lw-complex-sub (lw-exp-mixture-taylor-value nodes point degree)
                            (lw-exp-mixture-value nodes point budget))
            (* (len nodes) budget)))
  :hints (("Goal" :induct (lw-exp-mixturep nodes)
                  :in-theory (e/d (lw-exp-mixture-taylor-value)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes
                                   lw-complex-sub-add-first)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-mixture-node-tail (value (caar nodes)) (base (cdar nodes)))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub
                                 (lw-complex-mul (cdar nodes)
                                   (lw-complex-exp-sum (lw-complex-scale (caar nodes) point) degree))
                                 (lw-complex-mul (cdar nodes)
                                   (lw-complex-exp-value (lw-complex-scale (caar nodes) point)
                                                         (lw-exp-mixture-node-precision (cdar nodes) budget)))))
                          (radius budget)
                          (right (lw-complex-sub
                                  (lw-exp-mixture-taylor-value (cdr nodes) point degree)
                                  (lw-exp-mixture-value (cdr nodes) point budget)))
                          (other-radius (* (len (cdr nodes)) budget))))
                 :in-theory (disable lw-exp-mixture-taylor-value lw-exp-mixture-value
                                     lw-complex-add-commutative lw-complex-add-left-commutes
                                     lw-complex-sub-add-first lw-exp-mixture-node-tail lw-complex-add-disk)))))

(defun lw-exp-mixture-budget (nodes error) (/ error (+ 1 (len nodes))))

(defthm lw-exp-mixture-budget-positive
  (implies (and (rationalp error) (< 0 error))
           (and (rationalp (lw-exp-mixture-budget nodes error)) (< 0 (lw-exp-mixture-budget nodes error))))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-exp-mixture-budget-adequate
  (implies (and (rationalp error) (< 0 error))
           (<= (* (len nodes) (lw-exp-mixture-budget nodes error)) error))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* (len nodes) error)) (divisor (+ 1 (len nodes))) (bound error))))))

(defun lw-exp-mixture-degree (nodes radius target error)
  (max (nfix target) (lw-exp-mixture-degree-raw nodes radius (lw-exp-mixture-budget nodes error))))

(defthm lw-exp-mixture-degree-data
  (implies (and (lw-exp-mixturep nodes) (rationalp radius) (<= 0 radius)
                (natp target) (rationalp error) (< 0 error))
           (and (natp (lw-exp-mixture-degree nodes radius target error))
                (<= target (lw-exp-mixture-degree nodes radius target error))
                (<= (lw-exp-mixture-degree-raw nodes radius (lw-exp-mixture-budget nodes error))
                    (lw-exp-mixture-degree nodes radius target error))))
  :hints (("Goal" :use (lw-exp-mixture-budget-positive)
                  :in-theory (disable lw-exp-mixture-budget lw-exp-mixture-budget-positive))))


(local (in-theory (disable lw-exp-mixture-degree lw-exp-mixture-degree-raw lw-exp-mixture-budget
                           lw-exp-mixture-value)))

(defthm lw-exp-mixture-computed-uniform-polynomial
  (implies (and (lw-exp-mixturep nodes) (lw-complex-diskp point radius)
                (natp target) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-complex-polynomial
              (lw-exp-mixture-coefficients nodes 0 (+ 1 (lw-exp-mixture-degree nodes radius target error))) point 0)
             (lw-exp-mixture-value nodes point (lw-exp-mixture-budget nodes error))) error))
  :hints (("Goal" :use (lw-exp-mixture-degree-data lw-exp-mixture-budget-positive
                        lw-exp-mixture-budget-adequate
                        (:instance lw-exp-mixture-uniform-tail-raw
                          (degree (lw-exp-mixture-degree nodes radius target error))
                          (budget (lw-exp-mixture-budget nodes error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-exp-mixture-taylor-value nodes point
                                                               (lw-exp-mixture-degree nodes radius target error))
                                  (lw-exp-mixture-value nodes point (lw-exp-mixture-budget nodes error))))
                          (radius (* (len nodes) (lw-exp-mixture-budget nodes error))) (cap error)))
                  :in-theory (disable lw-exp-mixture-degree-data lw-exp-mixture-budget-positive
                                      lw-exp-mixture-budget-adequate lw-exp-mixture-uniform-tail-raw))))
