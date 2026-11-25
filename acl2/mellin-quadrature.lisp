(in-package "ACL2")

(include-book "mellin-integrand")

; A cell is (log-abscissa . nonnegative-weight). This book bounds the
; evaluation error on a fixed finite weighted grid. The error between the
; exact weighted sum and the improper integral is a separate obligation.
(defun lw-mellin-cellsp (cells)
  (if (consp cells)
      (and (consp (car cells)) (rationalp (caar cells)) (<= 0 (caar cells))
           (rationalp (cdar cells)) (<= 0 (cdar cells)) (lw-mellin-cellsp (cdr cells)))
    (equal cells nil)))

(defun lw-mellin-sum-raw (cells sigma height index point-error)
  (if (consp cells)
      (lw-complex-add (lw-mellin-sample (caar cells) sigma height index (cdar cells) point-error)
                      (lw-mellin-sum-raw (cdr cells) sigma height index point-error))
    (cons 0 0)))

(defun lw-mellin-sum-error (cells error) (/ error (+ 1 (len cells))))
(defun lw-mellin-sum (cells sigma height index error)
  (lw-mellin-sum-raw cells sigma height index (lw-mellin-sum-error cells error)))

(defun lw-mellin-sum-check (cells sigma index point-error)
  (if (consp cells)
      (and (lw-mellin-sample-check (caar cells) sigma index (cdar cells) point-error)
           (lw-mellin-sum-check (cdr cells) sigma index point-error))
    (equal cells nil)))

(local (defthm lw-mq-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mq-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mq-zero-product (equal (* 0 value) 0)))
(local (defthm lw-mq-minus-one-product
         (implies (rationalp value) (equal (* -1 value) (- value)))))
(local (defthm lw-mq-add-cancel
         (implies (and (rationalp value) (rationalp rest))
                  (equal (+ value (- value) rest) rest))))
(local (defthm lw-mq-sum-left-distribute
         (implies (and (rationalp left) (rationalp right) (rationalp factor))
                  (equal (* (+ left right) factor) (+ (* left factor) (* right factor))))
         :hints (("Goal" :use ((:instance distributivity (x factor) (y left) (z right)))
                         :in-theory (disable distributivity)))))

(local (in-theory (disable lw-mellin-sample lw-complexp lw-complex-add lw-complex-sub lw-complex-diskp
                           lw-complex-disk-enlarge lw-disk-enlarge)))

(defthm lw-mellin-sum-error-positive
  (implies (and (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-sum-error cells error)) (< 0 (lw-mellin-sum-error cells error))))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-mellin-sum-check-valid
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma)
                (rationalp point-error) (< 0 point-error))
           (lw-mellin-sum-check cells sigma index point-error))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (disable lw-mellin-sample-check))))

(defthm lw-mellin-sum-raw-rational
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp point-error) (< 0 point-error))
           (lw-complexp (lw-mellin-sum-raw cells sigma height index point-error)))
  :hints (("Goal" :induct (lw-mellin-cellsp cells)
                  :in-theory (enable lw-complexp lw-complex-add))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-sample-rational
                          (value (caar cells)) (step (cdar cells)) (error point-error)))
                 :in-theory (e/d (lw-complexp lw-complex-add)
                                 (lw-mellin-sample-rational))))))

(local
 (defthm lw-mq-sub-add-identity
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
            (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                   (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d))))
   :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))
   :rule-classes nil))

(local
 (defthm lw-mq-add-difference-bound
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                 (lw-complex-diskp (lw-complex-sub a c) radius)
                 (lw-complex-diskp (lw-complex-sub b d) other-radius))
            (lw-complex-diskp (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d)) (+ radius other-radius)))
   :hints (("Goal" :use (lw-mq-sub-add-identity
                         (:instance lw-complex-add-disk (left (lw-complex-sub a c)) (right (lw-complex-sub b d))))
                   :in-theory (disable lw-complex-add-disk)))
   :rule-classes nil))

(defthm lw-mellin-sum-raw-cauchy
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sum-raw cells sigma height index left-error)
                            (lw-mellin-sum-raw cells sigma height index right-error))
            (* (len cells) (+ left-error right-error))))
  :hints (("Goal" :induct (lw-mellin-cellsp cells))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-sample-cauchy (value (caar cells)) (step (cdar cells)))
                       (:instance lw-mellin-sample-rational (value (caar cells)) (step (cdar cells)) (error left-error))
                       (:instance lw-mellin-sample-rational (value (caar cells)) (step (cdar cells)) (error right-error))
                       (:instance lw-mellin-sum-raw-rational (cells (cdr cells)) (point-error left-error))
                       (:instance lw-mellin-sum-raw-rational (cells (cdr cells)) (point-error right-error))
                       (:instance lw-mq-add-difference-bound
                         (a (lw-mellin-sample (caar cells) sigma height index (cdar cells) left-error))
                         (b (lw-mellin-sum-raw (cdr cells) sigma height index left-error))
                         (c (lw-mellin-sample (caar cells) sigma height index (cdar cells) right-error))
                         (d (lw-mellin-sum-raw (cdr cells) sigma height index right-error))
                         (radius (+ left-error right-error)) (other-radius (* (len (cdr cells)) (+ left-error right-error)))))
                 :in-theory (disable lw-mellin-sum-raw lw-mellin-sum-raw-rational lw-mellin-sample-cauchy
                                     lw-mellin-sample-rational)))))

(defthm lw-mellin-sum-error-budget
  (implies (and (rationalp error) (< 0 error))
           (<= (* (len cells) (lw-mellin-sum-error cells error)) error))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* (len cells) error)) (divisor (+ 1 (len cells))) (bound error)))
                  :nonlinearp t)))

(defthm lw-mellin-sum-constructor-check
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma)
                (rationalp error) (< 0 error))
           (lw-mellin-sum-check cells sigma index (lw-mellin-sum-error cells error)))
  :hints (("Goal" :use (lw-mellin-sum-error-positive
                        (:instance lw-mellin-sum-check-valid (point-error (lw-mellin-sum-error cells error))))
                  :in-theory (disable lw-mellin-sum-check lw-mellin-sum-error
                                      lw-mellin-sum-error-positive lw-mellin-sum-check-valid))))

(defthm lw-mellin-sum-rational
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-sum cells sigma height index error)))
  :hints (("Goal" :use (lw-mellin-sum-error-positive
                        (:instance lw-mellin-sum-raw-rational (point-error (lw-mellin-sum-error cells error))))
                  :in-theory (disable lw-mellin-sum-raw lw-mellin-sum-error
                                      lw-mellin-sum-error-positive lw-mellin-sum-raw-rational))))

(defthm lw-mellin-sum-cauchy
  (implies (and (lw-mellin-cellsp cells) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sum cells sigma height index left-error)
                            (lw-mellin-sum cells sigma height index right-error)) (+ left-error right-error)))
  :hints (("Goal"
           :use ((:instance lw-mellin-sum-error-positive (error left-error))
                 (:instance lw-mellin-sum-error-positive (error right-error))
                 (:instance lw-mellin-sum-error-budget (error left-error))
                 (:instance lw-mellin-sum-error-budget (error right-error))
                 (:instance lw-mellin-sum-raw-cauchy
                   (left-error (lw-mellin-sum-error cells left-error)) (right-error (lw-mellin-sum-error cells right-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-sum cells sigma height index left-error)
                                          (lw-mellin-sum cells sigma height index right-error)))
                   (radius (* (len cells) (+ (lw-mellin-sum-error cells left-error) (lw-mellin-sum-error cells right-error))))
                   (cap (+ left-error right-error))))
           :in-theory (disable lw-mellin-sum-raw lw-mellin-sum-error lw-mellin-sum-error-positive
                               lw-mellin-sum-error-budget lw-mellin-sum-raw-cauchy))))

(assert-event
 (and (equal (lw-mellin-sum nil 252 0 3 1/100) (cons 0 0))
      (lw-mellin-cellsp '((0 . 1/4) (1/4 . 1/4) (1/2 . 1/4)))
      (<= (* 3 (lw-mellin-sum-error '((0 . 1/4) (1/4 . 1/4) (1/2 . 1/4)) 1/100)) 1/100)))
