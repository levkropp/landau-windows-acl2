(in-package "ACL2")

(include-book "complex-exp")

; Explicit polynomial coefficients for finite mixtures of exponentials.
; A node is (nonnegative-rational-abscissa . rational-complex-amplitude).

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-scale-add lw-complex-scale-product
                 lw-complex-power lw-complex-power-add lw-complex-power-power
                 lw-complex-exp-term lw-complex-exp-sum lw-complex-exp-value
                 lw-complex-l1 lw-exp-term lw-exp-sum lw-exp-band lw-exp-index
                 lw-exp-bounds lw-complex-polynomial)))

(local (defthm lw-xp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-xp-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-xp-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-xp-zero-times (equal (* 0 a) 0)))
(local (defthm lw-xp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-xp-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-xp-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defun lw-xp-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-xp-countdown (- index 1)))))

(local (defthm lw-xp-term-zero
         (implies (zp index) (equal (lw-complex-exp-term point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-term)))))
(local (defthm lw-xp-sum-zero
         (implies (zp index) (equal (lw-complex-exp-sum point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-exp-sum)))))

(defun lw-complex-exp-block (point offset count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-exp-term point offset)
     (lw-complex-exp-block point (+ 1 offset) (- count 1)))))

(defthm lw-complex-exp-block-rational
  (implies (and (lw-complexp point) (natp offset) (natp count))
           (lw-complexp (lw-complex-exp-block point offset count))))

(local (defthm lw-xp-block-zero
         (implies (zp count) (equal (lw-complex-exp-block point offset count) (cons 0 0)))))

(defthm lw-complex-exp-block-last
  (implies (and (lw-complexp point) (natp offset) (natp count))
           (equal (lw-complex-exp-block point offset (+ 1 count))
                  (lw-complex-add (lw-complex-exp-term point (+ offset count))
                                  (lw-complex-exp-block point offset count))))
  :hints (("Goal" :induct (lw-complex-exp-block point offset count)
                  :expand ((lw-complex-exp-block point offset (+ 1 count))
                           (lw-complex-exp-block point offset 1)))))

(defthm lw-complex-exp-block-prefix
  (implies (and (lw-complexp point) (natp degree))
           (equal (lw-complex-exp-block point 0 (+ 1 degree)) (lw-complex-exp-sum point degree)))
  :hints (("Goal" :induct (lw-xp-countdown degree)
                  :expand ((lw-complex-exp-sum point degree) (lw-complex-exp-block point 0 1))
                  :in-theory (disable lw-complex-exp-block))))

(defun lw-exp-mixturep (nodes)
  (if (consp nodes)
      (and (consp (car nodes)) (rationalp (caar nodes)) (<= 0 (caar nodes))
           (lw-complexp (cdar nodes)) (lw-exp-mixturep (cdr nodes)))
    (equal nodes nil)))

(defun lw-exp-mixture-coefficient (nodes index)
  (if (consp nodes)
      (lw-complex-add (lw-complex-scale (lw-exp-term (caar nodes) index) (cdar nodes))
                      (lw-exp-mixture-coefficient (cdr nodes) index))
    (cons 0 0)))

(defthm lw-exp-mixture-coefficient-rational
  (implies (and (lw-exp-mixturep nodes) (natp index))
           (lw-complexp (lw-exp-mixture-coefficient nodes index))))

(defun lw-exp-mixture-coefficients (nodes offset count)
  (if (zp count) nil
    (cons (lw-exp-mixture-coefficient nodes offset)
          (lw-exp-mixture-coefficients nodes (+ 1 offset) (- count 1)))))

(defthm lw-exp-mixture-coefficients-valid
  (implies (and (lw-exp-mixturep nodes) (natp offset) (natp count))
           (and (lw-complex-coefficientsp (lw-exp-mixture-coefficients nodes offset count))
                (equal (len (lw-exp-mixture-coefficients nodes offset count)) count))))

(local (defun lw-xp-coefficient-induct (offset count index)
         (declare (xargs :measure (nfix count)))
         (if (or (zp count) (zp index)) (list offset index)
           (lw-xp-coefficient-induct (+ 1 offset) (- count 1) (- index 1)))))

(defthm lw-exp-mixture-coefficient-nth
  (implies (and (lw-exp-mixturep nodes) (natp offset) (natp count) (natp index) (< index count))
           (equal (nth index (lw-exp-mixture-coefficients nodes offset count))
                  (lw-exp-mixture-coefficient nodes (+ offset index))))
  :hints (("Goal" :induct (lw-xp-coefficient-induct offset count index)
                  :expand ((lw-exp-mixture-coefficients nodes offset count))
                  :in-theory (enable nth))))

(defun lw-exp-mixture-block (nodes point offset count)
  (if (consp nodes)
      (lw-complex-add
       (lw-complex-mul (cdar nodes) (lw-complex-exp-block (lw-complex-scale (caar nodes) point) offset count))
       (lw-exp-mixture-block (cdr nodes) point offset count))
    (cons 0 0)))

(defthm lw-exp-mixture-block-rational
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp offset) (natp count))
           (lw-complexp (lw-exp-mixture-block nodes point offset count))))

(defthm lw-exp-mixture-block-zero
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp offset))
           (equal (lw-exp-mixture-block nodes point offset 0) (cons 0 0))))

(local (defthm lw-xp-mul-scale-swap
         (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-mul (lw-complex-scale factor a) b)
                         (lw-complex-mul a (lw-complex-scale factor b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-scale)))
         :rule-classes nil))

(local (defthm lw-xp-add-pair-substitution
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (lw-complexp d) (lw-complexp e)
                       (equal b (lw-complex-add c d)))
                  (equal (lw-complex-add b (lw-complex-add a e))
                         (lw-complex-add c (lw-complex-add d (lw-complex-add a e)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))
         :rule-classes nil))

(defthm lw-exp-mixture-block-first
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp offset) (posp count))
           (equal
            (lw-exp-mixture-block nodes point offset count)
            (lw-complex-add
             (lw-complex-mul (lw-exp-mixture-coefficient nodes offset) (lw-complex-power point offset))
             (lw-exp-mixture-block nodes point (+ 1 offset) (- count 1)))))
  :hints (("Goal" :induct (lw-exp-mixturep nodes)
                  :in-theory (disable lw-complex-mul-commutative lw-complex-mul-left-commutes))
          (and stable-under-simplificationp
               '(:use ((:instance lw-xp-mul-scale-swap
                          (factor (lw-exp-term (caar nodes) offset))
                          (a (cdar nodes)) (b (lw-complex-power point offset)))
                        (:instance lw-xp-add-pair-substitution
                          (a (lw-complex-mul (cdar nodes)
                               (lw-complex-scale (lw-exp-term (caar nodes) offset) (lw-complex-power point offset))))
                          (b (lw-exp-mixture-block (cdr nodes) point offset count))
                          (c (lw-complex-mul (lw-exp-mixture-coefficient (cdr nodes) offset) (lw-complex-power point offset)))
                          (d (lw-exp-mixture-block (cdr nodes) point (+ 1 offset) (- count 1)))
                          (e (lw-complex-mul (cdar nodes)
                               (lw-complex-exp-block (lw-complex-scale (caar nodes) point) (+ 1 offset) (- count 1))))))
                 :in-theory (disable lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(defthm lw-exp-mixture-polynomial-block
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp offset) (natp count))
           (equal (lw-complex-polynomial (lw-exp-mixture-coefficients nodes offset count) point offset)
                  (lw-exp-mixture-block nodes point offset count)))
  :hints (("Goal" :induct (lw-exp-mixture-coefficients nodes offset count)
                  :in-theory (e/d (lw-complex-polynomial)
                                  (lw-exp-mixture-block lw-exp-mixture-coefficient)))
          (and stable-under-simplificationp
               '(:use (lw-exp-mixture-block-first)
                 :in-theory (disable lw-exp-mixture-block-first lw-exp-mixture-block
                                     lw-exp-mixture-coefficient lw-complex-polynomial)))))

(defun lw-exp-mixture-taylor-value (nodes point degree)
  (if (consp nodes)
      (lw-complex-add
       (lw-complex-mul (cdar nodes) (lw-complex-exp-sum (lw-complex-scale (caar nodes) point) degree))
       (lw-exp-mixture-taylor-value (cdr nodes) point degree))
    (cons 0 0)))

(defthm lw-exp-mixture-prefix-value
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp degree))
           (equal (lw-exp-mixture-block nodes point 0 (+ 1 degree))
                  (lw-exp-mixture-taylor-value nodes point degree)))
  :hints (("Goal" :induct (lw-exp-mixturep nodes)
                  :in-theory (disable lw-complex-exp-block lw-exp-mixture-block-first))))

(defthm lw-exp-mixture-polynomial-value
  (implies (and (lw-exp-mixturep nodes) (lw-complexp point) (natp degree))
           (equal (lw-complex-polynomial (lw-exp-mixture-coefficients nodes 0 (+ 1 degree)) point 0)
                  (lw-exp-mixture-taylor-value nodes point degree)))
  :hints (("Goal" :in-theory (disable lw-exp-mixture-block lw-exp-mixture-taylor-value
                                     lw-exp-mixture-coefficients))))

; For E_2(w)+i*E_2(2*w), the coefficients are independently calculated.
(assert-event
 (let* ((nodes (list (cons 1 (cons 1 0)) (cons 2 (cons 0 1))))
        (coefficients (lw-exp-mixture-coefficients nodes 0 3)))
   (and (equal coefficients (list (cons 1 1) (cons 1 2) (cons 1/2 2)))
        (equal (lw-complex-polynomial coefficients (cons 0 1) 0) (cons -3/2 0))
        (equal (lw-exp-mixture-taylor-value nodes (cons 0 1) 2) (cons -3/2 0)))))
