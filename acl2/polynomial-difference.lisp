(in-package "ACL2")

(include-book "cauchy-extraction")

; A finite boundary check on the actual difference of two polynomials
; controls their selected coefficients. Both lists share one degree.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-complex-polynomial
                 lw-complex-mul-subtract lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-coefficient-at lw-complex-coefficient-mass
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-cauchy-polynomial-average
                 lw-cauchy-evaluation-sum lw-cauchy-moment-count lw-geometric-index lw-geometric-threshold
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-pdiff-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-pdiff-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pdiff-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pdiff-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-pdiff-double-negative
         (implies (rationalp value) (equal (- (- value)) value))))
(local (defthm lw-pdiff-sub-product
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp point))
                  (equal (lw-complex-mul (lw-complex-sub a b) point)
                         (lw-complex-sub (lw-complex-mul a point) (lw-complex-mul b point))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul lw-complex-sub)))))

(defun lw-polynomial-difference (left right)
  (if (consp left)
      (cons (lw-complex-sub (car left) (car right))
            (lw-polynomial-difference (cdr left) (cdr right)))
    nil))

(defthm lw-polynomial-difference-valid
  (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (equal (len left) (len right)))
           (and (lw-complex-coefficientsp (lw-polynomial-difference left right))
                (equal (len (lw-polynomial-difference left right)) (len left)))))

(local (defun lw-pdiff-nth-induct (left right index)
         (declare (xargs :measure (len left)))
         (if (or (endp left) (zp index)) (list left right index)
           (lw-pdiff-nth-induct (cdr left) (cdr right) (- index 1)))))

(defthm lw-polynomial-difference-nth
  (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (equal (len left) (len right))
                (natp index) (< index (len left)))
           (equal (nth index (lw-polynomial-difference left right))
                  (lw-complex-sub (nth index left) (nth index right))))
  :hints (("Goal" :induct (lw-pdiff-nth-induct left right index)
                  :in-theory (enable nth))))

(local (defun lw-pdiff-eval-induct (left right offset)
         (declare (xargs :measure (len left)))
         (if (endp left) (list left right offset)
           (lw-pdiff-eval-induct (cdr left) (cdr right) (+ 1 offset)))))

(defthm lw-polynomial-difference-evaluation
  (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (equal (len left) (len right))
                (lw-complexp point) (natp offset))
           (equal (lw-complex-polynomial (lw-polynomial-difference left right) point offset)
                  (lw-complex-sub (lw-complex-polynomial left point offset)
                                  (lw-complex-polynomial right point offset))))
  :hints (("Goal" :induct (lw-pdiff-eval-induct left right offset)
                  :in-theory (e/d (lw-complex-polynomial)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes lw-complex-sub-add-first)))))

(local (in-theory (disable lw-polynomial-difference)))

(defthm lw-polynomial-difference-cauchy-bound
  (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right) (equal (len left) (len right))
                (natp degree) (<= (len left) (+ 1 degree)) (natp index) (< index (len left))
                (rationalp error) (< 0 error) (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check
                 (lw-polynomial-difference left right) (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count (lw-polynomial-difference left right) degree error) cap))
           (lw-complex-diskp (lw-complex-sub (nth index left) (nth index right)) (+ cap error)))
  :hints (("Goal" :use ((:instance lw-cauchy-finite-coefficient-bound
                          (coefficients (lw-polynomial-difference left right)) (target index)))
                  :in-theory (disable lw-cauchy-finite-coefficient-bound))))

; P(z)=1+i*z and Q(z)=2-z have P-Q=-1+(1+i)*z.
(assert-event
 (and (equal (lw-polynomial-difference (list (cons 1 0) (cons 0 1)) (list (cons 2 0) (cons -1 0)))
             (list (cons -1 0) (cons 1 1)))
      (equal (lw-complex-polynomial
              (lw-polynomial-difference (list (cons 1 0) (cons 0 1)) (list (cons 2 0) (cons -1 0)))
              (cons 0 1) 0)
             (cons -2 1))))

