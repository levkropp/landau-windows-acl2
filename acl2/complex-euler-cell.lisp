(in-package "ACL2")

(include-book "log-cell-bounds")
(include-book "complex-exp-increment")

; Local Euler cancellation for the pole-removed continuation.
; The first-order error is uniform once |s| <= n.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-l1 lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-term lw-complex-exp-sum lw-exp-term lw-exp-sum
                 lw-exp-bounds lw-exp-lipschitz-cap lw-exp-index
                 lw-complex-disk-enlarge lw-disk-enlarge)))
(local (in-theory (disable lw-log-bounds lw-complex-exp-uniform-cap
 lw-complex-scale-add lw-complex-scale-product lw-complex-sub-add-first
 lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-ecell-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecell-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecell-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecell-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecell-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecell-times-negative)))))

(local (defthm lw-ecell-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecell-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecell-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecell-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecell-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecell-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecell-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecell-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecell-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecell-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecell-left-commutes)))))

(local (defthm lw-ecell-factorization
 (implies (and (lw-complexp point) (lw-complexp sample)
               (rationalp index) (rationalp ell))
  (equal
   (lw-complex-add point (lw-complex-scale (+ 1 index) (lw-complex-sub sample (cons 1 0))))
   (lw-complex-add
    (lw-complex-scale (- 1 (* (+ 1 index) ell)) point)
    (lw-complex-scale (+ 1 index)
     (lw-complex-sub sample
      (lw-complex-add (cons 1 0) (lw-complex-scale (- ell) point)))))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)
                 :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-ecell-remainder-radius
 (implies (and (rationalp cap) (<= 0 cap) (posp index) (rationalp error) (< 0 error))
  (<= (+ (* cap (+ (/ index) (* (+ 1 index) error)))
         (* (+ 1 index) (+ (* cap (/ index) cap (/ index)) error)))
      (+ (* (+ cap (* 2 cap cap)) (/ index)) (* (+ cap 1) (+ 1 index) error))))
 :hints (("Goal"
  :use ((:instance inverse-of-* (x index))
        (:instance lw-ecell-multiply-order (a 1) (b index) (factor (* cap cap (/ index) (/ index)))))
  :in-theory (disable inverse-of-*) :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-euler-linear-cell-bound
 (implies (and (lw-complex-diskp point cap) (posp index) (<= cap index)
               (rationalp ell) (<= 0 ell) (<= ell (/ index))
               (rationalp error) (< 0 error)
               (<= (abs (- 1 (* (+ 1 index) ell))) (+ (/ index) (* (+ 1 index) error))))
  (lw-complex-diskp
   (lw-complex-add point
    (lw-complex-scale (+ 1 index)
     (lw-complex-sub (lw-complex-exp-value (lw-complex-scale (- ell) point) error) (cons 1 0))))
   (+ (* (+ cap (* 2 cap cap)) (/ index)) (* (+ cap 1) (+ 1 index) error))))
 :hints (("Goal"
  :use ((:instance lw-complex-scale-disk (factor (- ell)) (radius cap))
        (:instance lw-ecell-multiply-order (a ell) (b (/ index)) (factor cap))
        (:instance lw-ecell-multiply-order (a cap) (b index) (factor (/ index)))
        (:instance lw-ecell-inverse-factor (divisor index) (coefficient 1))
        (:instance lw-complex-disk-enlarge (point (lw-complex-scale (- ell) point))
         (radius (* ell cap)) (cap (* cap (/ index))))
        (:instance lw-complex-exp-first-order-error
         (point (lw-complex-scale (- ell) point)) (radius (* cap (/ index))))
        (:instance lw-complex-scale-disk (factor (- 1 (* (+ 1 index) ell))) (radius cap))
        (:instance lw-ecell-multiply-order
         (a (abs (- 1 (* (+ 1 index) ell)))) (b (+ (/ index) (* (+ 1 index) error))) (factor cap))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-scale (- 1 (* (+ 1 index) ell)) point))
         (radius (* (abs (- 1 (* (+ 1 index) ell))) cap))
         (cap (* cap (+ (/ index) (* (+ 1 index) error)))))
        (:instance lw-complex-scale-disk
         (point (lw-complex-sub (lw-complex-exp-value (lw-complex-scale (- ell) point) error)
          (lw-complex-add (cons 1 0) (lw-complex-scale (- ell) point))))
         (factor (+ 1 index)) (radius (+ (* cap (/ index) cap (/ index)) error)))
        (:instance lw-complex-add-disk
         (left (lw-complex-scale (- 1 (* (+ 1 index) ell)) point))
         (right (lw-complex-scale (+ 1 index)
          (lw-complex-sub (lw-complex-exp-value (lw-complex-scale (- ell) point) error)
           (lw-complex-add (cons 1 0) (lw-complex-scale (- ell) point)))))
         (radius (* cap (+ (/ index) (* (+ 1 index) error))))
         (other-radius (* (+ 1 index) (+ (* cap (/ index) cap (/ index)) error))))
        (:instance lw-ecell-factorization
         (sample (lw-complex-exp-value (lw-complex-scale (- ell) point) error)))
        lw-ecell-remainder-radius
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-add point
          (lw-complex-scale (+ 1 index)
           (lw-complex-sub (lw-complex-exp-value (lw-complex-scale (- ell) point) error) (cons 1 0)))))
         (radius (+ (* cap (+ (/ index) (* (+ 1 index) error)))
                    (* (+ 1 index) (+ (* cap (/ index) cap (/ index)) error))))
         (cap (+ (* (+ cap (* 2 cap cap)) (/ index)) (* (+ cap 1) (+ 1 index) error)))))
  :in-theory (disable lw-complex-scale-disk lw-complex-exp-first-order-error lw-complex-add-disk
                      lw-ecell-inverse-factor)
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-euler-cell-factor (point index error)
 (lw-complex-add point
  (lw-complex-scale (+ 1 index)
   (lw-complex-sub
    (lw-complex-exp-value
     (lw-complex-scale (- (car (lw-log-bounds (+ 1 (/ index)) error))) point) error)
    (cons 1 0)))))

(local (in-theory (disable lw-complex-euler-cell-factor)))

(defthm lw-complex-euler-cell-factor-rational
 (implies (and (lw-complexp point) (posp index) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-cell-factor point index error)))
 :hints (("Goal"
  :use (lw-log-successor-cell-normalization)
  :in-theory (e/d (lw-complex-euler-cell-factor)
                  (lw-log-successor-cell-normalization))
  :do-not-induct t)))

(defthm lw-complex-euler-cell-factor-bound
 (implies (and (lw-complex-diskp point cap) (posp index) (<= cap index)
               (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-euler-cell-factor point index error)
   (+ (* (+ cap (* 2 cap cap)) (/ index)) (* (+ cap 1) (+ 1 index) error))))
 :hints (("Goal"
  :use (lw-log-successor-cell-normalization lw-log-successor-cell-error
        (:instance lw-complex-euler-linear-cell-bound
         (ell (car (lw-log-bounds (+ 1 (/ index)) error)))))
  :in-theory (e/d (lw-complex-euler-cell-factor)
   (lw-log-successor-cell-normalization lw-log-successor-cell-error lw-complex-euler-linear-cell-bound))
  :nonlinearp nil :do-not-induct t)))

