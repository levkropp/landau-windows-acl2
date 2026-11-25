; Scalar kernels and finite arithmetic examples, kept separate from the
; full complex Mellin construction and the final Landau reduction.
(in-package "ACL2")
(include-book "../acl2/kernel-bounds")

(local
 (defthm video-six-product-commutes
   (equal (* left (* middle right)) (* middle (* left right)))
   :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                         (:instance associativity-of-* (x middle) (y left) (z right))
                         (:instance commutativity-of-* (x left) (y middle)))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(defthm video-exp-terms
  (and (equal (lw-exp-term 1 0) 1)
       (equal (lw-exp-term 1 1) 1)
       (equal (lw-exp-term 1 2) 1/2)
       (equal (lw-exp-term 1 3) 1/6)
       (equal (lw-exp-term 1 4) 1/24))
  :rule-classes nil)

(defthm video-exp-band-example
  (equal (lw-exp-band 1 3) '(8/3 . 11/4))
  :rule-classes nil)

(defthm video-exp-band-finite-upper
  (implies (and (natp later) (<= 3 later))
           (<= (lw-exp-sum 1 later) 11/4))
  :hints (("Goal" :use ((:instance lw-exp-later-partial-sum-enclosed
                          (value 1) (small 3) (large later)))
                  :in-theory (disable lw-exp-later-partial-sum-enclosed lw-exp-sum)))
  :rule-classes nil)

(defthm video-exp-auto-examples
  (and (equal (lw-exp-index 1 1/100) 7)
       (equal (lw-exp-bounds 1 1/10) '(8/3 . 11/4))
       (equal (lw-exp-bounds 1 1/100) '(685/252 . 54801/20160))
       (equal (lw-exp-neg-bounds 1 1/10) '(4/11 . 3/8)))
  :rule-classes nil)

(defthm video-kernel-examples
  (and (equal (lw-kernel-weight-scale 1/3 2 1/2) 1/36)
       (equal (lw-kernel-weight-bounds 1/3 3 2 1/2 1/10) '(1/99 . 1/96))
       (equal (lw-kernel-weight-bounds 1/3 3 2 1/2 1/100) '(560/54801 . 7/685)))
  :rule-classes nil)

(defun video-line-grid (start step count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (* start step)
       (video-line-grid (+ start step) step (- count 1)))))

(local
 (defthm video-line-grid-rational
   (implies (and (rationalp start) (rationalp step))
            (rationalp (video-line-grid start step count)))
   :rule-classes (:rewrite :type-prescription)))

(defthm video-line-grid-formula
  (implies (and (rationalp start) (rationalp step) (natp count))
           (equal (video-line-grid start step count)
                  (+ (* count start step)
                     (* 1/2 count (- count 1) step step))))
  :hints (("Goal" :induct (video-line-grid start step count) :nonlinearp t)))

(defthm video-quadrature-examples
  (and (equal (video-line-grid 0 1/4 4) 3/8)
       (equal (video-line-grid 0 1/8 8) 7/16)
       (equal (- 1/2 (video-line-grid 0 1/4 4)) 1/8)
       (equal (- 1/2 (video-line-grid 0 1/8 8)) 1/16))
  :rule-classes nil)

(defun video-cell-tolerance (count error)
  (/ error (+ 1 (nfix count))))

(defthm video-cell-budget
  (implies (and (natp count) (rationalp error) (< 0 error))
           (and (< 0 (video-cell-tolerance count error))
                (<= (* count (video-cell-tolerance count error)) error)))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* count error)) (divisor (+ 1 count)) (bound error)))
                  :nonlinearp t))
  :rule-classes nil)

(defthm video-decay-tail-sample
  (<= (cdr (lw-exp-neg-bounds 8 1/1000)) 1/1000)
  :rule-classes nil)

(defthm video-error-ledger
  (implies (and (rationalp x) (rationalp y) (rationalp z)
                (<= (abs x) 1/1000)
                (<= (abs y) 1/1000)
                (<= (abs z) 1/1000))
           (<= (abs (+ x y z)) 3/1000))
  :hints (("Goal" :in-theory (enable abs)))
  :rule-classes nil)

(assert-event (equal (lw-exp-sum 1 2) 5/2))
(assert-event (equal (lw-exp-initial-width 1) 1/12))
(assert-event (equal (lw-exp-depth 1 1/100) 4))
(assert-event (equal (video-cell-tolerance 4 1/100) 1/500))
