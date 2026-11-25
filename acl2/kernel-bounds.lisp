(in-package "ACL2")

(include-book "exp-bounds")

(local (defthm lw-kb-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

; The quadrature weight h*u^j*exp(-sigma*u)/j! is nonnegative.
; expTerm supplies u^j/j!, not an assumed kernel normalization.
(defun lw-kernel-weight-scale (value index step)
  (* step (lw-exp-term value index)))

(defun lw-kernel-weight-precision (value index step error)
  (/ error (+ 1 (lw-kernel-weight-scale value index step))))

(defun lw-kernel-weight-bounds (value sigma index step error)
  (let* ((scale (lw-kernel-weight-scale value index step))
         (precision (lw-kernel-weight-precision value index step error))
         (bounds (lw-exp-neg-bounds (* sigma value) precision)))
    (cons (* scale (car bounds)) (* scale (cdr bounds)))))

(defthm lw-kernel-weight-scale-nonnegative
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step))
           (and (rationalp (lw-kernel-weight-scale value index step))
                (<= 0 (lw-kernel-weight-scale value index step))))
  :hints (("Goal" :use (lw-exp-term-nonnegative)
                  :in-theory (disable lw-exp-term)
                  :nonlinearp t)))

(defthm lw-kernel-weight-precision-positive
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-kernel-weight-precision value index step error))
                (< 0 (lw-kernel-weight-precision value index step error))))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative)
                  :in-theory (disable lw-kernel-weight-scale lw-kernel-weight-scale-nonnegative)
                  :nonlinearp t)))

(defthm lw-kernel-weight-error-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error))
           (<= (* (lw-kernel-weight-scale value index step)
                  (lw-kernel-weight-precision value index step error)) error))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative
                        (:instance lw-positive-division-bound
                          (numerator (* (lw-kernel-weight-scale value index step) error))
                          (divisor (+ 1 (lw-kernel-weight-scale value index step))) (bound error)))
                  :in-theory (disable lw-kernel-weight-scale lw-kernel-weight-scale-nonnegative)
                  :nonlinearp t)))

(defthm lw-kernel-weight-bounds-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step))
           (and (lw-intervalp (lw-kernel-weight-bounds value sigma index step error))
                (<= 0 (car (lw-kernel-weight-bounds value sigma index step error)))
                (<= (cdr (lw-kernel-weight-bounds value sigma index step error))
                    (lw-kernel-weight-scale value index step))))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value)) (epsilon (lw-kernel-weight-precision value index step error))))
                  :in-theory (disable lw-kernel-weight-scale lw-kernel-weight-precision
                                      lw-kernel-weight-scale-nonnegative lw-exp-neg-bounds lw-exp-neg-bounds-valid
                                      lw-exp-neg-bounds-overlap)
                  :nonlinearp t)))

(defthm lw-kernel-weight-bounds-width
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (<= (- (cdr (lw-kernel-weight-bounds value sigma index step error))
                  (car (lw-kernel-weight-bounds value sigma index step error))) error))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative lw-kernel-weight-precision-positive
                        lw-kernel-weight-error-budget
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value)) (epsilon (lw-kernel-weight-precision value index step error)))
                        (:instance lw-exp-neg-bounds-width
                          (value (* sigma value)) (epsilon (lw-kernel-weight-precision value index step error))))
                  :in-theory (disable lw-kernel-weight-scale lw-kernel-weight-precision
                                      lw-kernel-weight-scale-nonnegative lw-kernel-weight-precision-positive
                                      lw-kernel-weight-error-budget lw-exp-neg-bounds
                                      lw-exp-neg-bounds-valid lw-exp-neg-bounds-width lw-exp-neg-bounds-overlap)
                  :nonlinearp t)))

(defthm lw-kernel-weight-bounds-overlap
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step))
           (<= (car (lw-kernel-weight-bounds value sigma index step left-error))
               (cdr (lw-kernel-weight-bounds value sigma index step right-error))))
  :hints (("Goal" :use (lw-kernel-weight-scale-nonnegative
                        (:instance lw-exp-neg-bounds-overlap
                          (value (* sigma value))
                          (left-error (lw-kernel-weight-precision value index step left-error))
                          (right-error (lw-kernel-weight-precision value index step right-error)))
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value))
                          (epsilon (lw-kernel-weight-precision value index step left-error)))
                        (:instance lw-exp-neg-bounds-valid
                          (value (* sigma value))
                          (epsilon (lw-kernel-weight-precision value index step right-error))))
                  :in-theory (disable lw-kernel-weight-scale lw-kernel-weight-precision
                                      lw-kernel-weight-scale-nonnegative lw-exp-neg-bounds
                                      lw-exp-neg-bounds-overlap lw-exp-neg-bounds-valid)
                  :nonlinearp t)))

(defthm lw-kernel-weight-lower-cauchy
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                (rationalp step) (<= 0 step)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-kernel-weight-bounds value sigma index step left-error))
                       (car (lw-kernel-weight-bounds value sigma index step right-error))))
               (+ left-error right-error)))
  :hints (("Goal" :use (lw-kernel-weight-bounds-overlap
                        (:instance lw-kernel-weight-bounds-overlap
                          (left-error right-error) (right-error left-error))
                        (:instance lw-kernel-weight-bounds-valid (error left-error))
                        (:instance lw-kernel-weight-bounds-valid (error right-error))
                        (:instance lw-kernel-weight-bounds-width (error left-error))
                        (:instance lw-kernel-weight-bounds-width (error right-error)))
                  :in-theory (disable lw-kernel-weight-bounds lw-kernel-weight-bounds-overlap
                                      lw-kernel-weight-bounds-valid lw-kernel-weight-bounds-width))))

(assert-event
 (let ((bounds (lw-kernel-weight-bounds 1 2 3 1/10 1/1000)))
   (and (lw-intervalp bounds) (< 0 (car bounds))
        (<= (- (cdr bounds) (car bounds)) 1/1000))))

(assert-event
 (and (equal (lw-kernel-weight-bounds 0 252 0 1/10 1/100) (cons 1/10 1/10))
      (equal (lw-kernel-weight-bounds 0 252 3 1/10 1/100) (cons 0 0))
      (equal (lw-kernel-weight-bounds 1 252 3 0 1/100) (cons 0 0))))
