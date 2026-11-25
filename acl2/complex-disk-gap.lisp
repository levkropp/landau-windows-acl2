(in-package "ACL2")

(include-book "complex-geometric")

; A rational point outside a closed rational disk is still outside a
; slightly enlarged disk, with an explicitly computed positive slack.
; This eliminates auxiliary approximation budgets by a finite argument.

(local (in-theory
        (disable lw-complexp lw-complex-diskp lw-diskp lw-complex-norm-square
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cdg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cdg-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cdg-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cdg-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cdg-square-nonnegative
         (implies (rationalp value) (<= 0 (* value value)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cdg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cdg-division-data
         (implies (and (rationalp gap) (< 0 gap) (rationalp norm) (<= gap norm)
                       (rationalp radius) (<= 0 radius))
                  (and (rationalp (/ gap (* 4 (+ 1 norm radius))))
                       (< 0 (/ gap (* 4 (+ 1 norm radius))))
                       (<= (/ gap (* 4 (+ 1 norm radius))) 1)
                       (<= (* (+ (* 2 radius) 1) (/ gap (* 4 (+ 1 norm radius)))) (* 1/2 gap))))
         :hints (("Goal" :use ((:instance lw-positive-division-bound
                                 (numerator gap) (divisor (* 4 (+ 1 norm radius))) (bound 1))
                               (:instance lw-positive-division-bound
                                 (numerator (* (+ (* 2 radius) 1) gap))
                                 (divisor (* 4 (+ 1 norm radius))) (bound (* 1/2 gap))))
                         :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-cdg-small-enlargement
         (implies (and (rationalp radius) (<= 0 radius) (rationalp gap) (< 0 gap)
                       (rationalp slack) (< 0 slack) (<= slack 1)
                       (<= (* (+ (* 2 radius) 1) slack) (* 1/2 gap)))
                  (< (* (+ radius slack) (+ radius slack)) (+ (* radius radius) gap)))
         :hints (("Goal" :use ((:instance lw-cdg-multiply-order (a slack) (b 1) (factor slack)))
                         :nonlinearp t))
         :rule-classes nil))

(defun lw-disk-gap-error (norm radius)
  (/ (- norm (* radius radius)) (* 4 (+ 1 norm radius))))

(defthm lw-disk-gap-error-data
  (implies (and (rationalp norm) (rationalp radius) (<= 0 radius) (< (* radius radius) norm))
           (and (rationalp (lw-disk-gap-error norm radius))
                (< 0 (lw-disk-gap-error norm radius))
                (< (* (+ radius (lw-disk-gap-error norm radius))
                      (+ radius (lw-disk-gap-error norm radius))) norm)))
  :hints (("Goal" :use ((:instance lw-cdg-square-nonnegative (value radius))
                        (:instance lw-cdg-division-data (gap (- norm (* radius radius))))
                        (:instance lw-cdg-small-enlargement
                          (gap (- norm (* radius radius))) (slack (lw-disk-gap-error norm radius))))
                  :nonlinearp t)))

(local (in-theory (disable lw-disk-gap-error)))

(defthm lw-complex-disk-gap-excludes
  (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius)
                (not (lw-complex-diskp point radius)))
           (and (rationalp (lw-disk-gap-error (lw-complex-norm-square point) radius))
                (< 0 (lw-disk-gap-error (lw-complex-norm-square point) radius))
                (not (lw-complex-diskp
                      point (+ radius (lw-disk-gap-error (lw-complex-norm-square point) radius))))))
  :hints (("Goal" :use (lw-complex-norm-square-valid
                        (:instance lw-disk-gap-error-data (norm (lw-complex-norm-square point)))
                        lw-complex-disk-norm-square
                        (:instance lw-complex-disk-norm-square
                          (radius (+ radius (lw-disk-gap-error (lw-complex-norm-square point) radius)))))
                  :in-theory (disable lw-complex-norm-square-valid lw-disk-gap-error-data))))

(assert-event
 (and (equal (lw-disk-gap-error 2 1) 1/16)
      (not (lw-complex-diskp (cons 1 1) 17/16))))

