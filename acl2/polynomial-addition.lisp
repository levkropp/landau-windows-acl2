(in-package "ACL2")

(include-book "polynomial-maps")
(include-book "cauchy-extraction")

; Combine finite polynomial models and discharge their coarse boundary
; caps from coefficients. Tighter constructed caps may be used as well.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner lw-complex-l1
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-padd-zero-times (equal (* 0 a) 0)))
(local (defthm lw-padd-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-padd-polynomial-nil
         (equal (lw-complex-polynomial nil point offset) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-polynomial)))))

(defun lw-polynomial-add (left right)
  (cond ((endp left) right)
        ((endp right) left)
        (t (cons (lw-complex-add (car left) (car right))
                 (lw-polynomial-add (cdr left) (cdr right))))))

(defthm lw-polynomial-add-valid
  (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right))
           (and (lw-complex-coefficientsp (lw-polynomial-add left right))
                (equal (len (lw-polynomial-add left right)) (max (len left) (len right))))))

(local (defun lw-padd-evaluation-induct (left right offset)
         (if (or (endp left) (endp right)) offset
           (lw-padd-evaluation-induct (cdr left) (cdr right) (+ 1 offset)))))

(defthm lw-polynomial-add-evaluation
  (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right)
                (lw-complexp point) (natp offset))
           (equal
            (lw-complex-polynomial (lw-polynomial-add left right) point offset)
            (lw-complex-add (lw-complex-polynomial left point offset)
                            (lw-complex-polynomial right point offset))))
  :hints (("Goal" :induct (lw-padd-evaluation-induct left right offset)
                  :in-theory (enable lw-complex-polynomial))))

(defthm lw-complex-polynomial-unit-mass-bound
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complex-diskp point 1) (natp offset))
           (lw-complex-diskp (lw-complex-polynomial coefficients point offset)
                            (lw-complex-coefficient-mass coefficients)))
  :hints (("Goal" :induct (lw-complex-polynomial coefficients point offset)
                  :in-theory (e/d (lw-complex-polynomial lw-complex-coefficient-mass)
                                  (lw-complex-mul-disk lw-complex-add-disk lw-complex-l1-bound)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-l1-bound (point (car coefficients)))
                       (:instance lw-complex-unit-power (index offset))
                       (:instance lw-complex-mul-disk
                         (left (car coefficients)) (radius (lw-complex-l1 (car coefficients)))
                         (right (lw-complex-power point offset)) (other-radius 1))
                       (:instance lw-complex-add-disk
                         (left (lw-complex-mul (car coefficients) (lw-complex-power point offset)))
                         (radius (lw-complex-l1 (car coefficients)))
                         (right (lw-complex-polynomial (cdr coefficients) point (+ 1 offset)))
                         (other-radius (lw-complex-coefficient-mass (cdr coefficients)))))
                 :do-not-induct t))))

(local (defun lw-padd-countdown (count)
         (declare (xargs :measure (nfix count)))
         (if (zp count) 0 (lw-padd-countdown (- count 1)))))

(defthm lw-cauchy-boundary-check-coefficient-mass
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complex-diskp point 1)
                (natp offset) (natp count))
           (lw-cauchy-boundary-check coefficients point offset count
                                     (lw-complex-coefficient-mass coefficients)))
  :hints (("Goal" :induct (lw-padd-countdown count)
                  :in-theory (enable lw-cauchy-boundary-check))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-polynomial-unit-mass-bound
                          (point (lw-complex-power point (- count 1)))))
                 :in-theory (disable lw-complex-polynomial-unit-mass-bound)
                 :do-not-induct t))))
