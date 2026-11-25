(in-package "ACL2")

(include-book "polynomial-maps")

; Compute P(center+slope*w) without coefficient or evaluation hypotheses.
; Linear multiplication and Horner composition operate on finite lists.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner
                 lw-polynomial-add-constant lw-polynomial-multiply-coefficients)))

(local (defthm lw-pa-zero-times (equal (* 0 a) 0)))
(local (defthm lw-pa-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-pa-polynomial-nil
         (equal (lw-complex-polynomial nil point offset) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-polynomial)))))

(defun lw-polynomial-multiply-linear (constant slope coefficients)
  (if (endp coefficients) nil
    (cons (lw-complex-mul constant (car coefficients))
      (lw-polynomial-add-constant (lw-complex-mul slope (car coefficients))
        (lw-polynomial-multiply-linear constant slope (cdr coefficients))))))

(defthm lw-polynomial-multiply-linear-valid
  (implies (and (lw-complexp constant) (lw-complexp slope) (lw-complex-coefficientsp coefficients))
           (and (lw-complex-coefficientsp
                  (lw-polynomial-multiply-linear constant slope coefficients))
                (equal (len (lw-polynomial-multiply-linear constant slope coefficients))
                       (if (consp coefficients) (+ 1 (len coefficients)) 0)))))

(defthm lw-polynomial-multiply-linear-evaluation
  (implies (and (lw-complexp constant) (lw-complexp slope) (lw-complex-coefficientsp coefficients)
                (lw-complexp point))
           (equal
            (lw-complex-polynomial (lw-polynomial-multiply-linear constant slope coefficients) point 0)
            (lw-complex-mul (lw-complex-add constant (lw-complex-mul slope point))
                            (lw-complex-polynomial coefficients point 0))))
  :hints (("Goal" :induct (lw-polynomial-multiply-linear constant slope coefficients)
                  :in-theory (enable lw-complex-polynomial-horner))))

(defun lw-polynomial-affine (coefficients center slope)
  (if (endp coefficients) nil
    (lw-polynomial-add-constant (car coefficients)
      (lw-polynomial-multiply-linear center slope
        (lw-polynomial-affine (cdr coefficients) center slope)))))

(defthm lw-polynomial-affine-valid
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp center) (lw-complexp slope))
           (and (lw-complex-coefficientsp (lw-polynomial-affine coefficients center slope))
                (equal (len (lw-polynomial-affine coefficients center slope)) (len coefficients)))))

(defthm lw-polynomial-affine-evaluation
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp center) (lw-complexp slope)
                (lw-complexp point))
           (equal
            (lw-complex-polynomial (lw-polynomial-affine coefficients center slope) point 0)
            (lw-complex-polynomial coefficients (lw-complex-add center (lw-complex-mul slope point)) 0)))
  :hints (("Goal" :induct (lw-polynomial-affine coefficients center slope)
                  :in-theory (e/d (lw-complex-polynomial-horner)
                                  (lw-polynomial-multiply-linear)))))

(assert-event
 (let ((coefficients (list (cons 1 0) (cons 2 0) (cons 3 0))))
   (and (equal (lw-polynomial-affine coefficients (cons 2 0) (cons -1 0))
                (list (cons 17 0) (cons -14 0) (cons 3 0)))
        (equal (lw-complex-polynomial
                 (lw-polynomial-affine coefficients (cons 2 0) (cons -1 0)) (cons 1 0) 0)
               (cons 6 0)))))
