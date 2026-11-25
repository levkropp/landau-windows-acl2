(in-package "ACL2")

(include-book "polynomial-divided-difference")

; Finite coefficient constructors for normalized regular models.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-polynomial-horner)))

(local (defthm lw-pm-zero-times (equal (* 0 a) 0)))
(local (defthm lw-pm-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-pm-polynomial-nil
         (equal (lw-complex-polynomial nil point offset) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-polynomial)))))

(defun lw-polynomial-multiply-coefficients (factor coefficients)
  (if (endp coefficients) nil
    (cons (lw-complex-mul factor (car coefficients))
          (lw-polynomial-multiply-coefficients factor (cdr coefficients)))))

(defthm lw-polynomial-multiply-coefficients-valid
  (implies (and (lw-complexp factor) (lw-complex-coefficientsp coefficients))
           (and (lw-complex-coefficientsp
                  (lw-polynomial-multiply-coefficients factor coefficients))
                (equal (len (lw-polynomial-multiply-coefficients factor coefficients))
                       (len coefficients)))))

(defthm lw-polynomial-multiply-coefficients-evaluation
  (implies (and (lw-complexp factor) (lw-complex-coefficientsp coefficients)
                (lw-complexp point) (natp offset))
           (equal
            (lw-complex-polynomial
              (lw-polynomial-multiply-coefficients factor coefficients) point offset)
            (lw-complex-mul factor (lw-complex-polynomial coefficients point offset))))
  :hints (("Goal" :induct (lw-complex-polynomial coefficients point offset)
                  :in-theory (enable lw-complex-polynomial))))

(local (defun lw-pm-nth-induct (coefficients index)
         (declare (xargs :measure (nfix index)))
         (if (or (endp coefficients) (zp index)) nil
           (lw-pm-nth-induct (cdr coefficients) (- index 1)))))

(defthm lw-polynomial-multiply-coefficients-nth
  (implies (and (lw-complexp factor) (lw-complex-coefficientsp coefficients)
                (natp index) (< index (len coefficients)))
           (equal
            (nth index (lw-polynomial-multiply-coefficients factor coefficients))
            (lw-complex-mul factor (nth index coefficients))))
  :hints (("Goal" :induct (lw-pm-nth-induct coefficients index)
                  :in-theory (enable nth))))

(defun lw-polynomial-add-constant (constant coefficients)
  (if (endp coefficients) (list constant)
    (cons (lw-complex-add constant (car coefficients)) (cdr coefficients))))

(defthm lw-polynomial-add-constant-valid
  (implies (and (lw-complexp constant) (lw-complex-coefficientsp coefficients))
           (and (lw-complex-coefficientsp (lw-polynomial-add-constant constant coefficients))
                (equal (len (lw-polynomial-add-constant constant coefficients))
                       (if (consp coefficients) (len coefficients) 1)))))

(defthm lw-polynomial-add-constant-evaluation
  (implies (and (lw-complexp constant) (lw-complex-coefficientsp coefficients)
                (lw-complexp point))
           (equal
            (lw-complex-polynomial (lw-polynomial-add-constant constant coefficients) point 0)
            (lw-complex-add constant (lw-complex-polynomial coefficients point 0))))
  :hints (("Goal" :in-theory (enable lw-complex-polynomial-horner))
          (and stable-under-simplificationp
               '(:expand ((lw-complex-polynomial (list constant) point 0)
                           (lw-complex-power point 0))
                 :do-not-induct t))))
