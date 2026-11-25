(in-package "ACL2")

(include-book "polynomial-maps")
(include-book "pole-resolvents")

; Construct a finite polynomial for c/(a-R*w), with a computed truncation
; and a boundary cap independent of the polynomial degree.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-complex-reciprocal
                 lw-complex-norm-square lw-complex-l1 lw-rational-power lw-complex-polynomial
                 lw-polynomial-multiply-coefficients lw-complex-polynomial-horner
                 lw-pole-unit-value lw-pole-resolvent-ratio lw-pole-resolvent-factor
                 lw-pole-unit-coefficient lw-pole-coefficient-precision
                 lw-resolvent-value lw-resolvent-coefficients lw-resolvent-truncation-count
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-pp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defun lw-pole-polynomial-coefficients (residue offset radius count)
  (lw-polynomial-multiply-coefficients (lw-pole-resolvent-factor residue offset)
    (lw-resolvent-coefficients (lw-pole-resolvent-ratio offset radius) 0 count)))

(defthm lw-pole-polynomial-valid
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp radius) (natp count))
           (and (lw-complex-coefficientsp (lw-pole-polynomial-coefficients residue offset radius count))
                (equal (len (lw-pole-polynomial-coefficients residue offset radius count)) count))))

(defthm lw-pole-polynomial-nth
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp radius)
                (natp count) (natp index) (< index count))
           (equal
            (nth index (lw-pole-polynomial-coefficients residue offset radius count))
            (lw-pole-unit-coefficient residue offset radius index)))
  :hints (("Goal" :in-theory (e/d (lw-pole-unit-coefficient)
                                  (lw-pole-unit-coefficient-formula)))))

(local (in-theory (disable lw-pole-polynomial-coefficients)))

(defthm lw-pole-unit-value-bound
  (implies (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
                (rationalp radius)
                (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) ratio-cap) (< ratio-cap 1)
                (lw-complex-diskp point 1))
           (lw-complex-diskp (lw-pole-unit-value residue offset radius point)
             (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset)) (/ (- 1 ratio-cap)))))
  :hints (("Goal"
           :use ((:instance lw-pole-unit-value-as-resolvent (cap ratio-cap))
                 (:instance lw-complex-l1-bound (point (lw-pole-resolvent-factor residue offset)))
                 (:instance lw-complex-mul-disk
                   (left (lw-pole-resolvent-ratio offset radius)) (radius ratio-cap)
                   (right point) (other-radius 1))
                 (:instance lw-complex-resolvent-bound
                   (point (lw-complex-mul (lw-pole-resolvent-ratio offset radius) point))
                   (radius ratio-cap))
                 (:instance lw-complex-mul-disk
                   (left (lw-pole-resolvent-factor residue offset))
                   (radius (lw-complex-l1 (lw-pole-resolvent-factor residue offset)))
                   (right (lw-resolvent-value (lw-pole-resolvent-ratio offset radius) point))
                   (other-radius (/ (- 1 ratio-cap)))))
           :in-theory (e/d (lw-resolvent-value)
                           (lw-pole-unit-value-as-resolvent lw-complex-l1-bound
                            lw-complex-resolvent-bound lw-complex-mul-disk))
           :do-not-induct t)))

(defthm lw-pole-polynomial-error
  (implies
   (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
        (rationalp radius)
        (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) ratio-cap) (< ratio-cap 1)
        (lw-complex-diskp point 1) (rationalp error) (< 0 error) (natp count)
        (<= (lw-resolvent-truncation-count ratio-cap
              (lw-pole-coefficient-precision residue offset error)) count))
   (lw-complex-diskp
    (lw-complex-sub (lw-pole-unit-value residue offset radius point)
      (lw-complex-polynomial (lw-pole-polynomial-coefficients residue offset radius count) point 0))
    error))
  :hints (("Goal"
           :use ((:instance lw-pole-unit-value-as-resolvent (cap ratio-cap))
                 lw-pole-coefficient-precision-adequate
                 (:instance lw-resolvent-computed-polynomial-error
                   (ratio (lw-pole-resolvent-ratio offset radius)) (radius ratio-cap)
                   (error (lw-pole-coefficient-precision residue offset error)))
                 (:instance lw-complex-l1-bound (point (lw-pole-resolvent-factor residue offset)))
                 (:instance lw-complex-left-product-error
                   (factor (lw-pole-resolvent-factor residue offset))
                   (cap (lw-complex-l1 (lw-pole-resolvent-factor residue offset)))
                   (a (lw-resolvent-value (lw-pole-resolvent-ratio offset radius) point))
                   (b (lw-complex-polynomial
                        (lw-resolvent-coefficients (lw-pole-resolvent-ratio offset radius) 0 count)
                        point 0))
                   (error (lw-pole-coefficient-precision residue offset error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-pole-unit-value residue offset radius point)
                     (lw-complex-polynomial
                       (lw-pole-polynomial-coefficients residue offset radius count) point 0)))
                   (radius (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset))
                              (lw-pole-coefficient-precision residue offset error)))
                   (cap error)))
           :in-theory
           (e/d (lw-pole-polynomial-coefficients)
                (lw-pole-unit-value-as-resolvent lw-pole-coefficient-precision-adequate
                 lw-resolvent-computed-polynomial-error lw-complex-l1-bound
                 lw-complex-left-product-error))
           :do-not-induct t)))

(defthm lw-pole-polynomial-bound
  (implies
   (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
        (rationalp radius)
        (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) ratio-cap) (< ratio-cap 1)
        (lw-complex-diskp point 1) (rationalp error) (< 0 error) (natp count)
        (<= (lw-resolvent-truncation-count ratio-cap
              (lw-pole-coefficient-precision residue offset error)) count))
   (lw-complex-diskp
    (lw-complex-polynomial (lw-pole-polynomial-coefficients residue offset radius count) point 0)
    (+ (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset)) (/ (- 1 ratio-cap))) error)))
  :hints (("Goal"
           :use (lw-pole-polynomial-error lw-pole-unit-value-bound
                 (:instance lw-complex-subtract-cancel
                   (a (lw-pole-unit-value residue offset radius point))
                   (b (lw-complex-polynomial
                        (lw-pole-polynomial-coefficients residue offset radius count) point 0)))
                 (:instance lw-complex-sub-disk
                   (left (lw-pole-unit-value residue offset radius point))
                   (radius (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset))
                              (/ (- 1 ratio-cap))))
                   (right (lw-complex-sub (lw-pole-unit-value residue offset radius point)
                     (lw-complex-polynomial
                       (lw-pole-polynomial-coefficients residue offset radius count) point 0)))
                   (other-radius error)))
           :in-theory (disable lw-pole-polynomial-error lw-pole-unit-value-bound
                               lw-complex-subtract-cancel lw-complex-sub-disk
                               lw-complex-sub-add-first)
           :do-not-induct t)))

(defun lw-pole-polynomial-count (residue offset radius clearance error)
  (lw-resolvent-truncation-count (/ radius clearance)
    (lw-pole-coefficient-precision residue offset error)))

(defthm lw-pole-polynomial-count-natural
  (and (natp (lw-pole-polynomial-count residue offset radius clearance error))
       (< 0 (lw-pole-polynomial-count residue offset radius clearance error)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-pole-computed-polynomial-error
  (implies
   (and (lw-complexp residue) (lw-complexp offset)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square offset))
        (rationalp radius) (<= 0 radius) (< radius clearance)
        (lw-complex-diskp point 1) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub (lw-pole-unit-value residue offset radius point)
      (lw-complex-polynomial
        (lw-pole-polynomial-coefficients residue offset radius
          (lw-pole-polynomial-count residue offset radius clearance error)) point 0))
    error))
  :hints (("Goal"
           :use ((:instance lw-pole-resolvent-clearance-bound (lower clearance))
                 (:instance lw-pole-polynomial-error (ratio-cap (/ radius clearance))
                   (count (lw-pole-polynomial-count residue offset radius clearance error))))
           :in-theory (disable lw-pole-resolvent-clearance-bound lw-pole-polynomial-error)
           :do-not-induct t)))

(local (defun lw-pp-countdown (sample-count)
         (declare (xargs :measure (nfix sample-count)))
         (if (zp sample-count) 0 (lw-pp-countdown (- sample-count 1)))))

(defthm lw-pole-polynomial-boundary-check
  (implies
   (and (lw-complexp residue) (lw-complexp offset) (not (equal offset (cons 0 0)))
        (rationalp radius)
        (lw-complex-diskp (lw-pole-resolvent-ratio offset radius) ratio-cap) (< ratio-cap 1)
        (lw-complex-diskp point 1) (rationalp error) (< 0 error) (natp count)
        (<= (lw-resolvent-truncation-count ratio-cap
              (lw-pole-coefficient-precision residue offset error)) count)
        (natp sample-count))
   (lw-cauchy-boundary-check
    (lw-pole-polynomial-coefficients residue offset radius count) point 0 sample-count
    (+ (* (lw-complex-l1 (lw-pole-resolvent-factor residue offset)) (/ (- 1 ratio-cap))) error)))
  :hints (("Goal" :induct (lw-pp-countdown sample-count)
                  :in-theory (enable lw-cauchy-boundary-check))
          (and stable-under-simplificationp
               '(:use ((:instance lw-pole-polynomial-bound
                          (point (lw-complex-power point (- sample-count 1)))))
                 :in-theory (disable lw-pole-polynomial-bound)
                 :do-not-induct t))))
