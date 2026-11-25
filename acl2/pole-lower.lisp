(in-package "ACL2")

(include-book "pole-resolvents")

; Reconstruct the residue from a pole coefficient. Disk bounds on the
; coefficient therefore imply disk bounds on the explicitly given residue.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-conjugate lw-complex-norm-square lw-complex-diskp lw-diskp
                 lw-complex-reciprocal lw-complex-power lw-rational-power
                 lw-complex-polynomial lw-complex-coefficient-at lw-complex-l1
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-cauchy-moment-count lw-cauchy-orbit-moment
                 lw-cauchy-moment-expansion lw-cauchy-correlation-expansion lw-cauchy-residual-expansion
                 lw-complex-correlation-sum lw-complex-signed-power lw-complex-geometric-average
                 lw-complex-geometric-sum lw-cauchy-evaluation-sum lw-cauchy-polynomial-average
                 lw-cauchy-evaluation-sum-expansion lw-cauchy-evaluation-sum-first
                 lw-complex-conjugate-power lw-complex-power-power lw-complex-power-add lw-complex-power-step
                 lw-cauchy-polynomial-average-moments lw-cauchy-scaled-expansion
                 lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-resolvent-value lw-resolvent-coefficients lw-resolvent-polynomial-evaluation
                 lw-resolvent-truncation-count lw-geometric-index lw-geometric-threshold
                 lw-cauchy-resolvent-sum lw-cauchy-resolvent-average lw-resolvent-cauchy-order
                 lw-resolvent-cauchy-count lw-complex-coefficient-mass
                 lw-pole-resolvent-ratio lw-pole-resolvent-factor lw-pole-unit-value
                 lw-pole-unit-coefficient lw-pole-unit-coefficient-formula
                 lw-cauchy-pole-sum lw-cauchy-pole-average lw-pole-coefficient-precision
                 lw-cauchy-boundary-check)))

(local (defun lw-pl-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-pl-countdown (- index 1)))))

(local (defthm lw-pl-one-power
         (equal (lw-complex-power (cons 1 0) index) (cons 1 0))
         :hints (("Goal" :induct (lw-pl-countdown index)
                         :in-theory (enable lw-complex-power)))))

(defthm lw-complex-reciprocal-power-cancel
  (implies (and (lw-complexp point) (not (equal point (cons 0 0))) (natp index))
           (equal (lw-complex-mul (lw-complex-power point index)
                                  (lw-complex-power (lw-complex-reciprocal point) index))
                  (cons 1 0)))
  :hints (("Goal" :use ((:instance lw-complex-power-product
                          (left point) (right (lw-complex-reciprocal point))))
                  :in-theory (disable lw-complex-power-product))))

(defun lw-pole-coefficient (residue offset index)
  (lw-complex-mul
   residue (lw-complex-power (lw-complex-reciprocal offset) (+ 1 (nfix index)))))

(defthm lw-pole-coefficient-rational
  (implies (and (lw-complexp residue) (lw-complexp offset) (natp index))
           (lw-complexp (lw-pole-coefficient residue offset index))))

(defthm lw-pole-unit-coefficient-scaled
  (implies (and (lw-complexp residue) (lw-complexp offset) (rationalp radius) (natp index))
           (equal (lw-pole-unit-coefficient residue offset radius index)
                  (lw-complex-scale (lw-rational-power radius index)
                                    (lw-pole-coefficient residue offset index))))
  :hints (("Goal" :use ((:instance lw-pole-unit-coefficient-formula (target index))))))

(defthm lw-pole-coefficient-cancel
  (implies (and (lw-complexp residue) (lw-complexp offset)
                (not (equal offset (cons 0 0))) (natp index))
           (equal (lw-complex-mul
                   (lw-complex-power offset (+ 1 index))
                   (lw-pole-coefficient residue offset index)) residue))
  :hints (("Goal" :use ((:instance lw-complex-reciprocal-power-cancel
                          (point offset) (index (+ 1 index)))
                        (:instance lw-complex-mul-left-commutes
                          (a (lw-complex-power offset (+ 1 index))) (b residue)
                          (c (lw-complex-power (lw-complex-reciprocal offset) (+ 1 index)))))
                  :in-theory (disable lw-complex-reciprocal-power-cancel
                                      lw-complex-mul-commutative lw-complex-mul-left-commutes))))

(local (in-theory (disable lw-pole-coefficient)))

(defthm lw-pole-coefficient-disk-implies-residue-disk
  (implies (and (lw-complexp residue) (lw-complex-diskp offset distance)
                (not (equal offset (cons 0 0))) (natp index)
                (lw-complex-diskp (lw-pole-coefficient residue offset index) cap))
           (lw-complex-diskp residue (* (lw-rational-power distance (+ 1 index)) cap)))
  :hints (("Goal" :use ((:instance lw-complex-power-disk (point offset) (radius distance) (index (+ 1 index)))
                        lw-pole-coefficient-cancel
                        (:instance lw-complex-mul-disk
                          (left (lw-complex-power offset (+ 1 index)))
                          (radius (lw-rational-power distance (+ 1 index)))
                          (right (lw-pole-coefficient residue offset index)) (other-radius cap)))
                  :in-theory (disable lw-complex-power-disk lw-complex-mul-disk
                                      lw-pole-coefficient-cancel))))

(defthm lw-pole-plus-remainder-disk
  (implies (and (lw-complexp residue) (lw-complex-diskp offset distance)
                (not (equal offset (cons 0 0))) (natp index)
                (lw-complex-diskp remainder remainder-cap)
                (lw-complex-diskp (lw-complex-add (lw-pole-coefficient residue offset index) remainder) cap))
           (lw-complex-diskp
            residue (* (lw-rational-power distance (+ 1 index)) (+ cap remainder-cap))))
  :hints (("Goal" :use ((:instance lw-complex-sub-disk
                          (left (lw-complex-add (lw-pole-coefficient residue offset index) remainder))
                          (radius cap) (right remainder) (other-radius remainder-cap))
                        (:instance lw-pole-coefficient-disk-implies-residue-disk
                          (cap (+ cap remainder-cap))))
                  :in-theory (disable lw-complex-sub-disk
                                      lw-pole-coefficient-disk-implies-residue-disk
                                      lw-complex-sub-add-first))))

(defthm lw-pole-finite-cauchy-residue-bound
  (implies (and (lw-complexp residue) (lw-complex-diskp offset distance)
                (not (equal offset (cons 0 0)))
                (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (natp index) (< index (len coefficients))
                (rationalp error) (< 0 error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check
                 coefficients (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count coefficients degree error) boundary-cap)
                (lw-complex-diskp
                 (lw-complex-add (lw-pole-coefficient residue offset index) (nth index coefficients)) cap))
           (lw-complex-diskp residue
                             (* (lw-rational-power distance (+ 1 index)) (+ cap boundary-cap error))))
  :hints (("Goal" :use ((:instance lw-cauchy-finite-coefficient-bound (target index) (cap boundary-cap))
                        (:instance lw-pole-plus-remainder-disk
                          (remainder (nth index coefficients)) (remainder-cap (+ boundary-cap error))))
                  :in-theory (disable lw-cauchy-finite-coefficient-bound lw-pole-plus-remainder-disk))))


(assert-event
 (equal (lw-complex-mul (lw-complex-power (cons 3 4) 3)
                        (lw-pole-coefficient (cons 1 2) (cons 3 4) 2))
        (cons 1 2)))
