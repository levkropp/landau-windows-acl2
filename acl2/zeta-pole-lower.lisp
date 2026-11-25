(in-package "ACL2")

(include-book "pole-lower")

; The zeta principal-part residue is -multiplicity/(rho*(rho-1)).
; Its exact denominator identity forces a coefficient lower constraint.

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
                 lw-complex-mul-subtract
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


(local (defthm lw-zpl-zero-times (equal (* 0 a) 0)))
(local (defthm lw-zpl-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-zpl-scale-one
         (implies (rationalp factor)
                  (equal (lw-complex-scale factor (cons 1 0)) (cons factor 0)))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-zpl-sub-one-nonzero
         (implies (and (lw-complexp zero) (not (equal zero (cons 1 0))))
                  (not (equal (lw-complex-sub zero (cons 1 0)) (cons 0 0))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(defun lw-zeta-residue-denominator (zero)
  (lw-complex-mul zero (lw-complex-sub zero (cons 1 0))))

(defthm lw-zeta-residue-denominator-rational
  (implies (lw-complexp zero) (lw-complexp (lw-zeta-residue-denominator zero))))

(defthm lw-zeta-residue-denominator-nonzero
  (implies (and (lw-complexp zero) (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))))
           (not (equal (lw-zeta-residue-denominator zero) (cons 0 0)))))

(defun lw-zeta-pole-residue (zero multiplicity)
  (lw-complex-scale (- (nfix multiplicity))
                    (lw-complex-reciprocal (lw-zeta-residue-denominator zero))))

(defthm lw-zeta-pole-residue-rational
  (implies (and (lw-complexp zero) (natp multiplicity))
           (lw-complexp (lw-zeta-pole-residue zero multiplicity))))

(local (in-theory (disable lw-zeta-residue-denominator)))

(defthm lw-zeta-pole-residue-cancel
  (implies (and (lw-complexp zero) (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0)))
                (natp multiplicity))
           (equal (lw-complex-mul (lw-zeta-residue-denominator zero)
                                  (lw-zeta-pole-residue zero multiplicity))
                  (cons (- multiplicity) 0)))
  :hints (("Goal" :use ((:instance lw-complex-reciprocal-inverse (point (lw-zeta-residue-denominator zero)))
                        (:instance lw-complex-scale-product
                          (factor (- multiplicity)) (left (lw-zeta-residue-denominator zero))
                          (right (lw-complex-reciprocal (lw-zeta-residue-denominator zero)))))
                  :in-theory (disable lw-complex-scale-product lw-complex-reciprocal-inverse
                                      lw-complex-mul-commutative lw-complex-mul-left-commutes))))

(local (in-theory (disable lw-zeta-pole-residue)))

(defthm lw-zeta-residue-disk-lower
  (implies (and (lw-complex-diskp zero first-cap)
                (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (natp multiplicity)
                (lw-complex-diskp (lw-zeta-pole-residue zero multiplicity) cap))
           (<= multiplicity (* first-cap second-cap cap)))
  :hints (("Goal" :use (lw-zeta-pole-residue-cancel
                        (:instance lw-complex-mul-disk
                          (left zero) (radius first-cap)
                          (right (lw-complex-sub zero (cons 1 0))) (other-radius second-cap))
                        (:instance lw-complex-mul-disk
                          (left (lw-zeta-residue-denominator zero)) (radius (* first-cap second-cap))
                          (right (lw-zeta-pole-residue zero multiplicity)) (other-radius cap))
                        (:instance lw-complex-disk-coordinates
                          (point (cons (- multiplicity) 0)) (radius (* first-cap second-cap cap))))
                  :in-theory (e/d (lw-zeta-residue-denominator)
                                  (lw-zeta-pole-residue-cancel lw-complex-mul-disk
                                   lw-complex-disk-coordinates lw-complex-mul-commutative
                                   lw-complex-mul-left-commutes)))))

(defthm lw-zeta-pole-finite-cauchy-lower
  (implies (and (lw-complex-diskp zero first-cap)
                (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (posp multiplicity)
                (lw-complex-diskp offset distance) (not (equal offset (cons 0 0)))
                (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree)) (natp index) (< index (len coefficients))
                (rationalp error) (< 0 error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check
                 coefficients (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count coefficients degree error) boundary-cap)
                (lw-complex-diskp
                 (lw-complex-add (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity) offset index)
                                 (nth index coefficients)) cap))
           (<= multiplicity
               (* first-cap second-cap (lw-rational-power distance (+ 1 index))
                  (+ cap boundary-cap error))))
  :hints (("Goal" :use ((:instance lw-pole-finite-cauchy-residue-bound
                          (residue (lw-zeta-pole-residue zero multiplicity)))
                        (:instance lw-zeta-residue-disk-lower
                          (cap (* (lw-rational-power distance (+ 1 index)) (+ cap boundary-cap error)))))
                  :in-theory (disable lw-pole-finite-cauchy-residue-bound lw-zeta-residue-disk-lower))))

(defthm lw-zeta-pole-finite-cauchy-obstruction
  (implies (and (lw-complex-diskp zero first-cap)
                (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (posp multiplicity)
                (lw-complex-diskp offset distance) (not (equal offset (cons 0 0)))
                (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree)) (natp index) (< index (len coefficients))
                (rationalp error) (< 0 error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check
                 coefficients (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count coefficients degree error) boundary-cap)
                (lw-complex-diskp
                 (lw-complex-add (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity) offset index)
                                 (nth index coefficients)) cap)
                (< (* first-cap second-cap (lw-rational-power distance (+ 1 index))
                      (+ cap boundary-cap error)) multiplicity))
           nil)
  :hints (("Goal" :use (lw-zeta-pole-finite-cauchy-lower)
                  :in-theory (disable lw-zeta-pole-finite-cauchy-lower)))
  :rule-classes nil)

; Direct values test the sign and multiplicity in the residue formula.
(assert-event
 (and (equal (lw-zeta-pole-residue (cons 1/2 1) 3) (cons 12/5 0))
      (equal (lw-zeta-pole-residue (cons 3/4 2) 2) (cons 2144/4745 512/4745))))
