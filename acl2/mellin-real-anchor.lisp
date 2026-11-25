(in-package "ACL2")

(include-book "mellin-pole-bridge")

; Bound the retained real moment using its own finite pole-family model.
; The model has no selected pole: multiplicity zero contributes exactly
; zero. All listed pole and regular-part clearances remain explicit.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-complex-reciprocal
                 lw-complex-norm-square lw-complex-l1 lw-rational-power
                 lw-zeta-pole-residue lw-zeta-residue-mass lw-zeta-pole-familyp
                 lw-zeta-pole-clearance-check lw-zeta-pole-coefficient-sum lw-pole-coefficient
                 lw-pole-regular-coefficient lw-zeta-model-coefficient lw-zeta-model-polynomial
                 lw-mellin-model-boundary-check lw-mellin-integral lw-mellin-improper-polynomial
                 lw-mellin-improper-polynomial-degree lw-mellin-common-cells lw-mellin-common-cutoff
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-geometric-index lw-geometric-threshold lw-log-signal-bounds
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mra-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-mra-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mra-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-mra-zero-pole
         (implies (and (lw-complexp offset) (natp index))
                  (equal (lw-pole-coefficient (cons 0 0) offset index) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-pole-coefficient lw-complex-mul)))))

(defun lw-mellin-real-anchor-bound (entries clearance radius index boundary-cap regular-error comparison-cap error)
  (+ (* (lw-zeta-residue-mass entries) (lw-rational-power (/ clearance) (+ 1 index)))
     (* (+ boundary-cap regular-error) (lw-rational-power (/ radius) index))
     comparison-cap error))

(defthm lw-mellin-real-anchor-model-bound
  (implies (and (rationalp sigma) (natp index) (rationalp inner-radius) (<= 0 inner-radius) (< 2 (- sigma inner-radius))
                (rationalp error) (< 0 error) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance) (lw-zeta-pole-clearance-check (cons sigma 0) entries clearance)
                (lw-complex-coefficientsp coefficients) (natp regular-degree)
                (<= (len coefficients) (+ 1 regular-degree)) (< index (len coefficients))
                (rationalp radius) (< 0 radius) (rationalp regular-error) (< 0 regular-error)
                (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation regular-degree) 0
                  (lw-cauchy-coefficient-count coefficients regular-degree regular-error) boundary-cap)
                (rationalp comparison-cap) (<= 0 comparison-cap) (lw-mellin-model-boundary-check sigma 0 index
                  inner-radius error (cons 2 0) 0 entries coefficients radius comparison-cap))
           (lw-complex-diskp (lw-mellin-integral sigma 0 index (* 1/64 error)) (lw-mellin-real-anchor-bound entries
             clearance radius index boundary-cap regular-error comparison-cap error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-pole-model-coefficient-comparison (height 0) (zero (cons 2 0)) (multiplicity 0))
    (:instance lw-zeta-pole-coefficient-sum-upper (center (cons sigma 0)))
    (:instance lw-pole-regular-coefficient-cauchy-bound (degree regular-degree) (error regular-error))
    (:instance lw-complex-add-disk (left (lw-zeta-pole-coefficient-sum (cons sigma 0) entries index)) (right
      (lw-pole-regular-coefficient coefficients radius index)) (radius (* (lw-zeta-residue-mass entries)
      (lw-rational-power (/ clearance) (+ 1 index)))) (other-radius (* (+ boundary-cap regular-error)
      (lw-rational-power (/ radius) index))))
    (:instance lw-complex-difference-triangle (left (lw-mellin-integral sigma 0 index (* 1/64 error))) (middle
      (lw-zeta-model-coefficient (cons sigma 0) (cons 2 0) 0 entries coefficients radius index)) (right (cons 0 0))
      (radius (+ comparison-cap error)) (other-radius (+ (* (lw-zeta-residue-mass entries) (lw-rational-power (/
      clearance) (+ 1 index))) (* (+ boundary-cap regular-error) (lw-rational-power (/ radius) index))))))
    :in-theory (disable lw-mellin-pole-model-coefficient-comparison lw-zeta-pole-coefficient-sum-upper
                        lw-pole-regular-coefficient-cauchy-bound lw-complex-add-disk lw-complex-difference-triangle))))

(local (in-theory (disable lw-mellin-real-anchor-bound)))

(defthm lw-mellin-real-anchor-lower
  (implies (and (rationalp sigma) (natp index) (rationalp inner-radius) (<= 0 inner-radius) (< 2 (- sigma inner-radius))
                (rationalp error) (< 0 error) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance) (lw-zeta-pole-clearance-check (cons sigma 0) entries clearance)
                (lw-complex-coefficientsp coefficients) (natp regular-degree)
                (<= (len coefficients) (+ 1 regular-degree)) (< index (len coefficients))
                (rationalp radius) (< 0 radius) (rationalp regular-error) (< 0 regular-error)
                (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation regular-degree) 0
                  (lw-cauchy-coefficient-count coefficients regular-degree regular-error) boundary-cap)
                (rationalp comparison-cap) (<= 0 comparison-cap) (lw-mellin-model-boundary-check sigma 0 index
                  inner-radius error (cons 2 0) 0 entries coefficients radius comparison-cap))
           (<= (- (car (lw-mellin-integral sigma 0 index (* 1/64 error)))) (lw-mellin-real-anchor-bound entries
             clearance radius index boundary-cap regular-error comparison-cap error)))
  :hints (("Goal" :use (lw-mellin-real-anchor-model-bound
                        (:instance lw-complex-disk-coordinates (point (lw-mellin-integral sigma 0 index (* 1/64
                          error))) (radius (lw-mellin-real-anchor-bound entries clearance radius index boundary-cap
                          regular-error comparison-cap error))))
                  :in-theory (disable lw-mellin-real-anchor-model-bound lw-complex-disk-coordinates)
                  :cases ((<= 0 (car (lw-mellin-integral sigma 0 index (* 1/64 error))))))))

