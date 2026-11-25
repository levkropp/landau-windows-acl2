(in-package "ACL2")

(include-book "mellin-improper-polynomial")
(include-book "pole-radius-dominance")
(include-book "polynomial-difference")

; A finite model polynomial has the recorded pole coefficients and the
; regular coefficients rescaled from their physical contour. Compare its
; boundary with the polynomial built from the actual Mellin evaluator.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-conjugate lw-complex-norm-square
                 lw-complex-reciprocal lw-complex-power lw-complex-l1 lw-complex-polynomial
                 lw-complex-coefficient-at lw-complex-coefficient-mass
                 lw-rational-power lw-rational-power-product lw-rational-power-add-exponents
                 lw-zeta-pole-familyp lw-zeta-pole-datap lw-zeta-pole-clearance-check
                 lw-zeta-pole-residue lw-zeta-residue-denominator lw-zeta-residue-mass
                 lw-zeta-pole-coefficient-sum lw-pole-coefficient lw-pole-unit-coefficient
                 lw-pole-regular-coefficient lw-pole-family-index lw-pole-radius-remainder-index
                 lw-geometric-index lw-geometric-threshold lw-phase-rotation lw-phase-denominator
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-cauchy-polynomial-average lw-cauchy-evaluation-sum lw-polynomial-difference
                 lw-mellin-integral lw-mellin-improper-polynomial lw-mellin-improper-polynomial-degree
                 lw-mellin-common-cells lw-mellin-common-cutoff
                 lw-mellin-shift-polynomial lw-mellin-shift-polynomial-nodes lw-mellin-shift-polynomial-degree
                 lw-log-signal-bounds lw-mellin-sample lw-mellin-sample-kernel-form
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mpb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mpb-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mpb-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-mpb-nth-rational
         (implies (and (lw-complex-coefficientsp coefficients) (natp index) (< index (len coefficients)))
                  (lw-complexp (nth index coefficients)))
         :hints (("Goal" :use ((:instance lw-complex-coefficient-at-rational (target index) (offset 0))
                               (:instance lw-complex-coefficient-at-nth (target index) (offset 0)))
                         :in-theory (disable lw-complex-coefficient-at-rational lw-complex-coefficient-at-nth)))))

(defun lw-zeta-model-coefficient (center zero multiplicity entries coefficients radius index)
  (lw-complex-add
   (lw-complex-add
    (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity) (lw-complex-sub center zero) index)
    (lw-zeta-pole-coefficient-sum center entries index))
   (lw-complex-scale (lw-rational-power (/ radius) index)
                     (lw-complex-coefficient-at coefficients index 0))))

(defthm lw-zeta-model-coefficient-rational
  (implies (and (lw-complexp center) (lw-complexp zero) (natp multiplicity) (lw-zeta-pole-familyp entries)
                (lw-complex-coefficientsp coefficients) (rationalp radius) (< 0 radius) (natp index))
           (lw-complexp (lw-zeta-model-coefficient center zero multiplicity entries coefficients radius index))))

(defthm lw-zeta-model-coefficient-selected
  (implies (and (lw-complex-coefficientsp coefficients) (natp index) (< index (len coefficients)))
           (equal
            (lw-zeta-model-coefficient center zero multiplicity entries coefficients radius index)
            (lw-complex-add
             (lw-complex-add
              (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity) (lw-complex-sub center zero) index)
              (lw-zeta-pole-coefficient-sum center entries index))
             (lw-pole-regular-coefficient coefficients radius index))))
  :hints (("Goal" :use ((:instance lw-complex-coefficient-at-nth (target index) (offset 0)))
                  :in-theory (e/d (lw-pole-regular-coefficient) (lw-complex-coefficient-at-nth)))))

(local (in-theory (disable lw-zeta-model-coefficient)))

(defun lw-zeta-model-polynomial (center zero multiplicity entries coefficients radius offset count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (cons (lw-zeta-model-coefficient center zero multiplicity entries coefficients radius offset)
          (lw-zeta-model-polynomial center zero multiplicity entries coefficients radius (+ 1 offset) (- count 1)))))

(defthm lw-zeta-model-polynomial-valid
  (implies (and (lw-complexp center) (lw-complexp zero) (natp multiplicity) (lw-zeta-pole-familyp entries)
                (lw-complex-coefficientsp coefficients) (rationalp radius) (< 0 radius)
                (natp offset) (natp count))
           (and (lw-complex-coefficientsp
                 (lw-zeta-model-polynomial center zero multiplicity entries coefficients radius offset count))
                (equal (len (lw-zeta-model-polynomial center zero multiplicity entries coefficients radius offset
                  count))
                       count)))
  :hints (("Goal" :induct (lw-zeta-model-polynomial center zero multiplicity entries coefficients radius offset
    count))))

(local (defun lw-mpb-nth-induct (offset count index)
         (declare (xargs :measure (nfix count)))
         (if (or (zp count) (zp index)) (list offset count index)
           (lw-mpb-nth-induct (+ 1 offset) (- count 1) (- index 1)))))

(defthm lw-zeta-model-polynomial-nth
  (implies (and (lw-complexp center) (lw-complexp zero) (natp multiplicity) (lw-zeta-pole-familyp entries)
                (lw-complex-coefficientsp coefficients) (rationalp radius) (< 0 radius)
                (natp offset) (natp count) (natp index) (< index count))
           (equal
            (nth index (lw-zeta-model-polynomial center zero multiplicity entries coefficients radius offset count))
            (lw-zeta-model-coefficient center zero multiplicity entries coefficients radius (+ offset index))))
  :hints (("Goal" :induct (lw-mpb-nth-induct offset count index)
                  :expand ((lw-zeta-model-polynomial center zero multiplicity entries coefficients radius offset count))
                  :in-theory (enable nth))))

(local (in-theory (disable lw-zeta-model-polynomial)))



(defun lw-mellin-model-boundary-check
    (sigma height index inner-radius error zero multiplicity entries coefficients radius comparison-cap)
  (let* ((actual (lw-mellin-improper-polynomial sigma height index inner-radius error))
         (degree (lw-mellin-improper-polynomial-degree sigma height index inner-radius error))
         (model (lw-zeta-model-polynomial (cons sigma height) zero multiplicity entries coefficients radius 0 (+ 1
           degree)))
         (difference (lw-polynomial-difference actual model)))
    (lw-cauchy-boundary-check
     difference (lw-cauchy-orbit-rotation degree) 0
     (lw-cauchy-coefficient-count difference degree (* 1/2 error)) comparison-cap)))

(defthm lw-mellin-pole-model-coefficient-comparison
  (implies (and (rationalp sigma) (rationalp height) (natp index)
                (rationalp inner-radius) (<= 0 inner-radius) (< 2 (- sigma inner-radius))
                (rationalp error) (< 0 error) (lw-complexp zero) (natp multiplicity)
                (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
                (rationalp radius) (< 0 radius) (rationalp comparison-cap) (<= 0 comparison-cap)
                (lw-mellin-model-boundary-check sigma height index inner-radius error zero multiplicity entries
                  coefficients radius comparison-cap))
           (lw-complex-diskp (lw-complex-sub (lw-mellin-integral sigma height index (* 1/64 error))
             (lw-zeta-model-coefficient (cons sigma height) zero multiplicity entries coefficients radius index)) (+
             comparison-cap error)))
  :hints (("Goal" :use (
    (:instance lw-mellin-improper-polynomial-valid (target index) (radius inner-radius))
    (:instance lw-mellin-improper-polynomial-moment-comparison (target index) (radius inner-radius))
    (:instance lw-zeta-model-polynomial-valid (center (cons sigma height)) (offset 0) (count (+ 1
      (lw-mellin-improper-polynomial-degree sigma height index inner-radius error))))
    (:instance lw-zeta-model-polynomial-nth (center (cons sigma height)) (offset 0) (count (+ 1
      (lw-mellin-improper-polynomial-degree sigma height index inner-radius error))))
    (:instance lw-polynomial-difference-cauchy-bound (left (lw-mellin-improper-polynomial sigma height index
      inner-radius error)) (right (lw-zeta-model-polynomial (cons sigma height) zero multiplicity entries coefficients
      radius 0 (+ 1 (lw-mellin-improper-polynomial-degree sigma height index inner-radius error)))) (degree
      (lw-mellin-improper-polynomial-degree sigma height index inner-radius error)) (error (* 1/2 error)) (cap
      comparison-cap))
    (:instance lw-complex-difference-triangle (left (lw-mellin-integral sigma height index (* 1/64 error))) (middle
      (nth index (lw-mellin-improper-polynomial sigma height index inner-radius error))) (right
      (lw-zeta-model-coefficient (cons sigma height) zero multiplicity entries coefficients radius index)) (radius (*
      1/2 error)) (other-radius (+ comparison-cap (* 1/2 error))))
    (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-integral sigma height index (* 1/64 error))
      (lw-zeta-model-coefficient (cons sigma height) zero multiplicity entries coefficients radius index))) (radius (+
      (* 1/2 error) comparison-cap (* 1/2 error))) (cap (+ comparison-cap error))))
    :in-theory (disable lw-mellin-improper-polynomial-valid lw-mellin-improper-polynomial-moment-comparison
                        lw-zeta-model-polynomial-valid lw-zeta-model-polynomial-nth
                        lw-polynomial-difference-cauchy-bound lw-zeta-model-coefficient-selected
                        lw-complex-difference-triangle)
    :do-not-induct t)))

(defthm lw-mellin-pole-model-radius-dominance
  (implies (and (rationalp sigma) (rationalp height) (natp index)
                (rationalp inner-radius) (<= 0 inner-radius) (< 2 (- sigma inner-radius))
                (rationalp error) (< 0 error) (lw-complexp zero) (posp multiplicity)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0)))
                (lw-zeta-pole-familyp entries) (rationalp clearance) (< 0 clearance)
                (lw-zeta-pole-clearance-check (cons sigma height) entries clearance)
                (lw-complex-diskp zero first-cap) (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (lw-complex-diskp (lw-complex-sub (cons sigma height) zero) distance)
                (not (equal (cons sigma height) zero)) (< distance clearance)
                (rationalp radius) (< 0 radius) (< distance radius)
                (lw-complex-coefficientsp coefficients) (natp regular-degree)
                (<= (len coefficients) (+ 1 regular-degree)) (< index (len coefficients))
                (rationalp regular-error) (< 0 regular-error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation regular-degree) 0
                  (lw-cauchy-coefficient-count coefficients regular-degree regular-error) boundary-cap)
                (<= (lw-pole-radius-remainder-index distance clearance radius
                     (* (* first-cap second-cap) (lw-zeta-residue-mass entries)) (* (* first-cap second-cap) (+
                       boundary-cap regular-error))) index)
                (rationalp comparison-cap) (<= 0 comparison-cap) (lw-mellin-model-boundary-check sigma height index
                  inner-radius error zero multiplicity entries coefficients radius comparison-cap)
                (lw-complex-diskp (lw-mellin-integral sigma height index (* 1/64 error)) moment-cap))
           (<= 1/2 (* first-cap second-cap (+ moment-cap comparison-cap error)
                      (lw-rational-power distance (+ 1 index)))))
  :hints (("Goal" :use (lw-mellin-pole-model-coefficient-comparison
    (:instance lw-complex-subtract-cancel (a (lw-mellin-integral sigma height index (* 1/64 error))) (b
      (lw-zeta-model-coefficient (cons sigma height) zero multiplicity entries coefficients radius index)))
    (:instance lw-complex-sub-disk (left (lw-mellin-integral sigma height index (* 1/64 error))) (radius moment-cap)
      (right (lw-complex-sub (lw-mellin-integral sigma height index (* 1/64 error)) (lw-zeta-model-coefficient (cons
      sigma height) zero multiplicity entries coefficients radius index))) (other-radius (+ comparison-cap error)))
    (:instance lw-zeta-pole-radius-polynomial-family-dominance (center (cons sigma height)) (degree regular-degree)
      (error regular-error) (cap (+ moment-cap comparison-cap error))))
    :in-theory (disable lw-mellin-pole-model-coefficient-comparison lw-complex-subtract-cancel
                        lw-complex-sub-disk lw-complex-sub-add-first
                        lw-zeta-pole-radius-polynomial-family-dominance))))

