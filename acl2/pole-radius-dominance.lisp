(in-package "ACL2")

(include-book "pole-dominance")

; The regular polynomial is expressed in the unit variable w, while the
; physical contour is z=R*w. Its j-th physical coefficient is divided by
; R^j. Residues retain their original zeta-zero arguments.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-conjugate lw-complex-norm-square
                 lw-complex-reciprocal lw-complex-power lw-complex-l1 lw-complex-polynomial
                 lw-complex-coefficient-at lw-complex-coefficient-mass
                 lw-rational-power lw-rational-power-product lw-rational-power-add-exponents
                 lw-zeta-pole-familyp lw-zeta-pole-datap lw-zeta-pole-clearance-check
                 lw-zeta-pole-residue lw-zeta-residue-denominator lw-zeta-residue-mass
                 lw-zeta-pole-coefficient-sum lw-pole-coefficient lw-pole-unit-coefficient
                 lw-pole-family-index lw-pole-tail-precision lw-resolvent-truncation-count
                 lw-geometric-index lw-geometric-threshold lw-phase-rotation lw-phase-denominator
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-cauchy-polynomial-average lw-cauchy-evaluation-sum
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-prd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-prd-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-prd-zero-times (equal (* 0 a) 0)))
(local (defthm lw-prd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-prd-left-commutes)))))
(local (defthm lw-prd-reciprocal-step
         (implies (and (rationalp radius) (< 0 radius) (natp index))
                  (equal (* radius (lw-rational-power (/ radius) (+ 1 index)))
                         (lw-rational-power (/ radius) index)))
         :hints (("Goal" :expand ((lw-rational-power (/ radius) (+ 1 index)))))
         :rule-classes nil))
(local (defthm lw-prd-multiply-equality
         (implies (equal a b) (equal (* a factor) (* b factor)))
         :rule-classes nil))
(local (defthm lw-prd-radius-identity
         (implies (and (rationalp radius) (< 0 radius) (natp index))
                  (equal (* mass (lw-rational-power (/ radius) index)
                            (lw-rational-power distance (+ 1 index)))
                         (* mass radius (lw-rational-power (/ radius) (+ 1 index))
                            (lw-rational-power distance (+ 1 index)))))
         :hints (("Goal" :use (lw-prd-reciprocal-step
                               (:instance lw-prd-multiply-equality
                                 (a (* radius (lw-rational-power (/ radius) (+ 1 index))))
                                 (b (lw-rational-power (/ radius) index))
                                 (factor (* mass (lw-rational-power distance (+ 1 index))))))))
         :rule-classes nil))
(local (defthm lw-prd-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prd-nth-rational
         (implies (and (lw-complex-coefficientsp coefficients) (natp index) (< index (len coefficients)))
                  (lw-complexp (nth index coefficients)))
         :hints (("Goal" :use ((:instance lw-complex-coefficient-at-rational (target index) (offset 0))
                               (:instance lw-complex-coefficient-at-nth (target index) (offset 0)))
                         :in-theory (disable lw-complex-coefficient-at-rational lw-complex-coefficient-at-nth)))))

(defun lw-pole-regular-coefficient (coefficients radius index)
  (lw-complex-scale (lw-rational-power (/ radius) index) (nth index coefficients)))

(defthm lw-pole-regular-coefficient-rational
  (implies (and (lw-complex-coefficientsp coefficients) (rationalp radius) (< 0 radius)
                (natp index) (< index (len coefficients)))
           (lw-complexp (lw-pole-regular-coefficient coefficients radius index))))

(defthm lw-pole-regular-coefficient-cauchy-bound
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (<= (len coefficients) (+ 1 degree))
                (natp index) (< index (len coefficients)) (rationalp radius) (< 0 radius)
                (rationalp error) (< 0 error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check
                 coefficients (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count coefficients degree error) boundary-cap))
           (lw-complex-diskp (lw-pole-regular-coefficient coefficients radius index)
                             (* (+ boundary-cap error) (lw-rational-power (/ radius) index))))
  :hints (("Goal" :use ((:instance lw-cauchy-finite-coefficient-bound (target index) (cap boundary-cap))
                        (:instance lw-rational-power-nonnegative (base (/ radius)) (exponent index))
                        (:instance lw-complex-scale-disk (point (nth index coefficients))
                          (factor (lw-rational-power (/ radius) index)) (radius (+ boundary-cap error))))
                  :in-theory (disable lw-cauchy-finite-coefficient-bound lw-rational-power-nonnegative
                                      lw-complex-scale-disk))))

(local (in-theory (disable lw-pole-regular-coefficient)))

(defun lw-pole-radius-remainder-index (distance clearance radius other-mass regular-mass)
  (max (lw-pole-family-index distance clearance (* 2 other-mass))
       (lw-pole-family-index distance radius (* 2 radius regular-mass))))

(defthm lw-pole-radius-remainder-index-natural
  (natp (lw-pole-radius-remainder-index distance clearance radius other-mass regular-mass))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-pole-scaled-regular-quarter-budget
  (implies (and (rationalp distance) (<= 0 distance) (rationalp radius) (< 0 radius) (< distance radius)
                (rationalp mass) (<= 0 mass) (natp index)
                (<= (lw-pole-family-index distance radius (* 2 radius mass)) index))
           (<= (* mass (lw-rational-power (/ radius) index)
                  (lw-rational-power distance (+ 1 index))) 1/4))
  :hints (("Goal" :use ((:instance lw-pole-family-quarter-budget (clearance radius) (mass (* radius mass)))
                        (:instance lw-prd-product-nonnegative (a radius) (b mass))
                        lw-prd-radius-identity)
                  :in-theory (disable lw-pole-family-quarter-budget))))


(defthm lw-zeta-pole-radius-polynomial-family-dominance
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance) (lw-zeta-pole-clearance-check center entries clearance)
                (lw-complex-diskp zero first-cap) (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (posp multiplicity)
                (lw-complex-diskp (lw-complex-sub center zero) distance)
                (not (equal center zero)) (< distance clearance)
                (rationalp radius) (< 0 radius) (< distance radius)
                (lw-complex-coefficientsp coefficients) (natp degree) (<= (len coefficients) (+ 1 degree))
                (natp index) (< index (len coefficients))
                (rationalp error) (< 0 error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation degree) 0
                  (lw-cauchy-coefficient-count coefficients degree error) boundary-cap)
                (<= (lw-pole-radius-remainder-index
                     distance clearance radius (* (* first-cap second-cap) (lw-zeta-residue-mass entries)) (* (*
                       first-cap second-cap) (+ boundary-cap error))) index)
                (lw-complex-diskp (lw-complex-add (lw-complex-add (lw-pole-coefficient (lw-zeta-pole-residue zero
                  multiplicity) (lw-complex-sub center zero) index) (lw-zeta-pole-coefficient-sum center entries
                  index)) (lw-pole-regular-coefficient coefficients radius index)) cap))
           (<= 1/2 (* first-cap second-cap cap (lw-rational-power distance (+ 1 index)))))
  :hints (("Goal" :use (lw-zeta-residue-mass-valid lw-pole-regular-coefficient-cauchy-bound
    (:instance lw-prd-product-nonnegative (a first-cap) (b second-cap))
    (:instance lw-prd-product-nonnegative (a (* first-cap second-cap)) (b (lw-zeta-residue-mass entries)))
    (:instance lw-prd-product-nonnegative (a (* first-cap second-cap)) (b (+ boundary-cap error)))
    (:instance lw-complex-sub-disk (left (lw-complex-add (lw-complex-add (lw-pole-coefficient (lw-zeta-pole-residue
      zero multiplicity) (lw-complex-sub center zero) index) (lw-zeta-pole-coefficient-sum center entries index))
      (lw-pole-regular-coefficient coefficients radius index))) (radius cap) (right (lw-pole-regular-coefficient
      coefficients radius index)) (other-radius (* (+ boundary-cap error) (lw-rational-power (/ radius) index))))
    (:instance lw-zeta-selected-pole-family-lower (cap (+ cap (* (+ boundary-cap error) (lw-rational-power (/ radius)
      index)))))
    (:instance lw-pole-family-quarter-budget (mass (* (* first-cap second-cap) (lw-zeta-residue-mass entries))))
    (:instance lw-pole-scaled-regular-quarter-budget (mass (* (* first-cap second-cap) (+ boundary-cap error)))))
    :in-theory (e/d (lw-pole-radius-remainder-index)
                    (lw-zeta-residue-mass-valid lw-pole-regular-coefficient-cauchy-bound
                     lw-complex-sub-disk lw-complex-sub-add-first
                     lw-zeta-selected-pole-family-lower lw-pole-family-quarter-budget
                     lw-pole-scaled-regular-quarter-budget)))))

; Physical radius 2 divides the quadratic coefficient by 4.
(assert-event
 (equal (lw-pole-regular-coefficient (list (cons 1 0) (cons 2 0) (cons 20 12)) 2 2)
        (cons 5 3)))

; The index constructor also accepts a selected pole distance above 1.
(assert-event
 (let ((index (lw-pole-radius-remainder-index 2 4 3 5 7)))
   (and (natp index)
        (<= (* 5 (lw-rational-power 2 (+ 1 index))
               (lw-rational-power 1/4 (+ 1 index))) 1/4)
        (<= (* 7 (lw-rational-power 1/3 index)
               (lw-rational-power 2 (+ 1 index))) 1/4))))

