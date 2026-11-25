(in-package "ACL2")

(include-book "zeta-pole-sums")

; A computed index absorbs the complete contribution of a separated
; finite family of other poles, including their recorded multiplicities.

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




(local (in-theory (disable lw-zeta-pole-familyp lw-zeta-pole-datap lw-zeta-pole-clearance-check
                           lw-zeta-pole-coefficient-sum lw-zeta-residue-mass
                           lw-zeta-pole-residue lw-zeta-residue-denominator lw-pole-coefficient
                           lw-rational-power-product lw-rational-power-add-exponents)))

(local (defthm lw-pd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-pd-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-pd-strict-multiply
         (implies (and (rationalp a) (rationalp b) (< a b) (rationalp factor) (< 0 factor))
                  (< (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-pd-small-quotient
         (implies (and (rationalp numerator) (<= 0 numerator)
                       (rationalp denominator) (< 0 denominator) (< numerator denominator))
                  (and (rationalp (/ numerator denominator))
                       (<= 0 (/ numerator denominator)) (< (/ numerator denominator) 1)))
         :hints (("Goal" :use ((:instance inverse-of-* (x denominator))
                              (:instance lw-pd-strict-multiply
                                (a numerator) (b denominator) (factor (/ denominator))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-pd-unscale
         (implies (and (rationalp value) (<= 0 value)
                       (rationalp scale) (< 0 scale) (<= scale 1)
                       (rationalp error) (<= (/ value scale) error))
                  (<= value error))
         :hints (("Goal" :use ((:instance lw-reciprocal-antitone (left scale) (right 1))
                              (:instance lw-pd-multiply-order (a 1) (b (/ scale)) (factor value)))
                         :in-theory (disable lw-reciprocal-antitone)))
         :rule-classes nil))

(defthm lw-rational-power-computed-decay
  (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1)
                (rationalp error) (< 0 error) (natp index)
                (<= (lw-resolvent-truncation-count ratio error) index))
           (<= (lw-rational-power ratio index) error))
  :hints (("Goal" :use ((:instance lw-resolvent-truncation-count-adequate (radius ratio) (count index))
                        (:instance lw-rational-power-nonnegative (base ratio) (exponent index))
                        (:instance lw-pd-unscale (value (lw-rational-power ratio index)) (scale (- 1 ratio))))
                  :in-theory (disable lw-resolvent-truncation-count-adequate lw-rational-power-nonnegative
                                      lw-resolvent-truncation-count))))

(defun lw-pole-tail-precision (mass) (/ 1 (* 2 (+ 1 mass))))

(defthm lw-pole-tail-precision-adequate
  (implies (and (rationalp mass) (<= 0 mass))
           (and (rationalp (lw-pole-tail-precision mass)) (< 0 (lw-pole-tail-precision mass))
                (<= (* mass (lw-pole-tail-precision mass)) 1/2)))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator mass) (divisor (* 2 (+ 1 mass))) (bound 1/2))))))

(defun lw-pole-family-index (distance clearance mass)
  (lw-resolvent-truncation-count (/ distance clearance) (lw-pole-tail-precision mass)))

(defthm lw-pole-family-index-natural
  (and (natp (lw-pole-family-index distance clearance mass))
       (< 0 (lw-pole-family-index distance clearance mass)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-pole-family-tail-budget
  (implies (and (rationalp distance) (<= 0 distance)
                (rationalp clearance) (< 0 clearance) (< distance clearance)
                (rationalp mass) (<= 0 mass) (natp index)
                (<= (lw-pole-family-index distance clearance mass) index))
           (<= (* mass (lw-rational-power distance (+ 1 index))
                  (lw-rational-power (/ clearance) (+ 1 index))) 1/2))
  :hints (("Goal" :use ((:instance lw-pd-small-quotient (numerator distance) (denominator clearance))
                        lw-pole-tail-precision-adequate
                        (:instance lw-rational-power-computed-decay
                          (ratio (/ distance clearance)) (error (lw-pole-tail-precision mass)) (index (+ 1 index)))
                        (:instance lw-rational-power-product (left distance) (right (/ clearance)) (exponent (+ 1 index)))
                        (:instance lw-pd-multiply-order
                          (a (lw-rational-power (/ distance clearance) (+ 1 index)))
                          (b (lw-pole-tail-precision mass)) (factor mass)))
                  :in-theory (disable lw-pole-tail-precision lw-pole-tail-precision-adequate
                                      lw-rational-power-computed-decay))))

(local (in-theory (disable lw-pole-family-index lw-pole-tail-precision)))

(defthm lw-zeta-selected-pole-family-dominance
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance)
                (lw-zeta-pole-clearance-check center entries clearance)
                (lw-complex-diskp zero first-cap)
                (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (posp multiplicity)
                (lw-complex-diskp (lw-complex-sub center zero) distance)
                (< distance clearance) (not (equal center zero)) (natp index)
                (<= (lw-pole-family-index distance clearance
                                          (* first-cap second-cap (lw-zeta-residue-mass entries))) index)
                (lw-complex-diskp
                 (lw-complex-add
                  (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                                       (lw-complex-sub center zero) index)
                  (lw-zeta-pole-coefficient-sum center entries index)) cap))
           (<= 1/2 (* first-cap second-cap cap (lw-rational-power distance (+ 1 index)))))
  :hints (("Goal" :use (lw-zeta-selected-pole-family-lower lw-zeta-residue-mass-valid
                        (:instance lw-pole-family-tail-budget
                          (mass (* first-cap second-cap (lw-zeta-residue-mass entries)))))
                  :in-theory (disable lw-zeta-selected-pole-family-lower lw-zeta-residue-mass-valid
                                      lw-pole-family-tail-budget)
                  :nonlinearp t)))

; Exercise the actual index constructor at a nontrivial separation ratio.
(assert-event
 (let ((index (lw-pole-family-index 1/2 3/4 6)))
   (and (natp index)
        (<= (* 3 (lw-rational-power 1/2 (+ 1 index))
               (lw-rational-power 4/3 (+ 1 index))) 1/4))))

(defthm lw-pole-family-quarter-budget
  (implies (and (rationalp distance) (<= 0 distance)
                (rationalp clearance) (< 0 clearance) (< distance clearance)
                (rationalp mass) (<= 0 mass) (natp index)
                (<= (lw-pole-family-index distance clearance (* 2 mass)) index))
           (<= (* mass (lw-rational-power distance (+ 1 index))
                  (lw-rational-power (/ clearance) (+ 1 index))) 1/4))
  :hints (("Goal" :use ((:instance lw-pole-family-tail-budget (mass (* 2 mass))))
                  :in-theory (disable lw-pole-family-tail-budget))))

(defun lw-pole-remainder-index (distance clearance other-mass regular-mass)
  (max (lw-pole-family-index distance clearance (* 2 other-mass))
       (lw-pole-family-index distance 1 (* 2 regular-mass))))

(defthm lw-pole-remainder-index-natural
  (natp (lw-pole-remainder-index distance clearance other-mass regular-mass))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-zeta-pole-polynomial-family-dominance
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance)
                (lw-zeta-pole-clearance-check center entries clearance)
                (lw-complex-diskp zero first-cap)
                (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (posp multiplicity)
                (lw-complex-diskp (lw-complex-sub center zero) distance)
                (< distance clearance) (< distance 1) (not (equal center zero))
                (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree)) (natp index) (< index (len coefficients))
                (rationalp error) (< 0 error) (rationalp boundary-cap) (<= 0 boundary-cap)
                (lw-cauchy-boundary-check
                 coefficients (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count coefficients degree error) boundary-cap)
                (<= (lw-pole-remainder-index
                     distance clearance (* first-cap second-cap (lw-zeta-residue-mass entries))
                     (* first-cap second-cap (+ boundary-cap error))) index)
                (lw-complex-diskp
                 (lw-complex-add
                  (lw-complex-add
                   (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                                        (lw-complex-sub center zero) index)
                   (lw-zeta-pole-coefficient-sum center entries index))
                  (nth index coefficients)) cap))
           (<= 1/2 (* first-cap second-cap cap (lw-rational-power distance (+ 1 index)))))
  :hints (("Goal" :use (lw-zeta-residue-mass-valid
                        (:instance lw-cauchy-finite-coefficient-bound (target index) (cap boundary-cap))
                        (:instance lw-complex-sub-disk
                          (left (lw-complex-add
                                 (lw-complex-add
                                  (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                                                       (lw-complex-sub center zero) index)
                                  (lw-zeta-pole-coefficient-sum center entries index))
                                 (nth index coefficients)))
                          (radius cap) (right (nth index coefficients)) (other-radius (+ boundary-cap error)))
                        (:instance lw-zeta-selected-pole-family-lower (cap (+ cap boundary-cap error)))
                        (:instance lw-pole-family-quarter-budget
                          (mass (* first-cap second-cap (lw-zeta-residue-mass entries))))
                        (:instance lw-pole-family-quarter-budget
                          (clearance 1) (mass (* first-cap second-cap (+ boundary-cap error)))))
                  :in-theory (disable lw-zeta-residue-mass-valid lw-cauchy-finite-coefficient-bound
                                      lw-complex-sub-disk lw-complex-sub-add-first
                                      lw-zeta-selected-pole-family-lower lw-pole-family-quarter-budget)
                  :nonlinearp t)))
