(in-package "ACL2")

(include-book "mellin-window-certificate")

; Computed geometric and precision budgets for the conditional window
; certificate. Existence of the analytic model certificates remains open.

(local (in-theory
        (disable lw-rational-power lw-rational-power-product lw-rational-power-add-exponents
                 lw-pole-family-index lw-pole-tail-precision lw-resolvent-truncation-count
                 lw-geometric-index lw-geometric-threshold lw-window-index
                 lw-kernel-window-threshold (:executable-counterpart lw-kernel-window-threshold)
                 lw-complexp lw-complex-diskp lw-complex-sub lw-zeta-residue-mass
                 lw-zeta-pole-familyp lw-zeta-pole-clearance-check lw-zeta-pole-residue
                 lw-mellin-model-boundary-check lw-mellin-integral lw-mellin-improper-polynomial
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-orbit-rotation
                 lw-pole-radius-remainder-index lw-landau-window-search lw-landau-window-address
                 lw-signal-bounds)))

(local (defthm lw-mwb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mwb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mwb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(defthm lw-pole-family-sixteenth-budget
  (implies (and (rationalp distance) (<= 0 distance)
                (rationalp clearance) (< 0 clearance) (< distance clearance)
                (rationalp mass) (<= 0 mass) (natp index)
                (<= (lw-pole-family-index distance clearance (* 8 mass)) index))
           (<= (* mass (lw-rational-power distance (+ 1 index))
                  (lw-rational-power (/ clearance) (+ 1 index))) 1/16))
  :hints (("Goal" :use ((:instance lw-pole-family-quarter-budget (mass (* 4 mass))))
                  :in-theory (disable lw-pole-family-quarter-budget))))

(defthm lw-pole-scaled-regular-sixteenth-budget
  (implies (and (rationalp distance) (<= 0 distance)
                (rationalp radius) (< 0 radius) (< distance radius)
                (rationalp mass) (<= 0 mass) (natp index)
                (<= (lw-pole-family-index distance radius (* 8 radius mass)) index))
           (<= (* mass (lw-rational-power (/ radius) index)
                  (lw-rational-power distance (+ 1 index))) 1/16))
  :hints (("Goal" :use ((:instance lw-pole-scaled-regular-quarter-budget (mass (* 4 mass))))
                  :in-theory (disable lw-pole-scaled-regular-quarter-budget))))

(defun lw-mellin-window-decay-index
  (distance window-radius window-mass anchor-clearance anchor-mass regular-radius regular-mass)
  (max (lw-pole-family-index distance window-radius (* 8 window-mass))
       (max (lw-pole-family-index distance anchor-clearance (* 8 anchor-mass))
            (lw-pole-family-index distance regular-radius (* 8 regular-radius regular-mass)))))

(defthm lw-mellin-window-decay-index-natural
  (natp (lw-mellin-window-decay-index distance window-radius window-mass
          anchor-clearance anchor-mass regular-radius regular-mass))
  :rule-classes (:rewrite :type-prescription))

(defun lw-mellin-model-error-precision (scale)
  (/ 1 (* 128 (+ 1 scale))))

(defthm lw-mellin-model-error-precision-adequate
  (implies (and (rationalp scale) (<= 0 scale)
                (rationalp error) (< 0 error)
                (<= error (lw-mellin-model-error-precision scale))
                (rationalp left-cap) (<= 0 left-cap) (<= left-cap error)
                (rationalp right-cap) (<= 0 right-cap) (<= right-cap error))
           (and (rationalp (lw-mellin-model-error-precision scale))
                (< 0 (lw-mellin-model-error-precision scale))
                (<= (* scale (+ left-cap right-cap (* 129/64 error))) 1/16)))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator scale) (divisor (* 128 (+ 1 scale))) (bound 1/128)))
                  :nonlinearp t)))

(defthm lw-mellin-window-decay-budget
  (implies
   (and (rationalp distance) (<= 0 distance) (natp index)
        (rationalp window-radius) (< distance window-radius) (< 0 window-radius)
        (rationalp anchor-clearance) (< distance anchor-clearance) (< 0 anchor-clearance)
        (rationalp regular-radius) (< distance regular-radius) (< 0 regular-radius)
        (rationalp scale) (<= 0 scale)
        (rationalp window-mass) (<= 0 window-mass)
        (rationalp anchor-mass) (<= 0 anchor-mass)
        (rationalp regular-mass) (<= 0 regular-mass)
        (<= (lw-mellin-window-decay-index distance window-radius (* scale window-mass)
              anchor-clearance (* scale anchor-mass) regular-radius (* scale regular-mass)) index)
        (rationalp error) (< 0 error)
        (<= error (lw-mellin-model-error-precision
                    (* scale (lw-rational-power distance (+ 1 index)))))
        (rationalp left-cap) (<= 0 left-cap) (<= left-cap error)
        (rationalp right-cap) (<= 0 right-cap) (<= right-cap error))
   (< (* scale (lw-rational-power distance (+ 1 index))
         (+ (* window-mass (lw-rational-power (/ window-radius) (+ 1 index)))
            (* anchor-mass (lw-rational-power (/ anchor-clearance) (+ 1 index)))
            (* regular-mass (lw-rational-power (/ regular-radius) index))
            left-cap right-cap (* 129/64 error))) 1/2))
  :hints (("Goal"
           :use ((:instance lw-pole-family-sixteenth-budget
                   (clearance window-radius) (mass (* scale window-mass)))
                 (:instance lw-pole-family-sixteenth-budget
                   (clearance anchor-clearance) (mass (* scale anchor-mass)))
                 (:instance lw-pole-scaled-regular-sixteenth-budget
                   (radius regular-radius) (mass (* scale regular-mass)))
                 (:instance lw-mellin-model-error-precision-adequate
                   (scale (* scale (lw-rational-power distance (+ 1 index))))))
           :in-theory (disable lw-pole-family-sixteenth-budget
                               lw-pole-scaled-regular-sixteenth-budget
                               lw-mellin-model-error-precision-adequate
                               lw-mellin-model-error-precision)
           :nonlinearp t :do-not-induct t)))

(defun lw-mellin-window-effective-data-check
  (start ceiling numerator denominator height inner-radius error zero multiplicity entries
         clearance distance first-cap second-cap regular comparison-cap
         anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
  (let ((index (lw-window-index start)) (scale (* first-cap second-cap)))
    (and (lw-mellin-window-data-check start ceiling numerator denominator height inner-radius error
           zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
           anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
         (< distance (- 252 (/ numerator denominator)))
         (< distance anchor-clearance) (< distance (nth 2 anchor-regular))
         (<= (lw-mellin-window-decay-index distance (- 252 (/ numerator denominator))
               (* scale (+ (* 8 ceiling) 10)) anchor-clearance
               (* scale (lw-zeta-residue-mass anchor-entries)) (nth 2 anchor-regular)
               (* scale (+ (nth 3 anchor-regular) (nth 4 anchor-regular)))) index)
         (<= comparison-cap error) (<= anchor-comparison-cap error)
         (<= error (lw-mellin-model-error-precision
                     (* scale (lw-rational-power distance (+ 1 index))))))))

(defthm lw-mellin-computed-budget-certificate
  (implies
   (lw-mellin-window-effective-data-check start ceiling numerator denominator height inner-radius
     error zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
     anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
   (lw-mellin-window-certificatep start ceiling numerator denominator height inner-radius error
     zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
     anchor-entries anchor-clearance anchor-regular anchor-comparison-cap))
  :hints (("Goal"
           :use ((:instance lw-mellin-window-decay-budget (index (lw-window-index start))
                   (window-radius (- 252 (/ numerator denominator)))
                   (window-mass (+ (* 8 ceiling) 10))
                   (anchor-mass (lw-zeta-residue-mass anchor-entries))
                   (regular-radius (nth 2 anchor-regular))
                   (regular-mass (+ (nth 3 anchor-regular) (nth 4 anchor-regular)))
                   (scale (* first-cap second-cap))
                   (left-cap comparison-cap) (right-cap anchor-comparison-cap)))
           :in-theory (disable lw-mellin-window-decay-budget
                               lw-mellin-window-decay-index lw-mellin-model-error-precision)
           :nonlinearp t :do-not-induct t)))

(local (in-theory
        (disable lw-mellin-window-effective-data-check lw-mellin-window-certificatep
                 lw-mellin-window-data-check lw-mellin-window-moment-cap
                 lw-mellin-selected-certificatep lw-mellin-anchor-certificatep
                 lw-mellin-regular-certificatep lw-mellin-anchor-certificate-bound
                 lw-mellin-real-anchor-bound)))

(defthm lw-mellin-computed-budget-window-success
  (implies
   (lw-mellin-window-effective-data-check start ceiling numerator denominator height inner-radius
     error zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
     anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
   (lw-landau-window-search start ceiling numerator denominator))
  :hints (("Goal" :use (lw-mellin-computed-budget-certificate
                       lw-mellin-model-certificate-window-success)
                  :in-theory (disable lw-mellin-computed-budget-certificate
                                      lw-mellin-model-certificate-window-success)
                  :do-not-induct t)))

(defthm lw-mellin-computed-budget-window-witness
  (implies
   (lw-mellin-window-effective-data-check start ceiling numerator denominator height inner-radius
     error zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
     anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
   (let* ((found (lw-landau-window-search start ceiling numerator denominator))
          (address (lw-landau-window-address start ceiling found)))
     (and found (rationalp address) (<= start address)
          (<= (* address address) (* start start start)) (< 0 (cadr found))
          (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal" :use (lw-mellin-computed-budget-certificate
                       lw-mellin-model-certificate-window-witness)
                  :in-theory (disable lw-mellin-computed-budget-certificate
                                      lw-mellin-model-certificate-window-witness)
                  :do-not-induct t)))
