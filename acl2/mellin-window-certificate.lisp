(in-package "ACL2")

(include-book "mellin-real-anchor")
(include-book "mellin-dyadic-normalization")

; Conditional end of the arithmetic reduction. Both Mellin models are
; checked against the actual computed improper polynomials. This does not
; construct those models from analytic zeta data or prove complete covers.
; A regular-part record is (coefficients degree radius cap error).

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-complex-reciprocal
                 lw-complex-norm-square lw-complex-l1 lw-rational-power
                 lw-rational-power-product lw-rational-power-add-exponents
                 lw-zeta-pole-residue lw-zeta-residue-mass lw-zeta-pole-familyp
                 lw-zeta-pole-clearance-check lw-zeta-pole-coefficient-sum lw-pole-coefficient
                 lw-pole-regular-coefficient lw-pole-radius-remainder-index lw-pole-family-index
                 lw-zeta-model-coefficient lw-zeta-model-polynomial
                 lw-mellin-model-boundary-check lw-mellin-integral lw-mellin-improper-polynomial
                 lw-mellin-improper-polynomial-degree lw-mellin-common-cells lw-mellin-common-cutoff
                 lw-mellin-real-anchor-bound
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-coefficient-precision
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-geometric-index lw-geometric-threshold lw-log-signal-bounds
                 lw-kernel-window-threshold (:executable-counterpart lw-kernel-window-threshold)
                 lw-window-index lw-landau-window-search lw-landau-window-address lw-signal-bounds
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(defun lw-mellin-regular-certificatep (index regular)
  (let ((coefficients (nth 0 regular)) (degree (nth 1 regular))
        (radius (nth 2 regular)) (cap (nth 3 regular)) (error (nth 4 regular)))
    (and (true-listp regular) (equal (len regular) 5)
         (natp index) (lw-complex-coefficientsp coefficients) (natp degree)
         (<= (len coefficients) (+ 1 degree)) (< index (len coefficients))
         (rationalp radius) (< 0 radius) (rationalp cap) (<= 0 cap)
         (rationalp error) (< 0 error)
         (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation degree) 0
           (lw-cauchy-coefficient-count coefficients degree error) cap))))

(defun lw-mellin-selected-certificatep
  (height index inner-radius error zero multiplicity entries clearance distance
          first-cap second-cap regular comparison-cap)
  (and (rationalp height) (natp index)
       (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius 250)
       (rationalp error) (< 0 error) (lw-complexp zero) (posp multiplicity)
       (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0)))
       (lw-zeta-pole-familyp entries) (rationalp clearance) (< 0 clearance)
       (lw-zeta-pole-clearance-check (cons 252 height) entries clearance)
       (lw-complex-diskp zero first-cap)
       (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
       (lw-complex-diskp (lw-complex-sub (cons 252 height) zero) distance)
       (not (equal (cons 252 height) zero)) (< distance clearance)
       (lw-mellin-regular-certificatep index regular) (< distance (nth 2 regular))
       (<= (lw-pole-radius-remainder-index distance clearance (nth 2 regular)
              (* first-cap second-cap (lw-zeta-residue-mass entries))
              (* first-cap second-cap (+ (nth 3 regular) (nth 4 regular)))) index)
       (rationalp comparison-cap) (<= 0 comparison-cap)
       (lw-mellin-model-boundary-check 252 height index inner-radius error
         zero multiplicity entries (nth 0 regular) (nth 2 regular) comparison-cap)))

(defun lw-mellin-anchor-certificatep
  (index inner-radius error entries clearance regular comparison-cap)
  (and (natp index) (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius 250)
       (rationalp error) (< 0 error) (lw-zeta-pole-familyp entries)
       (rationalp clearance) (< 0 clearance)
       (lw-zeta-pole-clearance-check (cons 252 0) entries clearance)
       (lw-mellin-regular-certificatep index regular)
       (rationalp comparison-cap) (<= 0 comparison-cap)
       (lw-mellin-model-boundary-check 252 0 index inner-radius error (cons 2 0) 0
         entries (nth 0 regular) (nth 2 regular) comparison-cap)))

(defun lw-mellin-anchor-certificate-bound (index error entries clearance regular comparison-cap)
  (lw-mellin-real-anchor-bound entries clearance (nth 2 regular) index
    (nth 3 regular) (nth 4 regular) comparison-cap error))

(defthm lw-mellin-selected-certificate-lower
  (implies
   (and (lw-mellin-selected-certificatep height index inner-radius error zero multiplicity
          entries clearance distance first-cap second-cap regular comparison-cap)
        (lw-complex-diskp (lw-mellin-integral 252 height index (* 1/64 error)) moment-cap))
   (<= 1/2 (* first-cap second-cap (+ moment-cap comparison-cap error)
              (lw-rational-power distance (+ 1 index)))))
  :hints (("Goal"
           :use ((:instance lw-mellin-pole-model-radius-dominance
                   (sigma 252) (coefficients (nth 0 regular)) (regular-degree (nth 1 regular))
                   (radius (nth 2 regular)) (boundary-cap (nth 3 regular))
                   (regular-error (nth 4 regular))))
           :in-theory (disable lw-mellin-pole-model-radius-dominance))))

(defthm lw-mellin-anchor-certificate-lower
  (implies
   (lw-mellin-anchor-certificatep index inner-radius error entries clearance regular comparison-cap)
   (<= (- (car (lw-mellin-integral 252 0 index (* 1/64 error))))
       (lw-mellin-anchor-certificate-bound index error entries clearance regular comparison-cap)))
  :hints (("Goal"
           :use ((:instance lw-mellin-real-anchor-lower (sigma 252)
                   (coefficients (nth 0 regular)) (regular-degree (nth 1 regular))
                   (radius (nth 2 regular)) (boundary-cap (nth 3 regular))
                   (regular-error (nth 4 regular))))
           :in-theory (disable lw-mellin-real-anchor-lower))))

(local (in-theory (disable lw-mellin-selected-certificatep lw-mellin-anchor-certificatep
                           lw-mellin-regular-certificatep lw-mellin-anchor-certificate-bound)))

(defun lw-mellin-window-moment-cap
  (ceiling numerator denominator index error anchor-entries anchor-clearance
           anchor-regular anchor-comparison-cap)
  (+ (* (+ (* 8 ceiling) 10)
        (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))
     (lw-mellin-anchor-certificate-bound index error anchor-entries anchor-clearance
       anchor-regular anchor-comparison-cap)
     (* 1/64 error)))

(defun lw-mellin-window-data-check
  (start ceiling numerator denominator height inner-radius error zero multiplicity entries
         clearance distance first-cap second-cap regular comparison-cap
         anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
  (let ((index (lw-window-index start)))
    (and (rationalp start) (< 1 start) (<= (lw-kernel-window-threshold) start)
         (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator)
         (<= numerator denominator)
         (lw-mellin-selected-certificatep height index inner-radius error zero multiplicity
           entries clearance distance first-cap second-cap regular comparison-cap)
         (lw-mellin-anchor-certificatep index inner-radius error anchor-entries anchor-clearance
           anchor-regular anchor-comparison-cap))))

(defthm lw-mellin-failed-window-anchor-upper
  (implies
   (and (rationalp start) (< 1 start) (<= (lw-kernel-window-threshold) start)
        (rationalp height) (rationalp ceiling) (<= 0 ceiling)
        (natp numerator) (posp denominator) (<= numerator denominator)
        (lw-mellin-anchor-certificatep (lw-window-index start) inner-radius error
          anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
        (not (lw-landau-window-search start ceiling numerator denominator)))
   (lw-complex-diskp (lw-mellin-integral 252 height (lw-window-index start) (* 1/64 error))
     (lw-mellin-window-moment-cap ceiling numerator denominator (lw-window-index start) error
       anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)))
  :hints (("Goal"
           :use ((:instance lw-eventual-failed-search-improper-coefficient-normalized
                   (error (* 1/64 error)))
                 (:instance lw-mellin-anchor-certificate-lower (index (lw-window-index start))
                   (entries anchor-entries) (clearance anchor-clearance) (regular anchor-regular)
                   (comparison-cap anchor-comparison-cap))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-integral 252 height (lw-window-index start) (* 1/64 error)))
                   (radius (+ (* (+ (* 8 ceiling) 10)
                                 (lw-rational-power (/ (- 252 (/ numerator denominator)))
                                                    (+ 1 (lw-window-index start))))
                              (- (car (lw-mellin-integral 252 0 (lw-window-index start)
                                    (* 1/64 error)))) (* 1/64 error)))
                   (cap (lw-mellin-window-moment-cap ceiling numerator denominator
                          (lw-window-index start) error anchor-entries anchor-clearance
                          anchor-regular anchor-comparison-cap))))
           :in-theory
           (e/d (lw-mellin-anchor-certificatep lw-mellin-regular-certificatep
                 lw-mellin-anchor-certificate-bound lw-mellin-real-anchor-bound)
                (lw-eventual-failed-search-improper-coefficient-normalized
                 lw-mellin-anchor-certificate-lower))
           :do-not-induct t)))

(defthm lw-mellin-failed-window-model-constraint
  (implies
   (and (lw-mellin-window-data-check start ceiling numerator denominator height inner-radius error
          zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
          anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
        (not (lw-landau-window-search start ceiling numerator denominator)))
   (let ((index (lw-window-index start)))
     (<= 1/2
         (* first-cap second-cap
            (+ (lw-mellin-window-moment-cap ceiling numerator denominator index error
                 anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
               comparison-cap error)
            (lw-rational-power distance (+ 1 index))))))
  :hints (("Goal"
           :use (lw-mellin-failed-window-anchor-upper
                 (:instance lw-mellin-selected-certificate-lower (index (lw-window-index start))
                   (moment-cap (lw-mellin-window-moment-cap ceiling numerator denominator
                     (lw-window-index start) error anchor-entries anchor-clearance
                     anchor-regular anchor-comparison-cap))))
           :in-theory (e/d (lw-mellin-selected-certificatep)
                           (lw-mellin-failed-window-anchor-upper
                            lw-mellin-selected-certificate-lower
                            lw-mellin-window-moment-cap))
           :do-not-induct t)))

(defun lw-mellin-window-certificatep
  (start ceiling numerator denominator height inner-radius error zero multiplicity entries
         clearance distance first-cap second-cap regular comparison-cap
         anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
  (and (lw-mellin-window-data-check start ceiling numerator denominator height inner-radius error
         zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
         anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
       (< (* first-cap second-cap
             (+ (lw-mellin-window-moment-cap ceiling numerator denominator (lw-window-index start)
                  error anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
                comparison-cap error)
             (lw-rational-power distance (+ 1 (lw-window-index start)))) 1/2)))

(local (in-theory (disable lw-mellin-window-data-check lw-mellin-window-moment-cap)))

(defthm lw-mellin-model-certificate-window-success
  (implies
   (lw-mellin-window-certificatep start ceiling numerator denominator height inner-radius error
     zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
     anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
   (lw-landau-window-search start ceiling numerator denominator))
  :hints (("Goal" :use (lw-mellin-failed-window-model-constraint)
                  :in-theory (disable lw-mellin-failed-window-model-constraint)
                  :do-not-induct t)))

(defthm lw-mellin-model-certificate-window-witness
  (implies
   (lw-mellin-window-certificatep start ceiling numerator denominator height inner-radius error
     zero multiplicity entries clearance distance first-cap second-cap regular comparison-cap
     anchor-entries anchor-clearance anchor-regular anchor-comparison-cap)
   (let* ((found (lw-landau-window-search start ceiling numerator denominator))
          (address (lw-landau-window-address start ceiling found)))
     (and found (rationalp address) (<= start address)
          (<= (* address address) (* start start start)) (< 0 (cadr found))
          (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal" :use (lw-mellin-model-certificate-window-success
                       lw-landau-window-search-certificate)
                  :in-theory (e/d (lw-mellin-window-data-check)
                                  (lw-mellin-model-certificate-window-success
                                   lw-landau-window-search-certificate))
                  :do-not-induct t)))
