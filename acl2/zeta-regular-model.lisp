(in-package "ACL2")

(include-book "polynomial-normalization")
(include-book "polynomial-affine")
(include-book "polynomial-addition")
(include-book "pole-polynomials")
(include-book "zeta-factor-transform")
(include-book "mellin-window-certificate")

; Build the regular certificate for a finite factor family and a
; polynomial logarithmic derivative. The origin resolvent is truncated
; at a computed order. The Cauchy cap and extraction error are fixed
; independently of the target index and truncation precision.
; Actual zeta model generation and the Mellin identity remain separate.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-complex-reciprocal
                 lw-complex-quotient
                 lw-complex-norm-square lw-complex-l1 lw-rational-power lw-complex-polynomial
                 lw-polynomial-add lw-polynomial-add-constant lw-polynomial-multiply-coefficients
                 lw-polynomial-affine lw-polynomial-multiply-linear lw-complex-coefficient-mass
                 lw-normalized-log-polynomial-numerator lw-normalized-log-polynomial-value
                 lw-normalized-log-polynomial-regular lw-normalized-log-polynomial-origin
                 lw-zeta-factor-family-transform lw-zeta-factor-origin-residue
                 lw-zeta-factor-family-regular-value lw-zeta-pole-coefficient-sum
                 lw-zeta-pole-familyp lw-factor-model-away-check
                 lw-zeta-factor-family-normalized lw-zeta-factor-product-transform
                 lw-normalized-log-polynomial-normalized
                 lw-pole-unit-value lw-pole-polynomial-coefficients lw-pole-polynomial-count
                 lw-pole-resolvent-factor lw-pole-resolvent-ratio
                 lw-pole-coefficient-precision lw-resolvent-truncation-count
                 lw-cauchy-boundary-check lw-cauchy-coefficient-count lw-cauchy-orbit-rotation
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-zrm-real-pair
         (implies (rationalp value) (lw-complexp (cons value 0)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-zrm-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-zrm-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-zrm-zero-times (equal (* 0 a) 0)))
(local (defthm lw-zrm-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-zrm-shift
         (implies (and (lw-complexp center) (lw-complexp point) (rationalp radius))
                  (equal (lw-complex-add center (lw-complex-mul point (cons (- radius) 0)))
                         (lw-complex-sub center (lw-complex-mul point (cons radius 0)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul lw-complex-scale)))))

(local (defthm lw-zrm-sub-common
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
                  (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add a c))
                         (lw-complex-sub b c)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(defun lw-zeta-regular-model-origin (entries coefficients correction)
  (lw-complex-add (lw-zeta-factor-origin-residue entries)
                  (lw-normalized-log-polynomial-origin coefficients correction)))

(defun lw-zeta-regular-model-polynomial-part (coefficients correction center radius)
  (lw-polynomial-affine
    (lw-normalized-log-polynomial-regular coefficients correction) center (cons (- radius) 0)))

(defun lw-zeta-regular-model-count (entries coefficients correction center radius clearance error target)
  (max (+ 1 (nfix target))
       (lw-pole-polynomial-count
         (lw-zeta-regular-model-origin entries coefficients correction) center radius clearance error)))

(defun lw-zeta-regular-model-coefficients
  (entries coefficients correction center radius clearance error target)
  (lw-polynomial-add
    (lw-zeta-regular-model-polynomial-part coefficients correction center radius)
    (lw-pole-polynomial-coefficients (lw-zeta-regular-model-origin entries coefficients correction)
      center radius
      (lw-zeta-regular-model-count entries coefficients correction center radius clearance error target))))

(defun lw-zeta-regular-model-cap (entries coefficients correction center radius clearance)
  (+ (lw-complex-coefficient-mass
       (lw-zeta-regular-model-polynomial-part coefficients correction center radius))
     (* (lw-complex-l1
          (lw-pole-resolvent-factor (lw-zeta-regular-model-origin entries coefficients correction) center))
        (/ (- 1 (/ radius clearance))))
     1))

(defun lw-zeta-regular-model-record
  (entries coefficients correction center radius clearance error target)
  (let ((regular (lw-zeta-regular-model-coefficients
                   entries coefficients correction center radius clearance error target)))
    (list regular (len regular) radius
          (lw-zeta-regular-model-cap entries coefficients correction center radius clearance) 1)))

(defun lw-zeta-polynomial-log-model (point entries coefficients correction)
  (lw-complex-add (lw-zeta-factor-family-transform point entries)
                  (lw-normalized-log-polynomial-value point coefficients correction)))

(defthm lw-zeta-regular-model-data
  (implies (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
                (lw-complexp correction) (lw-complexp center) (rationalp radius) (natp target))
           (and
            (lw-complexp (lw-zeta-regular-model-origin entries coefficients correction))
            (lw-complex-coefficientsp
              (lw-zeta-regular-model-polynomial-part coefficients correction center radius))
            (natp (lw-zeta-regular-model-count
                    entries coefficients correction center radius clearance error target))
            (lw-complex-coefficientsp
              (lw-zeta-regular-model-coefficients
                entries coefficients correction center radius clearance error target))
            (< target (len (lw-zeta-regular-model-coefficients
                             entries coefficients correction center radius clearance error target)))))
  :hints (("Goal"
           :use ((:instance lw-zeta-factor-family-rational (point center)))
           :in-theory (disable lw-zeta-factor-family-rational)
           :do-not-induct t)))

(local (in-theory
        (disable lw-zeta-regular-model-origin lw-zeta-regular-model-polynomial-part
                 lw-zeta-regular-model-count lw-zeta-regular-model-coefficients)))

(defthm lw-zeta-polynomial-log-model-split
  (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                (lw-zeta-pole-familyp entries) (lw-factor-model-away-check point entries)
                (lw-complex-coefficientsp coefficients) (lw-complexp correction))
           (equal
            (lw-zeta-polynomial-log-model point entries coefficients correction)
            (lw-complex-add (lw-zeta-pole-coefficient-sum point entries 0)
              (lw-complex-add
                (lw-complex-polynomial
                  (lw-normalized-log-polynomial-regular coefficients correction) point 0)
                (lw-complex-quotient
                  (lw-zeta-regular-model-origin entries coefficients correction) point)))))
  :hints (("Goal"
           :use (lw-zeta-factor-family-principal-parts lw-normalized-log-polynomial-split)
           :in-theory
           (e/d (lw-zeta-regular-model-origin lw-zeta-factor-family-regular-value lw-complex-quotient)
                (lw-zeta-factor-family-principal-parts lw-normalized-log-polynomial-split))
           :do-not-induct t)))

(defthm lw-zeta-regular-model-error
  (implies
   (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
        (lw-complexp correction) (lw-complexp center)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square center))
        (rationalp radius) (<= 0 radius) (< radius clearance)
        (rationalp error) (< 0 error) (natp target) (lw-complex-diskp point 1))
   (let ((shifted (lw-complex-sub center (lw-complex-mul (cons radius 0) point))))
     (lw-complex-diskp
      (lw-complex-sub
        (lw-complex-add
          (lw-complex-polynomial
            (lw-normalized-log-polynomial-regular coefficients correction) shifted 0)
          (lw-pole-unit-value (lw-zeta-regular-model-origin entries coefficients correction)
                              center radius point))
        (lw-complex-polynomial
          (lw-zeta-regular-model-coefficients
            entries coefficients correction center radius clearance error target) point 0))
      error)))
  :hints (("Goal"
           :use ((:instance lw-pole-resolvent-clearance-bound (offset center) (lower clearance))
                 (:instance lw-pole-polynomial-error
                   (residue (lw-zeta-regular-model-origin entries coefficients correction))
                   (offset center) (ratio-cap (/ radius clearance))
                   (count (lw-zeta-regular-model-count
                            entries coefficients correction center radius clearance error target)))
                 (:instance lw-zrm-sub-common
                   (a (lw-complex-polynomial
                        (lw-normalized-log-polynomial-regular coefficients correction)
                        (lw-complex-sub center (lw-complex-mul (cons radius 0) point)) 0))
                   (b (lw-pole-unit-value (lw-zeta-regular-model-origin entries coefficients correction)
                                          center radius point))
                   (c (lw-complex-polynomial
                        (lw-pole-polynomial-coefficients
                          (lw-zeta-regular-model-origin entries coefficients correction) center radius
                          (lw-zeta-regular-model-count
                            entries coefficients correction center radius clearance error target)) point 0))))
           :in-theory
           (e/d (lw-zeta-regular-model-coefficients lw-zeta-regular-model-polynomial-part
                 lw-zeta-regular-model-count lw-pole-polynomial-count)
                (lw-pole-resolvent-clearance-bound lw-pole-polynomial-error
                 lw-complex-sub-add-first lw-zrm-sub-common lw-complex-real-product
                 lw-polynomial-divided-difference-identity))
           :do-not-induct t)))

(local (defthm lw-zrm-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-zeta-regular-model-cap-data
  (implies
   (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
        (lw-complexp correction) (lw-complexp center)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square center))
        (rationalp radius) (<= 0 radius) (< radius clearance))
   (and (rationalp (lw-zeta-regular-model-cap
                     entries coefficients correction center radius clearance))
        (<= 0 (lw-zeta-regular-model-cap
                entries coefficients correction center radius clearance))))
  :hints (("Goal"
           :use ((:instance lw-zeta-regular-model-data (target 0))
                 (:instance lw-complex-coefficient-mass-valid
                   (coefficients
                     (lw-zeta-regular-model-polynomial-part coefficients correction center radius)))
                 (:instance lw-pole-resolvent-clearance-bound (offset center) (lower clearance))
                 (:instance lw-zrm-product-nonnegative
                   (a (lw-complex-l1
                        (lw-pole-resolvent-factor
                          (lw-zeta-regular-model-origin entries coefficients correction) center)))
                   (b (/ (- 1 (/ radius clearance)))))
                 (:instance lw-complex-l1-bound
                   (point (lw-pole-resolvent-factor
                            (lw-zeta-regular-model-origin entries coefficients correction) center))))
           :in-theory (disable lw-zeta-regular-model-data lw-pole-resolvent-clearance-bound
                               lw-complex-l1-bound lw-complex-coefficient-mass-valid)
           :nonlinearp t :do-not-induct t)))

(defthm lw-zeta-regular-model-bound
  (implies
   (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
        (lw-complexp correction) (lw-complexp center)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square center))
        (rationalp radius) (<= 0 radius) (< radius clearance)
        (rationalp error) (< 0 error) (<= error 1) (natp target) (lw-complex-diskp point 1))
   (lw-complex-diskp
    (lw-complex-polynomial
      (lw-zeta-regular-model-coefficients
        entries coefficients correction center radius clearance error target) point 0)
    (lw-zeta-regular-model-cap entries coefficients correction center radius clearance)))
  :hints (("Goal"
           :use (lw-zeta-regular-model-data
                 (:instance lw-pole-resolvent-clearance-bound (offset center) (lower clearance))
                 (:instance lw-pole-polynomial-bound
                   (residue (lw-zeta-regular-model-origin entries coefficients correction))
                   (offset center) (ratio-cap (/ radius clearance))
                   (count (lw-zeta-regular-model-count
                            entries coefficients correction center radius clearance error target)))
                 (:instance lw-complex-polynomial-unit-mass-bound
                   (coefficients
                     (lw-zeta-regular-model-polynomial-part coefficients correction center radius))
                   (offset 0))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-polynomial
                     (lw-zeta-regular-model-polynomial-part coefficients correction center radius) point 0))
                   (radius (lw-complex-coefficient-mass
                     (lw-zeta-regular-model-polynomial-part coefficients correction center radius)))
                   (right (lw-complex-polynomial
                     (lw-pole-polynomial-coefficients
                       (lw-zeta-regular-model-origin entries coefficients correction) center radius
                       (lw-zeta-regular-model-count
                         entries coefficients correction center radius clearance error target)) point 0))
                   (other-radius (+ (* (lw-complex-l1
                     (lw-pole-resolvent-factor
                       (lw-zeta-regular-model-origin entries coefficients correction) center))
                     (/ (- 1 (/ radius clearance)))) error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-polynomial
                     (lw-zeta-regular-model-coefficients
                       entries coefficients correction center radius clearance error target) point 0))
                   (radius (+ (lw-complex-coefficient-mass
                       (lw-zeta-regular-model-polynomial-part coefficients correction center radius))
                     (* (lw-complex-l1 (lw-pole-resolvent-factor
                          (lw-zeta-regular-model-origin entries coefficients correction) center))
                        (/ (- 1 (/ radius clearance)))) error))
                   (cap (lw-zeta-regular-model-cap
                          entries coefficients correction center radius clearance))))
           :in-theory
           (e/d (lw-zeta-regular-model-coefficients lw-zeta-regular-model-count lw-pole-polynomial-count)
                (lw-zeta-regular-model-data lw-pole-resolvent-clearance-bound lw-pole-polynomial-bound
                 lw-complex-polynomial-unit-mass-bound lw-complex-add-disk))
           :do-not-induct t)))

(local (defun lw-zrm-countdown (sample-count)
         (declare (xargs :measure (nfix sample-count)))
         (if (zp sample-count) 0 (lw-zrm-countdown (- sample-count 1)))))

(defthm lw-zeta-regular-model-boundary-check
  (implies
   (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
        (lw-complexp correction) (lw-complexp center)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square center))
        (rationalp radius) (<= 0 radius) (< radius clearance)
        (rationalp error) (< 0 error) (<= error 1)
        (natp target) (lw-complex-diskp point 1) (natp sample-count))
   (lw-cauchy-boundary-check
    (lw-zeta-regular-model-coefficients
      entries coefficients correction center radius clearance error target)
    point 0 sample-count
    (lw-zeta-regular-model-cap entries coefficients correction center radius clearance)))
  :hints (("Goal" :induct (lw-zrm-countdown sample-count)
                  :in-theory (enable lw-cauchy-boundary-check))
          (and stable-under-simplificationp
               '(:use ((:instance lw-zeta-regular-model-bound
                          (point (lw-complex-power point (- sample-count 1)))))
                 :in-theory (disable lw-zeta-regular-model-bound)
                 :do-not-induct t))))

(defthm lw-zeta-regular-model-certificate
  (implies
   (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
        (lw-complexp correction) (lw-complexp center)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square center))
        (rationalp radius) (< 0 radius) (< radius clearance)
        (rationalp error) (< 0 error) (<= error 1) (natp target))
   (lw-mellin-regular-certificatep target
     (lw-zeta-regular-model-record
       entries coefficients correction center radius clearance error target)))
  :hints (("Goal"
           :use (lw-zeta-regular-model-data lw-zeta-regular-model-cap-data
                 (:instance lw-zeta-regular-model-boundary-check
                   (point (lw-cauchy-orbit-rotation
                     (len (lw-zeta-regular-model-coefficients
                            entries coefficients correction center radius clearance error target))))
                   (sample-count (lw-cauchy-coefficient-count
                     (lw-zeta-regular-model-coefficients
                       entries coefficients correction center radius clearance error target)
                     (len (lw-zeta-regular-model-coefficients
                            entries coefficients correction center radius clearance error target)) 1))))
           :in-theory
           (e/d (lw-mellin-regular-certificatep lw-zeta-regular-model-record)
                (lw-zeta-regular-model-data lw-zeta-regular-model-cap-data
                 lw-zeta-regular-model-boundary-check))
           :do-not-induct t)))

(local (in-theory (disable lw-zeta-polynomial-log-model)))

(defthm lw-zeta-polynomial-log-model-error
  (implies
   (and (lw-zeta-pole-familyp entries) (lw-complex-coefficientsp coefficients)
        (lw-complexp correction) (lw-complexp center)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square center))
        (rationalp radius) (<= 0 radius) (< radius clearance)
        (rationalp error) (< 0 error) (natp target) (lw-complex-diskp point 1)
        (not (equal (lw-complex-sub center (lw-complex-mul (cons radius 0) point)) (cons 0 0)))
        (lw-factor-model-away-check
          (lw-complex-sub center (lw-complex-mul (cons radius 0) point)) entries))
   (let ((shifted (lw-complex-sub center (lw-complex-mul (cons radius 0) point))))
     (lw-complex-diskp
      (lw-complex-sub
        (lw-zeta-polynomial-log-model shifted entries coefficients correction)
        (lw-complex-add (lw-zeta-pole-coefficient-sum shifted entries 0)
          (lw-complex-polynomial
            (lw-zeta-regular-model-coefficients
              entries coefficients correction center radius clearance error target) point 0)))
      error)))
  :hints (("Goal"
           :use (lw-zeta-regular-model-error
                 (:instance lw-zeta-polynomial-log-model-split
                   (point (lw-complex-sub center (lw-complex-mul (cons radius 0) point))))
                 (:instance lw-zrm-sub-common
                   (a (lw-zeta-pole-coefficient-sum
                        (lw-complex-sub center (lw-complex-mul (cons radius 0) point)) entries 0))
                   (b (lw-complex-add
                        (lw-complex-polynomial
                          (lw-normalized-log-polynomial-regular coefficients correction)
                          (lw-complex-sub center (lw-complex-mul (cons radius 0) point)) 0)
                        (lw-pole-unit-value
                          (lw-zeta-regular-model-origin entries coefficients correction)
                          center radius point)))
                   (c (lw-complex-polynomial
                        (lw-zeta-regular-model-coefficients
                          entries coefficients correction center radius clearance error target) point 0))))
           :in-theory
           (e/d (lw-complex-quotient lw-pole-unit-value)
                (lw-zeta-regular-model-error lw-zeta-polynomial-log-model-split
                 lw-zrm-sub-common lw-complex-sub-add-first lw-pole-unit-value-as-resolvent
                 lw-polynomial-divided-difference-identity))
           :do-not-induct t)))

(local (defthm lw-zrm-negative-quotient-add
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp denominator))
                  (equal
                   (lw-complex-add (lw-complex-scale -1 (lw-complex-quotient a denominator))
                                   (lw-complex-scale -1 (lw-complex-quotient b denominator)))
                   (lw-complex-scale -1
                     (lw-complex-quotient (lw-complex-add a b) denominator))))
         :hints (("Goal" :in-theory (enable lw-complex-quotient)))))

(local (defthm lw-zrm-numerator-add
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (lw-complexp d) (lw-complexp point) (lw-complexp rest))
                  (equal
                   (lw-complex-add rest
                     (lw-complex-add (lw-complex-sub a (lw-complex-mul point b))
                                     (lw-complex-sub c (lw-complex-mul point d))))
                   (lw-complex-add
                     (lw-complex-sub (lw-complex-add a c)
                       (lw-complex-mul point (lw-complex-add b d))) rest)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul)))))

(defthm lw-zeta-polynomial-log-model-normalized
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (lw-factor-model-away-check point entries)
                (lw-complex-coefficientsp coefficients) (lw-complexp correction)
                (not (equal point (cons 0 0))) (not (equal point (cons 1 0))))
           (equal
            (lw-zeta-polynomial-log-model point entries coefficients correction)
            (lw-complex-scale -1
              (lw-complex-quotient
                (lw-complex-add
                  (lw-complex-sub
                    (lw-complex-add (lw-factor-model-log-sum point entries)
                                    (lw-complex-polynomial coefficients point 0))
                    (lw-complex-mul point
                      (lw-complex-add (lw-factor-model-log-sum (cons 1 0) entries)
                                      (lw-complex-polynomial coefficients (cons 1 0) 0))))
                  (lw-complex-mul correction (lw-complex-sub (cons 1 0) point)))
                (lw-zeta-residue-denominator point)))))
  :hints (("Goal"
           :use (lw-zeta-factor-family-normalized lw-normalized-log-polynomial-normalized
                 (:instance lw-zrm-numerator-add
                   (a (lw-factor-model-log-sum point entries))
                   (b (lw-factor-model-log-sum (cons 1 0) entries))
                   (c (lw-complex-polynomial coefficients point 0))
                   (d (lw-complex-polynomial coefficients (cons 1 0) 0))
                   (rest (lw-complex-mul correction (lw-complex-sub (cons 1 0) point)))))
           :in-theory
           (e/d (lw-zeta-polynomial-log-model lw-zeta-residue-denominator
                 lw-zeta-factor-family-normalized lw-normalized-log-polynomial-normalized)
                (lw-zeta-polynomial-log-model-split lw-complex-mul-subtract
                 lw-zeta-factor-family-principal-parts lw-normalized-log-polynomial-split
                 lw-complex-mul-distribute lw-complex-mul-add-left lw-complex-sub-add-first
                 lw-complex-scale-add))
           :do-not-induct t)))

; Rational test locations exercise the finite model, not zeta-zero existence.
(assert-event
 (let ((entries (list (cons (cons 1/2 0) 2)))
       (coefficients (list (cons 1 0) (cons 2 0) (cons 3 0))))
   (and
    (equal (lw-zeta-polynomial-log-model (cons 1 0) entries coefficients (cons 4 0)) (cons 14 0))
    (equal (lw-zeta-polynomial-log-model (cons 2 0) entries coefficients (cons 4 0)) (cons 17/6 0))
    (equal (lw-zeta-regular-model-cap
             entries coefficients (cons 4 0) (cons 2 0) 1/4 3/2) 23/5))))
