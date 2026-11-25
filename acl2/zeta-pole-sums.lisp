(in-package "ACL2")

(include-book "zeta-pole-lower")

; A finite family of other poles, with explicit multiplicities and an
; independently checked distance from the evaluation center.

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



(local (defthm lw-zps-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-zps-zero-times (equal (* 0 a) 0)))
(local (defthm lw-zps-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (in-theory (disable lw-zeta-pole-residue lw-zeta-residue-denominator
                           lw-pole-coefficient lw-rational-power-product
                           lw-rational-power-add-exponents)))

(defthm lw-pole-coefficient-clearance-upper
  (implies (and (lw-complexp residue) (lw-complexp offset)
                (rationalp clearance) (< 0 clearance)
                (<= (* clearance clearance) (lw-complex-norm-square offset)) (natp index))
           (lw-complex-diskp
            (lw-pole-coefficient residue offset index)
            (* (lw-complex-l1 residue) (lw-rational-power (/ clearance) (+ 1 index)))))
  :hints (("Goal" :use ((:instance lw-complex-reciprocal-disk-bound (point offset) (lower clearance))
                        (:instance lw-complex-l1-bound (point residue))
                        (:instance lw-complex-power-disk
                          (point (lw-complex-reciprocal offset)) (radius (/ clearance)) (index (+ 1 index)))
                        (:instance lw-complex-mul-disk
                          (left residue) (radius (lw-complex-l1 residue))
                          (right (lw-complex-power (lw-complex-reciprocal offset) (+ 1 index)))
                          (other-radius (lw-rational-power (/ clearance) (+ 1 index)))))
                  :in-theory (e/d (lw-pole-coefficient)
                                  (lw-complex-reciprocal-disk-bound lw-complex-l1-bound
                                   lw-complex-power-disk lw-complex-mul-disk)))))

(defun lw-zeta-pole-datap (entry)
  (and (consp entry) (lw-complexp (car entry)) (posp (cdr entry))
       (not (equal (car entry) (cons 0 0))) (not (equal (car entry) (cons 1 0)))))

(defun lw-zeta-pole-familyp (entries)
  (if (consp entries)
      (and (lw-zeta-pole-datap (car entries)) (lw-zeta-pole-familyp (cdr entries)))
    (equal entries nil)))

(defun lw-zeta-residue-mass (entries)
  (if (endp entries) 0
    (+ (lw-complex-l1 (lw-zeta-pole-residue (caar entries) (cdar entries)))
       (lw-zeta-residue-mass (cdr entries)))))

(defthm lw-zeta-residue-mass-valid
  (implies (lw-zeta-pole-familyp entries)
           (and (rationalp (lw-zeta-residue-mass entries)) (<= 0 (lw-zeta-residue-mass entries))))
  :hints (("Goal" :induct (lw-zeta-residue-mass entries))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-l1-bound
                          (point (lw-zeta-pole-residue (caar entries) (cdar entries)))))
                 :in-theory (disable lw-complex-l1-bound)))))

(defun lw-zeta-pole-clearance-check (center entries clearance)
  (if (endp entries) t
    (and (<= (* clearance clearance)
             (lw-complex-norm-square (lw-complex-sub center (caar entries))))
         (lw-zeta-pole-clearance-check center (cdr entries) clearance))))

(defun lw-zeta-pole-coefficient-sum (center entries index)
  (if (endp entries) (cons 0 0)
    (lw-complex-add
     (lw-pole-coefficient (lw-zeta-pole-residue (caar entries) (cdar entries))
                          (lw-complex-sub center (caar entries)) index)
     (lw-zeta-pole-coefficient-sum center (cdr entries) index))))

(defthm lw-zeta-pole-coefficient-sum-rational
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries) (natp index))
           (lw-complexp (lw-zeta-pole-coefficient-sum center entries index))))

(defthm lw-zeta-pole-coefficient-sum-upper
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance)
                (lw-zeta-pole-clearance-check center entries clearance) (natp index))
           (lw-complex-diskp
            (lw-zeta-pole-coefficient-sum center entries index)
            (* (lw-zeta-residue-mass entries) (lw-rational-power (/ clearance) (+ 1 index)))))
  :hints (("Goal" :induct (lw-zeta-pole-coefficient-sum center entries index))
          (and stable-under-simplificationp
               '(:use ((:instance lw-pole-coefficient-clearance-upper
                          (residue (lw-zeta-pole-residue (caar entries) (cdar entries)))
                          (offset (lw-complex-sub center (caar entries))))
                        (:instance lw-complex-add-disk
                          (left (lw-pole-coefficient
                                 (lw-zeta-pole-residue (caar entries) (cdar entries))
                                 (lw-complex-sub center (caar entries)) index))
                          (radius (* (lw-complex-l1 (lw-zeta-pole-residue (caar entries) (cdar entries)))
                                     (lw-rational-power (/ clearance) (+ 1 index))))
                          (right (lw-zeta-pole-coefficient-sum center (cdr entries) index))
                          (other-radius (* (lw-zeta-residue-mass (cdr entries))
                                           (lw-rational-power (/ clearance) (+ 1 index))))))
                 :in-theory (disable lw-pole-coefficient-clearance-upper lw-complex-add-disk
                                     lw-zeta-pole-coefficient-sum lw-complex-l1)))))

(local (in-theory (disable lw-zeta-pole-familyp lw-zeta-pole-datap lw-zeta-pole-clearance-check
                           lw-zeta-pole-coefficient-sum lw-zeta-residue-mass)))

(defthm lw-complex-sub-nonzero
  (implies (and (lw-complexp a) (lw-complexp b) (not (equal a b)))
           (not (equal (lw-complex-sub a b) (cons 0 0))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub))))

(defthm lw-zeta-selected-pole-family-lower
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance)
                (lw-zeta-pole-clearance-check center entries clearance)
                (lw-complex-diskp zero first-cap)
                (lw-complex-diskp (lw-complex-sub zero (cons 1 0)) second-cap)
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))) (posp multiplicity)
                (lw-complex-diskp (lw-complex-sub center zero) distance)
                (not (equal center zero)) (natp index)
                (lw-complex-diskp
                 (lw-complex-add
                  (lw-pole-coefficient (lw-zeta-pole-residue zero multiplicity)
                                       (lw-complex-sub center zero) index)
                  (lw-zeta-pole-coefficient-sum center entries index)) cap))
           (<= multiplicity
               (* first-cap second-cap (lw-rational-power distance (+ 1 index))
                  (+ cap (* (lw-zeta-residue-mass entries)
                            (lw-rational-power (/ clearance) (+ 1 index)))))))
  :hints (("Goal" :use (lw-zeta-pole-coefficient-sum-upper
                        (:instance lw-pole-plus-remainder-disk
                          (residue (lw-zeta-pole-residue zero multiplicity))
                          (offset (lw-complex-sub center zero))
                          (remainder (lw-zeta-pole-coefficient-sum center entries index))
                          (remainder-cap (* (lw-zeta-residue-mass entries)
                                            (lw-rational-power (/ clearance) (+ 1 index)))))
                        (:instance lw-zeta-residue-disk-lower
                          (cap (* (lw-rational-power distance (+ 1 index))
                                  (+ cap (* (lw-zeta-residue-mass entries)
                                            (lw-rational-power (/ clearance) (+ 1 index))))))))
                  :in-theory (disable lw-zeta-pole-coefficient-sum-upper lw-pole-plus-remainder-disk
                                      lw-zeta-residue-disk-lower))))

; Two different locations and multiplicities exercise the family format.
(assert-event
 (let ((entries (list (cons (cons 1/2 1) 1) (cons (cons 3/4 2) 2)))
       (center (cons 4 0)))
   (and (lw-zeta-pole-familyp entries)
        (lw-zeta-pole-clearance-check center entries 3)
        (not (lw-zeta-pole-clearance-check center entries 4))
        (equal (lw-zeta-residue-mass entries) 6452/4745)
        (lw-complex-diskp (lw-zeta-pole-coefficient-sum center entries 2)
                          (* 1/27 (lw-zeta-residue-mass entries))))))
