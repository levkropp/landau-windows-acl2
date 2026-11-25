(in-package "ACL2")

(include-book "complex-quotients")
(include-book "zeta-pole-sums")

; Exact product and formal-derivative models, retaining multiplicities.
; The logarithmic derivative is derived from the finite product. It is
; not assumed to be the sum of the recorded principal parts.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-complex-reciprocal
                 lw-complex-norm-square lw-complex-quotient
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract lw-complex-mul-distribute
                 lw-zeta-pole-coefficient-sum lw-zeta-residue-mass lw-zeta-pole-residue)))

(local (defthm lw-pfm-scale-mul-left
         (implies (and (rationalp scale) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-mul (lw-complex-scale scale a) b)
                         (lw-complex-scale scale (lw-complex-mul a b))))
         :hints (("Goal"
                  :use ((:instance lw-complex-scale-product (factor scale) (left b) (right a))
                        (:instance lw-complex-mul-commutative
                          (left (lw-complex-scale scale a)) (right b))
                        (:instance lw-complex-mul-commutative (left a) (right b)))
                  :in-theory (disable lw-complex-scale-product)))))
(local (defthm lw-pfm-scale-one
         (implies (rationalp scale)
                  (equal (lw-complex-scale scale (cons 1 0)) (cons scale 0)))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-pfm-zero-times (equal (* 0 a) 0)))
(local (defthm lw-pfm-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-pfm-one-times (implies (rationalp a) (equal (* 1 a) a))))
(local (defthm lw-pfm-scale-one-point
         (implies (lw-complexp point) (equal (lw-complex-scale 1 point) point))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale)))))

(defthm lw-complex-power-nonzero
  (implies (and (lw-complexp point) (not (equal point (cons 0 0))) (natp index))
           (not (equal (lw-complex-power point index) (cons 0 0))))
  :hints (("Goal"
           :use (lw-complex-reciprocal-power-cancel)
           :in-theory (disable lw-complex-reciprocal-power-cancel)
           :cases ((equal (lw-complex-power point index) (cons 0 0))))
          (and stable-under-simplificationp
               '(:in-theory (enable lw-complex-mul)))))

(defthm lw-complex-monomial-log-derivative
  (implies (and (lw-complexp point) (not (equal point (cons 0 0))) (posp index))
           (equal
            (lw-complex-quotient
              (lw-complex-scale index (lw-complex-power point (- index 1)))
              (lw-complex-power point index))
            (lw-complex-scale index (lw-complex-reciprocal point))))
  :hints (("Goal"
           :expand ((lw-complex-power point index))
           :in-theory (enable lw-complex-quotient lw-complex-reciprocal-product
                              lw-complex-mul-commutative lw-complex-mul-left-commutes)
           :do-not-induct t)))

(defun lw-factor-model-value (point entries)
  (if (endp entries) (cons 1 0)
    (lw-complex-mul (lw-complex-power (lw-complex-sub point (caar entries)) (cdar entries))
                    (lw-factor-model-value point (cdr entries)))))

(defun lw-factor-model-derivative (point entries)
  (if (endp entries) (cons 0 0)
    (lw-complex-add
      (lw-complex-mul
        (lw-complex-scale (cdar entries)
          (lw-complex-power (lw-complex-sub point (caar entries)) (- (cdar entries) 1)))
        (lw-factor-model-value point (cdr entries)))
      (lw-complex-mul
        (lw-complex-power (lw-complex-sub point (caar entries)) (cdar entries))
        (lw-factor-model-derivative point (cdr entries))))))

(defun lw-factor-model-log-sum (point entries)
  (if (endp entries) (cons 0 0)
    (lw-complex-add
      (lw-complex-scale (cdar entries)
        (lw-complex-reciprocal (lw-complex-sub point (caar entries))))
      (lw-factor-model-log-sum point (cdr entries)))))

(defun lw-factor-model-away-check (point entries)
  (if (endp entries) t
    (and (not (equal (lw-complex-sub point (caar entries)) (cons 0 0)))
         (lw-factor-model-away-check point (cdr entries)))))

(defthm lw-factor-model-rational
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries))
           (and (lw-complexp (lw-factor-model-value point entries))
                (lw-complexp (lw-factor-model-derivative point entries))
                (lw-complexp (lw-factor-model-log-sum point entries)))))

(defthm lw-factor-model-clearance-away
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance)
                (lw-zeta-pole-clearance-check point entries clearance))
           (lw-factor-model-away-check point entries))
  :hints (("Goal" :induct (lw-factor-model-away-check point entries)
                  :in-theory (disable lw-complex-norm-lower-nonzero))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-norm-lower-nonzero
                          (point (lw-complex-sub point (caar entries))) (lower clearance)))))))

(defthm lw-factor-model-value-nonzero
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (lw-factor-model-away-check point entries))
           (not (equal (lw-factor-model-value point entries) (cons 0 0))))
  :hints (("Goal" :induct (lw-factor-model-value point entries)
                  :in-theory (disable lw-complex-product-nonzero))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-product-nonzero
                          (a (lw-complex-power (lw-complex-sub point (caar entries)) (cdar entries)))
                          (b (lw-factor-model-value point (cdr entries)))))))))

(defthm lw-factor-model-log-derivative
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (lw-factor-model-away-check point entries))
           (equal (lw-complex-quotient (lw-factor-model-derivative point entries)
                                       (lw-factor-model-value point entries))
                  (lw-factor-model-log-sum point entries)))
  :hints (("Goal" :induct (lw-factor-model-derivative point entries)
                  :in-theory (disable lw-complex-quotient-product-rule))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-quotient-product-rule
                          (p (lw-complex-power (lw-complex-sub point (caar entries)) (cdar entries)))
                          (h (lw-factor-model-value point (cdr entries)))
                          (dp (lw-complex-scale (cdar entries)
                                (lw-complex-power (lw-complex-sub point (caar entries))
                                                  (- (cdar entries) 1))))
                          (dh (lw-factor-model-derivative point (cdr entries)))))
                 :do-not-induct t))))

(local (in-theory
        (disable lw-factor-model-value lw-factor-model-derivative lw-factor-model-log-sum
                 lw-factor-model-away-check lw-zeta-pole-familyp)))

(defthm lw-factor-model-log-derivative-error
  (implies
   (and (lw-complexp point) (lw-zeta-pole-familyp entries)
        (lw-factor-model-away-check point entries)
        (lw-complexp value) (lw-complexp derivative)
        (lw-complexp h) (lw-complexp dh) (not (equal h (cons 0 0)))
        (rationalp left-clearance) (< 0 left-clearance)
        (<= (* left-clearance left-clearance) (lw-complex-norm-square value))
        (rationalp right-clearance) (< 0 right-clearance)
        (<= (* right-clearance right-clearance)
            (lw-complex-norm-square (lw-complex-mul (lw-factor-model-value point entries) h)))
        (lw-complex-diskp
          (lw-complex-add (lw-complex-mul (lw-factor-model-derivative point entries) h)
                          (lw-complex-mul (lw-factor-model-value point entries) dh)) numerator-cap)
        (lw-complex-diskp
          (lw-complex-sub derivative
            (lw-complex-add (lw-complex-mul (lw-factor-model-derivative point entries) h)
                            (lw-complex-mul (lw-factor-model-value point entries) dh)))
          derivative-error)
        (lw-complex-diskp
          (lw-complex-sub value (lw-complex-mul (lw-factor-model-value point entries) h)) value-error))
   (lw-complex-diskp
     (lw-complex-sub (lw-complex-quotient derivative value)
       (lw-complex-add (lw-factor-model-log-sum point entries) (lw-complex-quotient dh h)))
     (+ (* (/ left-clearance) derivative-error)
        (* numerator-cap (/ left-clearance) (/ right-clearance) value-error))))
  :hints (("Goal"
           :use ((:instance lw-complex-factor-log-derivative-bound
                   (p (lw-factor-model-value point entries))
                   (dp (lw-factor-model-derivative point entries)))
                 lw-factor-model-log-derivative)
           :in-theory (disable lw-complex-factor-log-derivative-bound
                               lw-factor-model-log-derivative)
           :do-not-induct t)))

(defthm lw-factor-model-computed-log-derivative-error
  (implies
   (and (lw-complexp point) (lw-zeta-pole-familyp entries)
        (lw-factor-model-away-check point entries)
        (lw-complexp value) (lw-complexp derivative)
        (lw-complexp h) (lw-complexp dh) (not (equal h (cons 0 0)))
        (rationalp left-clearance) (< 0 left-clearance)
        (<= (* left-clearance left-clearance) (lw-complex-norm-square value))
        (rationalp right-clearance) (< 0 right-clearance)
        (<= (* right-clearance right-clearance)
            (lw-complex-norm-square (lw-complex-mul (lw-factor-model-value point entries) h)))
        (lw-complex-diskp
          (lw-complex-add (lw-complex-mul (lw-factor-model-derivative point entries) h)
                          (lw-complex-mul (lw-factor-model-value point entries) dh)) numerator-cap)
        (rationalp error) (< 0 error)
        (lw-complex-diskp
          (lw-complex-sub derivative
            (lw-complex-add (lw-complex-mul (lw-factor-model-derivative point entries) h)
                            (lw-complex-mul (lw-factor-model-value point entries) dh)))
          (lw-complex-quotient-precision left-clearance right-clearance numerator-cap error))
        (lw-complex-diskp
          (lw-complex-sub value (lw-complex-mul (lw-factor-model-value point entries) h))
          (lw-complex-quotient-precision left-clearance right-clearance numerator-cap error)))
   (lw-complex-diskp
     (lw-complex-sub (lw-complex-quotient derivative value)
       (lw-complex-add (lw-factor-model-log-sum point entries) (lw-complex-quotient dh h))) error))
  :hints (("Goal"
           :use ((:instance lw-complex-quotient-computed-error
                   (numerator derivative) (denominator value)
                   (approximate-numerator
                     (lw-complex-add (lw-complex-mul (lw-factor-model-derivative point entries) h)
                                     (lw-complex-mul (lw-factor-model-value point entries) dh)))
                   (approximate-denominator (lw-complex-mul (lw-factor-model-value point entries) h)))
                 (:instance lw-complex-quotient-product-rule
                   (p (lw-factor-model-value point entries))
                   (dp (lw-factor-model-derivative point entries)))
                 lw-factor-model-log-derivative)
           :in-theory (disable lw-complex-quotient-computed-error
                               lw-complex-quotient-product-rule lw-factor-model-log-derivative)
           :do-not-induct t)))
