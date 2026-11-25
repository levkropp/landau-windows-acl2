(in-package "ACL2")

(include-book "polynomial-factor-model")

; Normalize each factor's logarithmic derivative at s=1 before forming
; the transform. The apparent pole at 1 then cancels. The remaining
; regular correction is -multiplicity/(rho*s), with no pole at rho or 1.
; These are finite rational identities, not analytic zeta input.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-power lw-rational-power lw-complex-quotient
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-zeta-residue-denominator lw-zeta-pole-residue lw-pole-coefficient
                 lw-zeta-pole-coefficient-sum lw-factor-model-log-sum)))

(local (defthm lw-zft-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-zft-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-zft-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-zft-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-zft-zero-times (equal (* 0 a) 0)))
(local (defthm lw-zft-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-zft-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-zft-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-zft-times-one (implies (rationalp a) (equal (* 1 a) a))))
(local (defthm lw-zft-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-zft-sub-self
         (implies (lw-complexp point)
                  (equal (lw-complex-sub point point) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))
(local (defthm lw-zft-scale-real
         (implies (and (rationalp factor) (rationalp real))
                  (equal (lw-complex-scale factor (cons real 0)) (cons (* factor real) 0)))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-zft-sub-not-zero
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a b)))
                  (not (equal (lw-complex-sub a b) (cons 0 0))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(local (defthm lw-zft-one-minus-sign
         (implies (lw-complexp point)
                  (equal (lw-complex-sub (cons 1 0) point)
                         (lw-complex-scale -1 (lw-complex-sub point (cons 1 0)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))))

(local (defthm lw-zft-scale-mul-left
         (implies (and (rationalp scale) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-mul (lw-complex-scale scale a) b)
                         (lw-complex-scale scale (lw-complex-mul a b))))
         :hints (("Goal"
                  :use ((:instance lw-complex-scale-product (factor scale) (left b) (right a))
                        (:instance lw-complex-mul-commutative
                          (left (lw-complex-scale scale a)) (right b))
                        (:instance lw-complex-mul-commutative (left a) (right b)))
                  :in-theory (disable lw-complex-scale-product)))))

(local (defthm lw-zft-quotient-denominator
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal b (cons 0 0))))
                  (equal (lw-complex-mul b (lw-complex-quotient a b)) a))
         :hints (("Goal" :in-theory (enable lw-complex-quotient lw-complex-mul-commutative
                                          lw-complex-mul-left-commutes)))))

(local (defthm lw-zft-cancel-equality
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (not (equal c (cons 0 0)))
                       (equal (lw-complex-mul c a) (lw-complex-mul c b)))
                  (equal a b))
         :hints (("Goal"
                  :use ((:instance lw-complex-linear-solve (a c) (b a)
                            (c (lw-complex-mul c a)))
                        (:instance lw-complex-linear-solve (a c) (b b)
                            (c (lw-complex-mul c a)))))) :rule-classes nil))

(defun lw-zeta-factor-transform (point zero multiplicity)
  (lw-complex-scale (nfix multiplicity)
    (lw-complex-quotient (lw-complex-sub (lw-complex-add point (cons 1 0)) zero)
      (lw-complex-mul (lw-complex-sub (cons 1 0) zero)
        (lw-complex-mul point (lw-complex-sub point zero))))))

(defun lw-zeta-factor-regular-value (point zero multiplicity)
  (lw-complex-scale (- (nfix multiplicity))
    (lw-complex-mul (lw-complex-reciprocal zero) (lw-complex-reciprocal point))))

(defthm lw-zeta-factor-transform-rational
  (implies (and (lw-complexp point) (lw-complexp zero))
           (and (lw-complexp (lw-zeta-factor-transform point zero multiplicity))
                (lw-complexp (lw-zeta-factor-regular-value point zero multiplicity)))))

(local (defthm lw-zft-numerator-identity
         (implies (and (lw-complexp point) (lw-complexp zero))
                  (equal
                    (lw-complex-sub (lw-complex-sub (cons 1 0) zero)
                      (lw-complex-mul point (lw-complex-sub point zero)))
                    (lw-complex-scale -1
                      (lw-complex-mul (lw-complex-sub point (cons 1 0))
                        (lw-complex-sub (lw-complex-add point (cons 1 0)) zero)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-scale lw-complex-mul)))))

(local (defthm lw-zft-middle-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (not (equal a (cons 0 0))))
                  (equal
                   (lw-complex-mul a
                     (lw-complex-mul b (lw-complex-mul (lw-complex-reciprocal a) c)))
                   (lw-complex-mul b c)))
         :hints (("Goal"
                  :use ((:instance lw-complex-mul-left-commutes
                          (c (lw-complex-mul (lw-complex-reciprocal a) c))))
                  :in-theory (disable lw-complex-mul-commutative
                                      lw-complex-mul-left-commutes)))))

(local (defthm lw-zft-reciprocal-two-term
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp s)
                       (not (equal a (cons 0 0))) (not (equal b (cons 0 0))))
                  (equal
                   (lw-complex-sub (lw-complex-reciprocal a)
                     (lw-complex-mul s (lw-complex-reciprocal b)))
                   (lw-complex-mul
                     (lw-complex-sub b (lw-complex-mul s a))
                     (lw-complex-mul (lw-complex-reciprocal a) (lw-complex-reciprocal b)))))
         :hints (("Goal"
                  :in-theory (e/d (lw-complex-mul-commutative lw-complex-mul-left-commutes)
                                  (lw-zft-numerator-identity lw-zft-one-minus-sign))
                  :do-not-induct t))))

; The original normalization is recovered away from its removable point.
(defthm lw-zeta-factor-transform-normalized
  (implies (and (lw-complexp point) (lw-complexp zero) (natp multiplicity)
                (not (equal point (cons 0 0))) (not (equal point (cons 1 0)))
                (not (equal point zero)) (not (equal zero (cons 1 0))))
           (equal (lw-zeta-factor-transform point zero multiplicity)
             (lw-complex-scale (- multiplicity)
               (lw-complex-quotient
                 (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub point zero))
                   (lw-complex-mul point
                     (lw-complex-reciprocal (lw-complex-sub (cons 1 0) zero))))
                 (lw-zeta-residue-denominator point)))))
  :hints (("Goal"
           :in-theory (e/d (lw-zeta-factor-transform lw-zeta-residue-denominator
                            lw-complex-quotient lw-complex-reciprocal-product
                            lw-complex-mul-commutative lw-complex-mul-left-commutes)
                           (lw-complex-mul-distribute lw-complex-mul-add-left
                            lw-complex-mul-subtract lw-zft-one-minus-sign))
           :do-not-induct t)))


(local (defthm lw-zft-reciprocal-negative
         (implies (lw-complexp point)
                  (equal (lw-complex-reciprocal (lw-complex-scale -1 point))
                         (lw-complex-scale -1 (lw-complex-reciprocal point))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-reciprocal lw-complex-scale
                                          lw-complex-conjugate lw-complex-norm-square)))))

(local (defthm lw-zft-residue-positive-form
         (implies (and (lw-complexp zero) (natp multiplicity)
                       (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))))
                  (equal (lw-zeta-pole-residue zero multiplicity)
                         (lw-complex-scale multiplicity
                           (lw-complex-mul (lw-complex-reciprocal zero)
                             (lw-complex-reciprocal (lw-complex-sub (cons 1 0) zero))))))
         :hints (("Goal"
                  :in-theory (e/d (lw-zeta-pole-residue lw-zeta-residue-denominator
                                   lw-complex-reciprocal-product
                                   lw-complex-mul-commutative lw-complex-mul-left-commutes)
                                  (lw-complex-mul-subtract lw-complex-mul-distribute
                                   lw-complex-mul-add-left))))))

(local (defthm lw-zft-split-numerator
         (implies (and (lw-complexp point) (lw-complexp zero))
                  (equal
                   (lw-complex-mul zero (lw-complex-sub (lw-complex-add (cons 1 0) point) zero))
                   (lw-complex-sub point
                     (lw-complex-mul (lw-complex-sub (cons 1 0) zero)
                                     (lw-complex-sub point zero)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul lw-complex-scale)))))

(local (defthm lw-zft-scale-mul-right
         (implies (and (rationalp scale) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-mul a (lw-complex-scale scale b))
                         (lw-complex-scale scale (lw-complex-mul a b))))
         :hints (("Goal" :use ((:instance lw-complex-scale-product (factor scale)
                                (left a) (right b)))
                         :in-theory (disable lw-complex-scale-product)))))

(local (defthm lw-zft-scale-subtract
         (implies (and (rationalp scale) (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-scale scale (lw-complex-sub a b))
                         (lw-complex-add (lw-complex-scale scale a)
                                         (lw-complex-scale (- scale) b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add
                                          lw-complex-sub lw-complex-scale)))))

(defthm lw-zeta-factor-transform-principal-part
  (implies (and (lw-complexp point) (lw-complexp zero) (natp multiplicity)
                (not (equal point (cons 0 0))) (not (equal point zero))
                (not (equal zero (cons 0 0))) (not (equal zero (cons 1 0))))
           (equal
            (lw-zeta-factor-transform point zero multiplicity)
            (lw-complex-add
              (lw-complex-quotient (lw-zeta-pole-residue zero multiplicity)
                                   (lw-complex-sub point zero))
              (lw-zeta-factor-regular-value point zero multiplicity))))
  :hints (("Goal"
           :use ((:instance lw-zft-scale-subtract (scale multiplicity) (a point)
                   (b (lw-complex-mul (lw-complex-sub (cons 1 0) zero)
                                       (lw-complex-sub point zero))))
                 (:instance lw-zft-cancel-equality
                   (a (lw-zeta-factor-transform point zero multiplicity))
                   (b (lw-complex-add
                        (lw-complex-quotient (lw-zeta-pole-residue zero multiplicity)
                                             (lw-complex-sub point zero))
                        (lw-zeta-factor-regular-value point zero multiplicity)))
                   (c (lw-complex-mul point
                        (lw-complex-mul zero
                          (lw-complex-mul (lw-complex-sub (cons 1 0) zero)
                                          (lw-complex-sub point zero)))))))
           :in-theory
           (e/d (lw-zeta-factor-transform lw-zeta-factor-regular-value lw-complex-quotient
                 lw-complex-reciprocal-product lw-complex-mul-commutative
                 lw-complex-mul-left-commutes)
                (lw-complex-mul-subtract lw-zft-one-minus-sign
                 lw-complex-sub-add-first lw-complex-scale-product lw-zft-scale-subtract
                 lw-zeta-factor-transform-normalized))
           :do-not-induct t)))

(local (in-theory
        (disable lw-zeta-factor-transform lw-zeta-factor-regular-value
                 lw-zft-one-minus-sign lw-zft-residue-positive-form lw-zft-scale-subtract)))

(defun lw-zeta-factor-family-transform (point entries)
  (if (endp entries) (cons 0 0)
    (lw-complex-add (lw-zeta-factor-transform point (caar entries) (cdar entries))
                    (lw-zeta-factor-family-transform point (cdr entries)))))

(defun lw-zeta-factor-origin-residue (entries)
  (if (endp entries) (cons 0 0)
    (lw-complex-add
      (lw-complex-scale (- (nfix (cdar entries))) (lw-complex-reciprocal (caar entries)))
      (lw-zeta-factor-origin-residue (cdr entries)))))

(defun lw-zeta-factor-family-regular-value (point entries)
  (lw-complex-quotient (lw-zeta-factor-origin-residue entries) point))

(defthm lw-zeta-factor-family-rational
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries))
           (and (lw-complexp (lw-zeta-factor-family-transform point entries))
                (lw-complexp (lw-zeta-factor-origin-residue entries))
                (lw-complexp (lw-zeta-factor-family-regular-value point entries)))))

(local (defthm lw-zft-constant-pole-value
         (implies (and (lw-complexp residue) (lw-complexp offset))
                  (equal (lw-pole-coefficient residue offset 0)
                         (lw-complex-quotient residue offset)))
         :hints (("Goal" :in-theory (enable lw-pole-coefficient lw-complex-power
                                          lw-complex-quotient)))))

(defthm lw-zeta-factor-family-principal-parts
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (lw-factor-model-away-check point entries) (not (equal point (cons 0 0))))
           (equal
            (lw-zeta-factor-family-transform point entries)
            (lw-complex-add (lw-zeta-pole-coefficient-sum point entries 0)
                            (lw-zeta-factor-family-regular-value point entries))))
  :hints (("Goal" :induct (lw-zeta-factor-family-transform point entries)
                  :in-theory
                  (e/d (lw-factor-model-away-check lw-zeta-pole-coefficient-sum
                        lw-zeta-factor-family-regular-value lw-complex-quotient
                        lw-zeta-factor-regular-value lw-complex-mul-commutative
                        lw-complex-mul-left-commutes)
                       (lw-zeta-factor-transform-normalized lw-complex-scale-product
                        lw-complex-mul-subtract)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-zeta-factor-transform-principal-part
                          (zero (caar entries)) (multiplicity (cdar entries))))
                 :cases ((equal point (caar entries))) :do-not-induct t))))

(defthm lw-zeta-factor-family-normalized
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (lw-factor-model-away-check point entries)
                (not (equal point (cons 0 0))) (not (equal point (cons 1 0))))
           (equal
            (lw-zeta-factor-family-transform point entries)
            (lw-complex-scale -1
              (lw-complex-quotient
                (lw-complex-sub (lw-factor-model-log-sum point entries)
                  (lw-complex-mul point (lw-factor-model-log-sum (cons 1 0) entries)))
                (lw-zeta-residue-denominator point)))))
  :hints (("Goal" :induct (lw-zeta-factor-family-transform point entries)
                  :in-theory
                  (e/d (lw-factor-model-away-check lw-factor-model-log-sum
                        lw-complex-quotient lw-complex-mul-commutative
                        lw-complex-mul-left-commutes lw-zft-scale-subtract)
                       (lw-zeta-factor-transform-principal-part lw-complex-scale-product
                        lw-zeta-factor-family-principal-parts lw-zft-reciprocal-two-term)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-zeta-factor-transform-normalized
                          (zero (caar entries)) (multiplicity (cdar entries))))
                 :cases ((equal point (caar entries))) :do-not-induct t))))

(local (in-theory
        (disable lw-zeta-factor-family-transform lw-zeta-factor-origin-residue
                 lw-zeta-factor-family-regular-value)))

(defthm lw-zeta-factor-family-regular-bound
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (rationalp clearance) (< 0 clearance)
                (<= (* clearance clearance) (lw-complex-norm-square point)))
           (lw-complex-diskp (lw-zeta-factor-family-regular-value point entries)
             (* (lw-complex-l1 (lw-zeta-factor-origin-residue entries)) (/ clearance))))
  :hints (("Goal"
           :use ((:instance lw-complex-l1-bound (point (lw-zeta-factor-origin-residue entries)))
                 (:instance lw-complex-reciprocal-disk-bound (lower clearance))
                 (:instance lw-complex-mul-disk
                   (left (lw-zeta-factor-origin-residue entries))
                   (radius (lw-complex-l1 (lw-zeta-factor-origin-residue entries)))
                   (right (lw-complex-reciprocal point)) (other-radius (/ clearance))))
           :in-theory (e/d (lw-zeta-factor-family-regular-value lw-complex-quotient)
                           (lw-complex-l1-bound lw-complex-reciprocal-disk-bound
                            lw-complex-mul-disk)))))

(defthm lw-zeta-factor-origin-coefficient-bound
  (implies (and (lw-complexp center) (lw-zeta-pole-familyp entries) (natp index)
                (rationalp clearance) (< 0 clearance)
                (<= (* clearance clearance) (lw-complex-norm-square center)))
           (lw-complex-diskp
             (lw-pole-coefficient (lw-zeta-factor-origin-residue entries) center index)
             (* (lw-complex-l1 (lw-zeta-factor-origin-residue entries))
                (lw-rational-power (/ clearance) (+ 1 index)))))
  :hints (("Goal"
           :use ((:instance lw-pole-coefficient-clearance-upper
                   (residue (lw-zeta-factor-origin-residue entries)) (offset center)))
           :in-theory (disable lw-pole-coefficient-clearance-upper))))

; These are test locations for the rational identity, not asserted zeta zeros.
(assert-event (and (equal (lw-zeta-factor-transform (cons 1 0) (cons 1/2 0) 2) (cons 12 0))
                   (equal (lw-zeta-factor-transform (cons 2 0) (cons 1/2 0) 2) (cons 10/3 0))))

(local (defthm lw-zft-factors-away-one
         (implies (lw-zeta-pole-familyp entries)
                  (lw-factor-model-away-check (cons 1 0) entries))
         :hints (("Goal" :induct (lw-factor-model-away-check (cons 1 0) entries)
                         :in-theory (enable lw-factor-model-away-check)))))

(local (in-theory
        (disable lw-factor-model-value lw-factor-model-derivative lw-factor-model-log-sum
                 lw-factor-model-away-check lw-zeta-pole-familyp)))

(defthm lw-zeta-factor-product-transform
  (implies (and (lw-complexp point) (lw-zeta-pole-familyp entries)
                (lw-factor-model-away-check point entries)
                (not (equal point (cons 0 0))) (not (equal point (cons 1 0))))
           (equal
            (lw-zeta-factor-family-transform point entries)
            (lw-complex-scale -1
              (lw-complex-quotient
                (lw-complex-sub
                  (lw-complex-quotient (lw-factor-model-derivative point entries)
                                       (lw-factor-model-value point entries))
                  (lw-complex-mul point
                    (lw-complex-quotient (lw-factor-model-derivative (cons 1 0) entries)
                                         (lw-factor-model-value (cons 1 0) entries))))
                (lw-zeta-residue-denominator point)))))
  :hints (("Goal"
           :use (lw-zeta-factor-family-normalized lw-factor-model-log-derivative
                 (:instance lw-factor-model-log-derivative (point (cons 1 0))))
           :in-theory (disable lw-zeta-factor-family-normalized lw-factor-model-log-derivative)
           :do-not-induct t)))
