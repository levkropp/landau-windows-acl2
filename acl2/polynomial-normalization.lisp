(in-package "ACL2")

(include-book "polynomial-maps")
(include-book "complex-quotients")

; Compute the normalized transform of a polynomial logarithmic derivative.
; R(s) = L(1)+k-D_1 L(s), so the removable singularity at 1 is absent.
; R(s)/s is a polynomial plus the explicitly computed residue R(0)/s.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-reciprocal lw-complex-norm-square lw-complex-quotient
                 lw-complex-polynomial lw-polynomial-divided-difference
                 lw-polynomial-multiply-coefficients lw-polynomial-add-constant
                 lw-complex-polynomial-horner
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-mul-subtract)))

(local (defthm lw-pn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-pn-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pn-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-pn-zero-times (equal (* 0 a) 0)))
(local (defthm lw-pn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-pn-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-pn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-pn-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-pn-sub-as-add
         (implies (and (lw-complexp a) (lw-complexp b))
                  (equal (lw-complex-add a (lw-complex-scale -1 b)) (lw-complex-sub a b)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-scale)))))

(local (defthm lw-pn-coefficient-parts
         (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients))
                  (and (lw-complexp (car coefficients))
                       (lw-complex-coefficientsp (cdr coefficients))))
         :hints (("Goal" :in-theory (enable lw-complex-coefficientsp)))))
(local (defthm lw-pn-add-constant-nonempty
         (consp (lw-polynomial-add-constant constant coefficients))
         :hints (("Goal" :in-theory (enable lw-polynomial-add-constant)))))

(defun lw-normalized-log-polynomial-numerator (coefficients correction)
  (lw-polynomial-add-constant
    (lw-complex-add (lw-complex-polynomial coefficients (cons 1 0) 0) correction)
    (lw-polynomial-multiply-coefficients (cons -1 0)
      (lw-polynomial-divided-difference coefficients (cons 1 0)))))

(defun lw-normalized-log-polynomial-value (point coefficients correction)
  (lw-complex-quotient
    (lw-complex-polynomial
      (lw-normalized-log-polynomial-numerator coefficients correction) point 0) point))

(defun lw-normalized-log-polynomial-regular (coefficients correction)
  (cdr (lw-normalized-log-polynomial-numerator coefficients correction)))

(defun lw-normalized-log-polynomial-origin (coefficients correction)
  (car (lw-normalized-log-polynomial-numerator coefficients correction)))

(defthm lw-normalized-log-polynomial-data
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp correction))
           (and
            (consp (lw-normalized-log-polynomial-numerator coefficients correction))
            (lw-complex-coefficientsp
              (lw-normalized-log-polynomial-numerator coefficients correction))
            (lw-complex-coefficientsp
              (lw-normalized-log-polynomial-regular coefficients correction))
            (lw-complexp (lw-normalized-log-polynomial-origin coefficients correction))))
  :hints (("Goal" :use ((:instance lw-pn-coefficient-parts
                          (coefficients
                            (lw-normalized-log-polynomial-numerator coefficients correction))))
                  :in-theory (disable lw-complex-coefficientsp)
                  :do-not-induct t)))

(defthm lw-normalized-log-polynomial-rational
  (implies (and (lw-complexp point) (lw-complex-coefficientsp coefficients) (lw-complexp correction))
           (lw-complexp (lw-normalized-log-polynomial-value point coefficients correction))))

(defthm lw-normalized-log-polynomial-numerator-evaluation
  (implies (and (lw-complexp point) (lw-complex-coefficientsp coefficients) (lw-complexp correction))
           (equal
            (lw-complex-polynomial
              (lw-normalized-log-polynomial-numerator coefficients correction) point 0)
            (lw-complex-sub
              (lw-complex-add (lw-complex-polynomial coefficients (cons 1 0) 0) correction)
              (lw-complex-polynomial
                (lw-polynomial-divided-difference coefficients (cons 1 0)) point 0))))
  :hints (("Goal" :in-theory (disable lw-polynomial-add-constant
                                     lw-polynomial-multiply-coefficients))))

(local (in-theory
        (disable lw-normalized-log-polynomial-numerator lw-normalized-log-polynomial-value
                 lw-normalized-log-polynomial-origin lw-normalized-log-polynomial-regular
                 lw-normalized-log-polynomial-numerator-evaluation)))

(local (defthm lw-pn-last-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a (cons 0 0))))
                  (equal (lw-complex-mul a
                           (lw-complex-mul b (lw-complex-reciprocal a))) b))
         :hints (("Goal" :use ((:instance lw-complex-mul-left-commutes
                                (c (lw-complex-reciprocal a))))
                         :in-theory (disable lw-complex-mul-commutative
                                             lw-complex-mul-left-commutes)))))

(local (defthm lw-pn-origin-split
         (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                       (lw-complexp constant) (lw-complexp tail))
                  (equal
                   (lw-complex-quotient
                     (lw-complex-add constant (lw-complex-mul point tail)) point)
                   (lw-complex-add tail (lw-complex-quotient constant point))))
         :hints (("Goal" :in-theory
                  (enable lw-complex-quotient lw-complex-mul-commutative
                          lw-complex-mul-left-commutes)))))

(defthm lw-normalized-log-polynomial-split
  (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                (lw-complex-coefficientsp coefficients) (lw-complexp correction))
           (equal
            (lw-normalized-log-polynomial-value point coefficients correction)
            (lw-complex-add
              (lw-complex-polynomial
                (lw-normalized-log-polynomial-regular coefficients correction) point 0)
              (lw-complex-quotient
                (lw-normalized-log-polynomial-origin coefficients correction) point))))
  :hints (("Goal"
           :use ((:instance lw-complex-polynomial-horner
                   (coefficients (lw-normalized-log-polynomial-numerator coefficients correction))))
           :in-theory (e/d (lw-normalized-log-polynomial-value
                            lw-normalized-log-polynomial-regular lw-normalized-log-polynomial-origin)
                           (lw-complex-polynomial-horner))
           :do-not-induct t)))

(assert-event
 (let ((coefficients (list (cons 1 0) (cons 2 0) (cons 3 0))))
   (and (equal (lw-normalized-log-polynomial-numerator coefficients (cons 4 0))
               (list (cons 5 0) (cons -3 0)))
        (equal (lw-normalized-log-polynomial-value (cons 1 0) coefficients (cons 4 0)) (cons 2 0))
        (equal (lw-normalized-log-polynomial-value (cons 2 0) coefficients (cons 4 0)) (cons -1/2 0)))))

(local (defthm lw-pn-sub-not-zero
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a b)))
                  (not (equal (lw-complex-sub a b) (cons 0 0))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(local (defthm lw-pn-numerator-factor
         (implies
          (and (lw-complexp point) (lw-complexp value) (lw-complexp at-one)
               (lw-complexp difference) (lw-complexp correction)
               (equal (lw-complex-sub value at-one)
                      (lw-complex-mul (lw-complex-sub point (cons 1 0)) difference)))
          (equal
           (lw-complex-add (lw-complex-sub value (lw-complex-mul point at-one))
             (lw-complex-mul correction (lw-complex-sub (cons 1 0) point)))
           (lw-complex-scale -1
             (lw-complex-mul (lw-complex-sub point (cons 1 0))
               (lw-complex-sub (lw-complex-add at-one correction) difference)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul lw-complex-scale)
                         :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-pn-quotient-scale
         (implies (and (rationalp factor) (lw-complexp numerator) (lw-complexp denominator))
                  (equal (lw-complex-quotient (lw-complex-scale factor numerator) denominator)
                         (lw-complex-scale factor (lw-complex-quotient numerator denominator))))
         :hints (("Goal"
                  :use ((:instance lw-complex-scale-product (left (lw-complex-reciprocal denominator))
                            (right numerator))
                        (:instance lw-complex-mul-commutative
                          (left (lw-complex-scale factor numerator))
                          (right (lw-complex-reciprocal denominator)))
                        (:instance lw-complex-mul-commutative (left numerator)
                          (right (lw-complex-reciprocal denominator))))
                  :in-theory (e/d (lw-complex-quotient) (lw-complex-scale-product))))))

(local (defthm lw-pn-quotient-factor-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                       (not (equal b (cons 0 0))) (not (equal c (cons 0 0))))
                  (equal (lw-complex-quotient (lw-complex-mul c a) (lw-complex-mul b c))
                         (lw-complex-quotient a b)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient lw-complex-reciprocal-product
                                          lw-complex-mul-left-commutes
                                          lw-complex-mul-commutative)))))

(local (defthm lw-pn-quotient-normalization
         (implies (and (lw-complexp point) (lw-complexp numerator)
                       (not (equal point (cons 0 0))) (not (equal point (cons 1 0))))
                  (equal
                   (lw-complex-scale -1
                     (lw-complex-quotient
                       (lw-complex-scale -1
                         (lw-complex-mul (lw-complex-sub point (cons 1 0)) numerator))
                       (lw-complex-mul point (lw-complex-sub point (cons 1 0)))))
                   (lw-complex-quotient numerator point)))
         :hints (("Goal" :in-theory (disable lw-complex-scale-product
                                            lw-complex-mul-subtract
                                            lw-complex-mul-distribute
                                            lw-complex-mul-add-left)))))

(defthm lw-normalized-log-polynomial-normalized
  (implies (and (lw-complexp point) (lw-complex-coefficientsp coefficients)
                (lw-complexp correction)
                (not (equal point (cons 0 0))) (not (equal point (cons 1 0))))
           (equal
            (lw-normalized-log-polynomial-value point coefficients correction)
            (lw-complex-scale -1
              (lw-complex-quotient
                (lw-complex-add
                  (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                    (lw-complex-mul point (lw-complex-polynomial coefficients (cons 1 0) 0)))
                  (lw-complex-mul correction (lw-complex-sub (cons 1 0) point)))
                (lw-complex-mul point (lw-complex-sub point (cons 1 0)))))))
  :hints (("Goal"
           :use ((:instance lw-polynomial-divided-difference-identity (anchor (cons 1 0)))
                 (:instance lw-pn-numerator-factor
                   (value (lw-complex-polynomial coefficients point 0))
                   (at-one (lw-complex-polynomial coefficients (cons 1 0) 0))
                   (difference (lw-complex-polynomial
                     (lw-polynomial-divided-difference coefficients (cons 1 0)) point 0))))
           :in-theory (e/d (lw-normalized-log-polynomial-value
                            lw-normalized-log-polynomial-numerator-evaluation)
                           (lw-polynomial-divided-difference-identity
                            lw-complex-mul-subtract lw-complex-mul-distribute
                            lw-complex-mul-add-left lw-complex-scale-product
                            lw-normalized-log-polynomial-split))
           :do-not-induct t)))
