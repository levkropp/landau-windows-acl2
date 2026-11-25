(in-package "ACL2")

(include-book "cauchy-polynomials")

; Construct the polynomial (P(s)-P(a))/(s-a), including at s=a.
; The coefficients are computed by synthetic division. This is needed to
; normalize a polynomial regular logarithmic derivative at s=1.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-power lw-rational-power
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-complex-polynomial lw-complex-mul-subtract)))

(local (defthm lw-pdd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-pdd-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pdd-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-pdd-zero-times (equal (* 0 a) 0)))
(local (defthm lw-pdd-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-pdd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pdd-power-step
         (implies (and (lw-complexp point) (natp offset))
                  (equal (lw-complex-power point (+ 1 offset))
                         (lw-complex-mul point (lw-complex-power point offset))))
         :hints (("Goal" :expand ((lw-complex-power point (+ 1 offset)))
                         :in-theory (disable lw-complex-power-add)))))

(defthm lw-complex-polynomial-offset-step
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp offset))
           (equal (lw-complex-polynomial coefficients point (+ 1 offset))
                  (lw-complex-mul point (lw-complex-polynomial coefficients point offset))))
  :hints (("Goal" :induct (lw-complex-polynomial coefficients point offset)
                  :in-theory (enable lw-complex-polynomial lw-complex-mul-commutative
                                     lw-complex-mul-left-commutes))))

(defthm lw-complex-polynomial-horner
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (consp coefficients))
           (equal (lw-complex-polynomial coefficients point 0)
                  (lw-complex-add (car coefficients)
                    (lw-complex-mul point (lw-complex-polynomial (cdr coefficients) point 0)))))
  :hints (("Goal"
           :expand ((lw-complex-polynomial coefficients point 0) (lw-complex-power point 0))
           :use ((:instance lw-complex-polynomial-offset-step
                   (coefficients (cdr coefficients)) (offset 0)))
           :in-theory (disable lw-complex-polynomial-offset-step))))

(defun lw-polynomial-divided-difference (coefficients anchor)
  (if (or (endp coefficients) (endp (cdr coefficients))) nil
    (cons (lw-complex-polynomial (cdr coefficients) anchor 0)
          (lw-polynomial-divided-difference (cdr coefficients) anchor))))

(defthm lw-polynomial-divided-difference-valid
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp anchor))
           (and (lw-complex-coefficientsp (lw-polynomial-divided-difference coefficients anchor))
                (equal (len (lw-polynomial-divided-difference coefficients anchor))
                       (if (consp coefficients) (- (len coefficients) 1) 0))))
  :hints (("Goal" :induct (lw-polynomial-divided-difference coefficients anchor)
                  :in-theory (disable lw-complex-polynomial-horner
                                      lw-complex-polynomial-offset-step))))

(local (defthm lw-pdd-step-identity
         (implies (and (lw-complexp c) (lw-complexp point) (lw-complexp anchor)
                       (lw-complexp p) (lw-complexp q))
                  (equal
                   (lw-complex-sub
                     (lw-complex-add c (lw-complex-mul point p))
                     (lw-complex-add c (lw-complex-mul anchor q)))
                   (lw-complex-add
                     (lw-complex-mul (lw-complex-sub point anchor) q)
                     (lw-complex-mul point (lw-complex-sub p q)))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub
                                          lw-complex-mul)))))

(local (defthm lw-pdd-step
         (implies
          (and (lw-complexp c) (lw-complexp point) (lw-complexp anchor)
               (lw-complexp p) (lw-complexp q) (lw-complexp d)
               (equal (lw-complex-sub p q)
                      (lw-complex-mul (lw-complex-sub point anchor) d)))
          (equal
           (lw-complex-sub (lw-complex-add c (lw-complex-mul point p))
                           (lw-complex-add c (lw-complex-mul anchor q)))
           (lw-complex-mul (lw-complex-sub point anchor)
                           (lw-complex-add q (lw-complex-mul point d)))))
         :hints (("Goal" :use (lw-pdd-step-identity)
                         :in-theory (e/d (lw-complex-mul-commutative
                                          lw-complex-mul-left-commutes)
                                         (lw-pdd-step-identity))))
         :rule-classes nil))

(local (in-theory (disable lw-polynomial-divided-difference lw-pdd-step-identity)))

(local (defthm lw-pdd-polynomial-nil
         (equal (lw-complex-polynomial nil point offset) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-polynomial)))))
(local (defthm lw-pdd-divided-difference-nil
         (equal (lw-polynomial-divided-difference nil anchor) nil)
         :hints (("Goal" :in-theory (enable lw-polynomial-divided-difference)))))
(local (defthm lw-pdd-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-pdd-sub-self
         (implies (lw-complexp point) (equal (lw-complex-sub point point) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub)))))

(defthm lw-polynomial-divided-difference-identity
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (lw-complexp anchor))
           (equal
            (lw-complex-sub (lw-complex-polynomial coefficients point 0)
                            (lw-complex-polynomial coefficients anchor 0))
            (lw-complex-mul (lw-complex-sub point anchor)
              (lw-complex-polynomial (lw-polynomial-divided-difference coefficients anchor) point 0))))
  :hints (("Goal" :induct (lw-polynomial-divided-difference coefficients anchor)
                  :expand ((lw-polynomial-divided-difference coefficients anchor))
                  :in-theory (enable (:induction lw-polynomial-divided-difference)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-pdd-step (c (car coefficients))
                          (p (lw-complex-polynomial (cdr coefficients) point 0))
                          (q (lw-complex-polynomial (cdr coefficients) anchor 0))
                          (d (lw-complex-polynomial
                               (lw-polynomial-divided-difference (cdr coefficients) anchor)
                               point 0))))
                 :do-not-induct t))))

(assert-event
 (let* ((coefficients (list (cons 1 0) (cons 2 0) (cons 3 0)))
        (quotient (lw-polynomial-divided-difference coefficients (cons 1 0))))
   (and (equal quotient (list (cons 5 0) (cons 3 0)))
        (equal (lw-complex-polynomial quotient (cons 1 0) 0) (cons 8 0))
        (equal (lw-complex-polynomial quotient (cons 2 0) 0) (cons 11 0)))))
