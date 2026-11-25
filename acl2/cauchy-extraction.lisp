(in-package "ACL2")

(include-book "cauchy-polynomials")

; A computed sample count recovers an actual polynomial coefficient.
; Boundary checks are evaluations of the polynomial at rational points.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-conjugate lw-complex-norm-square lw-complex-diskp lw-diskp
                 lw-complex-power lw-complex-polynomial lw-complex-coefficient-at lw-complex-l1
                 lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-cauchy-moment-count lw-cauchy-orbit-moment
                 lw-cauchy-moment-expansion lw-cauchy-correlation-expansion lw-cauchy-residual-expansion
                 lw-complex-correlation-sum lw-complex-signed-power lw-complex-geometric-average
                 lw-complex-geometric-sum lw-cauchy-evaluation-sum lw-cauchy-polynomial-average
                 lw-cauchy-evaluation-sum-expansion lw-cauchy-evaluation-sum-first
                 lw-complex-conjugate-power lw-complex-power-power
                 lw-cauchy-polynomial-average-moments lw-cauchy-scaled-expansion)))

(local (defthm lw-ce-zero-times (equal (* 0 a) 0)))
(local (defthm lw-ce-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-ce-add-cancel
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (- a) b) b))))

(defthm lw-cauchy-coefficient-recovery
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (natp target) (< target (len coefficients))
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-polynomial-average coefficients degree target (lw-cauchy-moment-count degree error))
             (nth target coefficients))
            (* (lw-complex-coefficient-mass coefficients) error)))
  :hints (("Goal" :use ((:instance lw-cauchy-residual-expansion-bound (offset 0))
                        (:instance lw-cauchy-residual-expansion-identity
                          (offset 0) (count (lw-cauchy-moment-count degree error)))
                        (:instance lw-complex-coefficient-at-nth (offset 0))
                        (:instance lw-cauchy-polynomial-average-moments
                          (count (lw-cauchy-moment-count degree error))))
                  :in-theory (disable lw-cauchy-residual-expansion-bound
                                      lw-cauchy-residual-expansion-identity
                                      lw-complex-coefficient-at-nth))))

(defun lw-cauchy-coefficient-precision (coefficients error)
  (/ error (+ 1 (lw-complex-coefficient-mass coefficients))))

(defun lw-cauchy-coefficient-count (coefficients degree error)
  (lw-cauchy-moment-count degree (lw-cauchy-coefficient-precision coefficients error)))

(defthm lw-cauchy-coefficient-count-natural
  (and (natp (lw-cauchy-coefficient-count coefficients degree error))
       (< 0 (lw-cauchy-coefficient-count coefficients degree error)))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-ce-precision
         (implies (and (rationalp mass) (<= 0 mass) (rationalp error) (< 0 error))
                  (and (rationalp (/ error (+ 1 mass))) (< 0 (/ error (+ 1 mass)))
                       (<= (* mass (/ error (+ 1 mass))) error)))
         :hints (("Goal" :use ((:instance lw-positive-division-bound
                                 (numerator (* mass error)) (divisor (+ 1 mass)) (bound error)))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-cauchy-coefficient-precision-adequate
  (implies (and (lw-complex-coefficientsp coefficients) (rationalp error) (< 0 error))
           (and (rationalp (lw-cauchy-coefficient-precision coefficients error))
                (< 0 (lw-cauchy-coefficient-precision coefficients error))
                (<= (* (lw-complex-coefficient-mass coefficients)
                       (lw-cauchy-coefficient-precision coefficients error)) error)))
  :hints (("Goal" :use (lw-complex-coefficient-mass-valid
                        (:instance lw-ce-precision (mass (lw-complex-coefficient-mass coefficients))))
                  :in-theory (disable lw-complex-coefficient-mass
                                      lw-complex-coefficient-mass-valid))))

(defthm lw-cauchy-computed-coefficient-recovery
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (natp target) (< target (len coefficients))
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-polynomial-average coefficients degree target
                                           (lw-cauchy-coefficient-count coefficients degree error))
             (nth target coefficients)) error))
  :hints (("Goal" :use (lw-cauchy-coefficient-precision-adequate
                        (:instance lw-cauchy-coefficient-recovery
                          (error (lw-cauchy-coefficient-precision coefficients error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                                  (lw-cauchy-polynomial-average coefficients degree target
                                                                (lw-cauchy-coefficient-count coefficients degree error))
                                  (nth target coefficients)))
                          (radius (* (lw-complex-coefficient-mass coefficients)
                                     (lw-cauchy-coefficient-precision coefficients error)))
                          (cap error)))
                  :in-theory (disable lw-complex-coefficient-mass lw-cauchy-coefficient-precision
                                      lw-cauchy-coefficient-recovery
                                      lw-cauchy-coefficient-precision-adequate))))

(defun lw-cauchy-boundary-check (coefficients point offset count cap)
  (if (zp count) t
    (and (lw-complex-diskp
          (lw-complex-polynomial coefficients (lw-complex-power point (- count 1)) offset) cap)
         (lw-cauchy-boundary-check coefficients point offset (- count 1) cap))))

(local (defun lw-ce-countdown (count)
         (declare (xargs :measure (nfix count)))
         (if (zp count) 0 (lw-ce-countdown (- count 1)))))

(defthm lw-cauchy-unit-weight-bound
  (implies (and (lw-complex-diskp point 1) (natp target) (natp index))
           (lw-complex-diskp
            (lw-complex-conjugate (lw-complex-power (lw-complex-power point index) target)) 1))
  :hints (("Goal" :use ((:instance lw-complex-unit-power)
                        (:instance lw-complex-unit-power
                          (point (lw-complex-power point index)) (index target))
                        (:instance lw-complex-conjugate-disk
                          (point (lw-complex-power (lw-complex-power point index) target)) (radius 1)))
                  :in-theory (disable lw-complex-conjugate-power lw-complex-power-power))))

(defthm lw-cauchy-evaluation-sum-bound
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complex-diskp point 1)
                (natp target) (natp offset) (natp count) (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check coefficients point offset count cap))
           (lw-complex-diskp
            (lw-cauchy-evaluation-sum coefficients point target offset count) (* count cap)))
  :hints (("Goal" :induct (lw-ce-countdown count)
                  :in-theory (enable lw-cauchy-evaluation-sum lw-cauchy-boundary-check))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cauchy-unit-weight-bound (index (- count 1)))
                        (:instance lw-complex-mul-disk
                          (left (lw-complex-polynomial coefficients (lw-complex-power point (- count 1)) offset))
                          (radius cap)
                          (right (lw-complex-conjugate
                                  (lw-complex-power (lw-complex-power point (- count 1)) target)))
                          (other-radius 1))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-mul
                                 (lw-complex-polynomial coefficients (lw-complex-power point (- count 1)) offset)
                                 (lw-complex-conjugate
                                  (lw-complex-power (lw-complex-power point (- count 1)) target))))
                          (radius cap)
                          (right (lw-cauchy-evaluation-sum coefficients point target offset (- count 1)))
                          (other-radius (* (- count 1) cap))))
                 :in-theory (disable lw-cauchy-evaluation-sum lw-cauchy-unit-weight-bound
                                     lw-complex-mul-disk lw-complex-add-disk
                                     lw-complex-coefficientsp)))))

(local (defthm lw-ce-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* (/ divisor) (* divisor coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x (/ divisor)) (y divisor) (z coefficient))
                              (:instance commutativity-of-* (x (/ divisor)) (y divisor))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defthm lw-cauchy-polynomial-average-bound
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (natp target) (posp count)
                (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check coefficients (lw-cauchy-orbit-rotation degree) 0 count cap))
           (lw-complex-diskp (lw-cauchy-polynomial-average coefficients degree target count) cap))
  :hints (("Goal" :use (lw-cauchy-orbit-data
                        (:instance lw-ce-inverse-factor (divisor count) (coefficient cap))
                        (:instance lw-cauchy-evaluation-sum-bound
                          (point (lw-cauchy-orbit-rotation degree)) (offset 0))
                        (:instance lw-complex-scale-disk
                          (point (lw-cauchy-evaluation-sum coefficients (lw-cauchy-orbit-rotation degree)
                                                         target 0 count))
                          (radius (* count cap)) (factor (/ count))))
                  :in-theory (e/d (lw-cauchy-polynomial-average)
                                  (lw-cauchy-evaluation-sum-expansion lw-complex-scale-add
                                   lw-cauchy-evaluation-sum-bound lw-complex-scale-disk
                                   lw-cauchy-boundary-check lw-ce-inverse-factor)))))

(defthm lw-cauchy-finite-coefficient-bound
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (natp target) (< target (len coefficients))
                (rationalp error) (< 0 error) (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check
                 coefficients (lw-cauchy-orbit-rotation degree) 0
                 (lw-cauchy-coefficient-count coefficients degree error) cap))
           (lw-complex-diskp (nth target coefficients) (+ cap error)))
  :hints (("Goal" :use (lw-cauchy-computed-coefficient-recovery
                        (:instance lw-cauchy-polynomial-average-bound
                          (count (lw-cauchy-coefficient-count coefficients degree error)))
                        (:instance lw-complex-coefficient-at-rational (offset 0))
                        (:instance lw-complex-coefficient-at-nth (offset 0))
                        (:instance lw-complex-subtract-cancel
                          (a (lw-cauchy-polynomial-average coefficients degree target
                                                          (lw-cauchy-coefficient-count coefficients degree error)))
                          (b (nth target coefficients)))
                        (:instance lw-complex-sub-disk
                          (left (lw-cauchy-polynomial-average coefficients degree target
                                                             (lw-cauchy-coefficient-count coefficients degree error)))
                          (radius cap)
                          (right (lw-complex-sub
                                  (lw-cauchy-polynomial-average coefficients degree target
                                                                (lw-cauchy-coefficient-count coefficients degree error))
                                  (nth target coefficients)))
                          (other-radius error)))
                  :in-theory (disable lw-complex-coefficient-mass lw-cauchy-coefficient-count
                                      lw-cauchy-boundary-check lw-cauchy-polynomial-average-moments
                                      lw-cauchy-computed-coefficient-recovery
                                      lw-cauchy-polynomial-average-bound
                                      lw-complex-coefficient-at-rational lw-complex-coefficient-at-nth
                                      lw-complex-subtract-cancel lw-complex-sub-disk))))

; Independent sign check: P(z)=1+2*i*z, target coefficient 1. The
; two-node average is (1+conjugate(63/65+16*i/65))/2 + 2*i.
(assert-event
 (equal (lw-cauchy-polynomial-average (list (cons 1 0) (cons 0 2)) 1 1 2)
        (cons 64/65 122/65)))
