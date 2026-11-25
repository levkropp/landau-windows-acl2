(in-package "ACL2")

(include-book "cauchy-orbits")

; Exact finite coefficient extraction from polynomial values on a rational
; unit-circle orbit. The sample average is evaluated from the polynomial,
; independently of the moment expansion used to prove its error bound.

(local (defthm lw-cp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cp-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cp-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cp-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cp-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(defthm lw-complex-scale-rational
  (implies (and (rationalp factor) (lw-complexp point))
           (lw-complexp (lw-complex-scale factor point))))

(defthm lw-complex-add-commutative
  (implies (and (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-add left right) (lw-complex-add right left))))

(defthm lw-complex-add-associative
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-add (lw-complex-add a b) c)
                  (lw-complex-add a (lw-complex-add b c)))))

(defthm lw-complex-add-zero
  (implies (lw-complexp point)
           (and (equal (lw-complex-add point (cons 0 0)) point)
                (equal (lw-complex-add (cons 0 0) point) point))))

(defthm lw-complex-conjugate-add
  (implies (and (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-conjugate (lw-complex-add left right))
                  (lw-complex-add (lw-complex-conjugate left)
                                  (lw-complex-conjugate right)))))

(defthm lw-complex-conjugate-scale
  (implies (and (rationalp factor) (lw-complexp point))
           (equal (lw-complex-conjugate (lw-complex-scale factor point))
                  (lw-complex-scale factor (lw-complex-conjugate point)))))

(defthm lw-complex-conjugate-product
  (implies (and (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-conjugate (lw-complex-mul left right))
                  (lw-complex-mul (lw-complex-conjugate left)
                                  (lw-complex-conjugate right)))))

(defthm lw-complex-conjugate-involution
  (implies (lw-complexp point)
           (equal (lw-complex-conjugate (lw-complex-conjugate point)) point)))

(defthm lw-complex-product-conjugate
  (implies (lw-complexp point)
           (equal (lw-complex-mul point (lw-complex-conjugate point))
                  (cons (lw-complex-norm-square point) 0))))

(defthm lw-complex-scale-add
  (implies (and (rationalp factor) (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-scale factor (lw-complex-add left right))
                  (lw-complex-add (lw-complex-scale factor left)
                                  (lw-complex-scale factor right)))))

(defthm lw-complex-scale-product
  (implies (and (rationalp factor) (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-scale factor (lw-complex-mul left right))
                  (lw-complex-mul left (lw-complex-scale factor right)))))

(defthm lw-complex-scale-zero
  (equal (lw-complex-scale factor (cons 0 0)) (cons 0 0)))

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul
                 lw-complex-scale lw-complex-conjugate lw-complex-norm-square
                 lw-complex-power lw-complex-diskp lw-diskp
                 lw-complex-power-add lw-complex-power-power)))

(defthm lw-complex-mul-left-commutes
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-mul a (lw-complex-mul b c))
                  (lw-complex-mul b (lw-complex-mul a c))))
  :hints (("Goal" :use ((:instance lw-complex-mul-associative (left a) (middle b) (right c))
                        (:instance lw-complex-mul-associative (left b) (middle a) (right c))
                        (:instance lw-complex-mul-commutative (left a) (right b)))
                  :in-theory (disable lw-complex-mul-associative lw-complex-mul-commutative))))

(defthm lw-complex-conjugate-power
  (implies (and (lw-complexp point) (natp index))
           (equal (lw-complex-conjugate (lw-complex-power point index))
                  (lw-complex-power (lw-complex-conjugate point) index)))
  :hints (("Goal" :induct (lw-complex-power point index)
                  :in-theory (enable lw-complex-power lw-complex-conjugate))))

(defthm lw-complex-unit-power-product-conjugate
  (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1)
                (natp index))
           (equal (lw-complex-mul (lw-complex-power point index)
                                  (lw-complex-conjugate (lw-complex-power point index)))
                  (cons 1 0)))
  :hints (("Goal" :use ((:instance lw-complex-product-conjugate
                          (point (lw-complex-power point index))))
                  :in-theory (disable lw-complex-conjugate-power
                                      lw-complex-product-conjugate))))

(defthm lw-complex-power-correlation-positive
  (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1)
                (natp offset) (natp index))
           (equal (lw-complex-mul (lw-complex-power point (+ offset index))
                                  (lw-complex-conjugate (lw-complex-power point index)))
                  (lw-complex-power point offset)))
  :hints (("Goal" :use ((:instance lw-complex-power-add (left offset) (right index)))
                  :in-theory (disable lw-complex-conjugate-power
                                      lw-complex-mul-commutative lw-complex-mul-left-commutes))))

(defthm lw-complex-power-correlation
  (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1)
                (natp left) (natp right))
           (equal (lw-complex-mul (lw-complex-power point left)
                                  (lw-complex-conjugate (lw-complex-power point right)))
                  (if (<= right left)
                      (lw-complex-power point (- left right))
                    (lw-complex-conjugate (lw-complex-power point (- right left))))))
  :hints (("Goal" :cases ((<= right left))
                  :use ((:instance lw-complex-power-correlation-positive
                            (offset (- left right)) (index right))
                        (:instance lw-complex-power-correlation-positive
                            (offset (- right left)) (index left))
                        (:instance lw-complex-conjugate-product
                            (left (lw-complex-power point right))
                            (right (lw-complex-conjugate (lw-complex-power point left)))))
                  :in-theory (disable lw-complex-conjugate-power
                                      lw-complex-conjugate-product
                                      lw-complex-power-correlation-positive))))

(defthm lw-complex-add-left-commutes
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-add a (lw-complex-add b c))
                  (lw-complex-add b (lw-complex-add a c))))
  :hints (("Goal" :use ((:instance lw-complex-add-associative)
                        (:instance lw-complex-add-associative (a b) (b a))
                        (:instance lw-complex-add-commutative (left a) (right b)))
                  :in-theory (disable lw-complex-add-associative lw-complex-add-commutative))))

(defthm lw-complex-mul-add-left
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-mul (lw-complex-add a b) c)
                  (lw-complex-add (lw-complex-mul a c) (lw-complex-mul b c))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-mul))))

(defthm lw-complex-scale-one
  (implies (lw-complexp point) (equal (lw-complex-scale 1 point) point))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale))))

(local (defun lw-cp-countdown (index)
         (declare (xargs :measure (nfix index)))
         (if (zp index) 0 (lw-cp-countdown (- index 1)))))

(local (defthm lw-cp-geometric-zero
         (implies (zp count)
                  (equal (lw-complex-geometric-sum point count) (cons 0 0)))
         :hints (("Goal" :in-theory (enable lw-complex-geometric-sum)))))
(local (defthm lw-cp-power-zero
         (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-power)))))

(defthm lw-complex-geometric-append
  (implies (and (lw-complexp point) (natp count))
           (equal (lw-complex-geometric-sum point (+ 1 count))
                  (lw-complex-add (lw-complex-power point count)
                                  (lw-complex-geometric-sum point count))))
  :hints (("Goal" :induct (lw-cp-countdown count)
                  :in-theory (enable lw-complex-geometric-sum lw-complex-power
                                     lw-complex-add lw-complex-mul lw-complexp))))

(defun lw-complex-power-sum (point count)
  (if (zp count) (cons 0 0)
    (lw-complex-add (lw-complex-power point (- count 1))
                    (lw-complex-power-sum point (- count 1)))))

(defthm lw-complex-power-sum-rational
  (implies (and (lw-complexp point) (natp count))
           (lw-complexp (lw-complex-power-sum point count))))

(defthm lw-complex-power-sum-geometric
  (implies (and (lw-complexp point) (natp count))
           (equal (lw-complex-power-sum point count)
                  (lw-complex-geometric-sum point count)))
  :hints (("Goal" :induct (lw-complex-power-sum point count)
                  :in-theory (disable lw-complex-geometric-sum))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-geometric-append (count (- count 1))))
                 :in-theory (disable lw-complex-geometric-append lw-complex-geometric-sum)))))

(defun lw-complex-signed-power (point frequency)
  (if (< frequency 0)
      (lw-complex-conjugate (lw-complex-power point (nfix (- frequency))))
    (lw-complex-power point (nfix frequency))))

(defthm lw-complex-signed-power-rational
  (implies (and (lw-complexp point) (integerp frequency))
           (lw-complexp (lw-complex-signed-power point frequency))))

(defthm lw-complex-signed-power-compose
  (implies (and (lw-complexp point) (integerp frequency) (natp index))
           (equal (lw-complex-signed-power (lw-complex-power point index) frequency)
                  (lw-complex-power (lw-complex-signed-power point frequency) index)))
  :hints (("Goal" :in-theory (enable lw-complex-power-power))))

(defun lw-complex-correlation-sum (point left right count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (lw-complex-power (lw-complex-power point (- count 1)) left)
      (lw-complex-conjugate
       (lw-complex-power (lw-complex-power point (- count 1)) right)))
     (lw-complex-correlation-sum point left right (- count 1)))))

(defthm lw-complex-correlation-sum-rational
  (implies (and (lw-complexp point) (natp left) (natp right) (natp count))
           (lw-complexp (lw-complex-correlation-sum point left right count))))

(defthm lw-complex-correlation-sum-geometric
  (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1)
                (natp left) (natp right) (natp count))
           (equal (lw-complex-correlation-sum point left right count)
                  (lw-complex-geometric-sum
                   (lw-complex-signed-power point (- left right)) count)))
  :hints (("Goal" :induct (lw-complex-correlation-sum point left right count)
                  :in-theory (disable lw-complex-geometric-sum lw-complex-signed-power
                                      lw-complex-conjugate-power))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-geometric-append
                          (point (lw-complex-signed-power point (- left right)))
                          (count (- count 1)))
                        (:instance lw-complex-power-correlation
                          (point (lw-complex-power point (- count 1))))
                        (:instance lw-complex-signed-power-compose
                          (frequency (- left right)) (index (- count 1))))
                 :in-theory (e/d (lw-complex-signed-power)
                                 (lw-complex-geometric-append lw-complex-geometric-sum
                                  lw-complex-power-correlation lw-complex-signed-power-compose
                                  lw-complex-conjugate-power))))))

(defthm lw-complex-geometric-conjugate
  (implies (and (lw-complexp point) (natp count))
           (equal (lw-complex-geometric-sum (lw-complex-conjugate point) count)
                  (lw-complex-conjugate (lw-complex-geometric-sum point count))))
  :hints (("Goal" :induct (lw-complex-geometric-sum point count)
                  :in-theory (enable lw-complex-geometric-sum lw-complex-conjugate))))

(local (in-theory
        (disable lw-cauchy-orbit-rotation lw-cauchy-orbit-step lw-cauchy-orbit-gap
                 lw-phase-rotation lw-phase-denominator lw-complex-geometric-sum
                 lw-complex-correlation-sum lw-complex-signed-power)))

(defthm lw-cauchy-orbit-norm-one
  (implies (natp degree)
           (equal (lw-complex-norm-square (lw-cauchy-orbit-rotation degree)) 1))
  :hints (("Goal" :use (lw-cauchy-orbit-step-adequate)
                  :in-theory (enable lw-cauchy-orbit-rotation))))

(defthm lw-cauchy-moment-as-correlation
  (implies (and (natp degree) (natp left) (natp right) (posp count))
           (equal (lw-complex-scale
                   (/ count)
                   (lw-complex-correlation-sum (lw-cauchy-orbit-rotation degree) left right count))
                  (lw-cauchy-orbit-moment degree (- left right) count)))
  :hints (("Goal" :use (lw-cauchy-orbit-data lw-cauchy-orbit-norm-one)
                  :in-theory (e/d (lw-cauchy-orbit-moment lw-complex-geometric-average
                                   lw-complex-signed-power)
                                  (lw-complex-conjugate-power)))))

(local (in-theory (disable lw-cauchy-orbit-moment lw-complex-geometric-average)))

(defun lw-complex-coefficientsp (coefficients)
  (if (consp coefficients)
      (and (lw-complexp (car coefficients)) (lw-complex-coefficientsp (cdr coefficients)))
    (equal coefficients nil)))

(defun lw-complex-polynomial (coefficients point offset)
  (if (endp coefficients) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul (car coefficients) (lw-complex-power point offset))
     (lw-complex-polynomial (cdr coefficients) point (+ 1 offset)))))

(defthm lw-complex-polynomial-rational
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp offset))
           (lw-complexp (lw-complex-polynomial coefficients point offset))))

(defun lw-cauchy-evaluation-sum (coefficients point target offset count)
  (if (zp count) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (lw-complex-polynomial coefficients (lw-complex-power point (- count 1)) offset)
      (lw-complex-conjugate
       (lw-complex-power (lw-complex-power point (- count 1)) target)))
     (lw-cauchy-evaluation-sum coefficients point target offset (- count 1)))))

(defthm lw-cauchy-evaluation-sum-rational
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                (natp target) (natp offset) (natp count))
           (lw-complexp (lw-cauchy-evaluation-sum coefficients point target offset count))))

(local (in-theory (disable lw-complex-coefficientsp lw-complex-polynomial lw-cauchy-evaluation-sum)))

(defthm lw-cauchy-evaluation-sum-empty
  (implies (and (lw-complexp point) (natp target) (natp offset) (natp count))
           (equal (lw-cauchy-evaluation-sum nil point target offset count) (cons 0 0)))
  :hints (("Goal" :induct (lw-cp-countdown count)
                  :in-theory (enable lw-cauchy-evaluation-sum lw-complex-polynomial))))

(defthm lw-cauchy-evaluation-sum-first
  (implies (and (consp coefficients) (lw-complex-coefficientsp coefficients)
                (lw-complexp point) (natp target) (natp offset) (natp count))
           (equal (lw-cauchy-evaluation-sum coefficients point target offset count)
                  (lw-complex-add
                   (lw-complex-mul
                    (car coefficients) (lw-complex-correlation-sum point offset target count))
                   (lw-cauchy-evaluation-sum (cdr coefficients) point target (+ 1 offset) count))))
  :hints (("Goal" :induct (lw-cp-countdown count)
                  :in-theory (enable lw-cauchy-evaluation-sum lw-complex-polynomial
                                     lw-complex-correlation-sum lw-complex-coefficientsp))))

(defun lw-cauchy-correlation-expansion (coefficients point target offset count)
  (if (endp coefficients) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (car coefficients) (lw-complex-correlation-sum point offset target count))
     (lw-cauchy-correlation-expansion (cdr coefficients) point target (+ 1 offset) count))))

(defthm lw-cauchy-correlation-expansion-rational
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                (natp target) (natp offset) (natp count))
           (lw-complexp (lw-cauchy-correlation-expansion coefficients point target offset count)))
  :hints (("Goal" :in-theory (enable lw-complex-coefficientsp))))

(defthm lw-cauchy-evaluation-sum-expansion
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                (natp target) (natp offset) (natp count))
           (equal (lw-cauchy-evaluation-sum coefficients point target offset count)
                  (lw-cauchy-correlation-expansion coefficients point target offset count)))
  :hints (("Goal" :induct (lw-cauchy-correlation-expansion coefficients point target offset count)
                  :in-theory (enable lw-complex-coefficientsp))))

(defun lw-cauchy-moment-expansion (coefficients degree target offset count)
  (if (endp coefficients) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (car coefficients) (lw-cauchy-orbit-moment degree (- offset target) count))
     (lw-cauchy-moment-expansion (cdr coefficients) degree target (+ 1 offset) count))))

(defthm lw-cauchy-moment-expansion-rational
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (natp target) (natp offset) (posp count))
           (lw-complexp (lw-cauchy-moment-expansion coefficients degree target offset count)))
  :hints (("Goal" :in-theory (enable lw-complex-coefficientsp lw-cauchy-orbit-moment
                                     lw-complex-geometric-average))))

(defthm lw-cauchy-scaled-expansion
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (natp target) (natp offset) (posp count))
           (equal (lw-complex-scale
                   (/ count)
                   (lw-cauchy-correlation-expansion coefficients (lw-cauchy-orbit-rotation degree)
                                                    target offset count))
                  (lw-cauchy-moment-expansion coefficients degree target offset count)))
  :hints (("Goal" :induct (lw-cauchy-moment-expansion coefficients degree target offset count)
                  :in-theory (e/d (lw-complex-coefficientsp)
                                  (lw-complex-correlation-sum-geometric
                                   lw-complex-mul-commutative)))))

(defun lw-cauchy-polynomial-average (coefficients degree target count)
  (lw-complex-scale
   (/ count)
   (lw-cauchy-evaluation-sum coefficients (lw-cauchy-orbit-rotation degree) target 0 count)))

(defthm lw-cauchy-polynomial-average-moments
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (natp target) (posp count))
           (equal (lw-cauchy-polynomial-average coefficients degree target count)
                  (lw-cauchy-moment-expansion coefficients degree target 0 count)))
  :hints (("Goal" :use (lw-cauchy-orbit-data))))

; L1 coefficient mass gives a rational bound without square roots.
(defun lw-complex-l1 (point) (+ (abs (car point)) (abs (cdr point))))

(defthm lw-complex-l1-bound
  (implies (lw-complexp point)
           (and (rationalp (lw-complex-l1 point)) (<= 0 (lw-complex-l1 point))
                (lw-complex-diskp point (lw-complex-l1 point))))
  :hints (("Goal" :cases ((<= 0 (car point)) (<= 0 (cdr point)))
                  :in-theory (enable lw-complexp lw-complex-diskp lw-diskp)
                  :nonlinearp t)))

(local (defthm lw-cp-l1-nonnegative
         (implies (lw-complexp point) (<= 0 (lw-complex-l1 point)))
         :hints (("Goal" :use (lw-complex-l1-bound)
                         :in-theory (disable lw-complex-l1 lw-complex-l1-bound)))
         :rule-classes :linear))

(defun lw-complex-coefficient-mass (coefficients)
  (if (endp coefficients) 0
    (+ (lw-complex-l1 (car coefficients))
       (lw-complex-coefficient-mass (cdr coefficients)))))

(defthm lw-complex-coefficient-mass-valid
  (implies (lw-complex-coefficientsp coefficients)
           (and (rationalp (lw-complex-coefficient-mass coefficients))
                (<= 0 (lw-complex-coefficient-mass coefficients))))
  :hints (("Goal" :in-theory (e/d (lw-complex-coefficientsp) (lw-complex-l1)))))

(defun lw-complex-coefficient-at (coefficients target offset)
  (if (endp coefficients) (cons 0 0)
    (lw-complex-add
     (if (equal offset target) (car coefficients) (cons 0 0))
     (lw-complex-coefficient-at (cdr coefficients) target (+ 1 offset)))))

(defthm lw-complex-coefficient-at-rational
  (implies (and (lw-complex-coefficientsp coefficients) (natp target) (natp offset))
           (lw-complexp (lw-complex-coefficient-at coefficients target offset)))
  :hints (("Goal" :in-theory (enable lw-complex-coefficientsp))))

(defthm lw-complex-coefficient-at-below-offset
  (implies (and (lw-complex-coefficientsp coefficients) (natp target) (natp offset) (< target offset))
           (equal (lw-complex-coefficient-at coefficients target offset) (cons 0 0)))
  :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
                  :in-theory (enable lw-complex-coefficientsp))))

(defthm lw-complex-coefficient-at-nth
  (implies (and (lw-complex-coefficientsp coefficients) (natp target) (natp offset)
                (<= offset target) (< target (+ offset (len coefficients))))
           (equal (lw-complex-coefficient-at coefficients target offset)
                  (nth (- target offset) coefficients)))
  :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
                  :in-theory (enable lw-complex-coefficientsp nth))))

(defthm lw-complex-sub-add
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
           (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                  (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-add))))

(defthm lw-complex-sub-zero
  (implies (lw-complexp point)
           (and (equal (lw-complex-sub point (cons 0 0)) point)
                (equal (lw-complex-sub point point) (cons 0 0))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub))))

(defthm lw-complex-zero-disk
  (implies (and (rationalp radius) (<= 0 radius))
           (lw-complex-diskp (cons 0 0) radius))
  :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)
                  :nonlinearp t)))

(defun lw-cauchy-residual-expansion (coefficients degree target offset count)
  (if (endp coefficients) (cons 0 0)
    (lw-complex-add
     (lw-complex-mul
      (car coefficients)
      (lw-complex-sub (lw-cauchy-orbit-moment degree (- offset target) count)
                       (if (equal offset target) (cons 1 0) (cons 0 0))))
     (lw-cauchy-residual-expansion (cdr coefficients) degree target (+ 1 offset) count))))

(local (in-theory
        (disable lw-complex-l1 lw-complex-coefficient-at lw-cauchy-moment-expansion
                 lw-cauchy-correlation-expansion lw-cauchy-polynomial-average)))

(defthm lw-cauchy-moment-residual-bound
  (implies (and (natp degree) (natp target) (<= target degree) (natp offset) (<= offset degree)
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-cauchy-orbit-moment degree (- offset target) (lw-cauchy-moment-count degree error))
             (if (equal offset target) (cons 1 0) (cons 0 0))) error))
  :hints (("Goal" :cases ((equal offset target))
                  :use ((:instance lw-cauchy-computed-signed-moment-bound
                            (frequency (- offset target)))))))

(defthm lw-cauchy-residual-expansion-bound
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (natp target) (<= target degree) (natp offset)
                (<= (+ offset (len coefficients)) (+ 1 degree))
                (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-cauchy-residual-expansion coefficients degree target offset
                                          (lw-cauchy-moment-count degree error))
            (* (lw-complex-coefficient-mass coefficients) error)))
  :hints (("Goal" :induct (lw-cauchy-residual-expansion coefficients degree target offset
                                                       (lw-cauchy-moment-count degree error))
                  :in-theory (enable lw-complex-coefficientsp))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cauchy-moment-residual-bound)
                        (:instance lw-complex-l1-bound (point (car coefficients)))
                        (:instance lw-complex-mul-disk
                          (left (car coefficients)) (radius (lw-complex-l1 (car coefficients)))
                          (right (lw-complex-sub
                                   (lw-cauchy-orbit-moment degree (- offset target)
                                                           (lw-cauchy-moment-count degree error))
                                   (if (equal offset target) (cons 1 0) (cons 0 0))))
                          (other-radius error))
                        (:instance lw-complex-add-disk
                          (left (lw-complex-mul
                                 (car coefficients)
                                 (lw-complex-sub
                                  (lw-cauchy-orbit-moment degree (- offset target)
                                                          (lw-cauchy-moment-count degree error))
                                  (if (equal offset target) (cons 1 0) (cons 0 0)))))
                          (radius (* (lw-complex-l1 (car coefficients)) error))
                          (right (lw-cauchy-residual-expansion
                                  (cdr coefficients) degree target (+ 1 offset)
                                  (lw-cauchy-moment-count degree error)))
                          (other-radius (* (lw-complex-coefficient-mass (cdr coefficients)) error))))
                 :in-theory (disable lw-cauchy-moment-residual-bound lw-complex-mul-disk
                                     lw-complex-add-disk lw-cauchy-residual-expansion
                                     lw-complex-l1-bound)))))

(defthm lw-cauchy-orbit-moment-rational
  (implies (and (natp degree) (integerp frequency) (posp count))
           (lw-complexp (lw-cauchy-orbit-moment degree frequency count)))
  :hints (("Goal" :in-theory (enable lw-cauchy-orbit-moment lw-complex-geometric-average))))

(defthm lw-complex-sub-add-first
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-sub (lw-complex-add a b) c)
                  (lw-complex-add a (lw-complex-sub b c))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-add))))

(defthm lw-complex-sub-add-cancel
  (implies (and (lw-complexp a) (lw-complexp b))
           (and (equal (lw-complex-sub (lw-complex-add a b) a) b)
                (equal (lw-complex-sub (lw-complex-add a b) b) a)))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-add))))

(defthm lw-cauchy-residual-expansion-identity
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (natp target) (natp offset) (posp count))
           (equal (lw-complex-sub
                   (lw-cauchy-moment-expansion coefficients degree target offset count)
                   (lw-complex-coefficient-at coefficients target offset))
                  (lw-cauchy-residual-expansion coefficients degree target offset count)))
  :hints (("Goal" :induct (lw-cauchy-residual-expansion coefficients degree target offset count)
                  :in-theory (e/d (lw-complex-coefficientsp lw-cauchy-moment-expansion
                                   lw-complex-coefficient-at)
                                  (lw-complex-add-commutative lw-complex-add-left-commutes)))))
