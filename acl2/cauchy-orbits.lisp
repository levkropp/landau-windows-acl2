(in-package "ACL2")

(include-book "complex-geometric")
(include-book "phase-bounds")

; Rational near-identity rotations with a checked gap for every nonzero
; frequency up to the polynomial degree. Geometric averages then cancel
; those frequencies with a computed finite sampling count.
(local (in-theory
        (disable lw-phase-rotation lw-phase-denominator lw-phase-rotation-unit lw-phase-rotation-chord
                 lw-complex-power lw-complex-power-remainder lw-complex-power-remainder-identity
                 lw-complex-power-quadratic-bound lw-complex-disk-coordinates
                 lw-complexp lw-complex-diskp lw-complex-norm-square lw-complex-reciprocal lw-complex-conjugate
                 lw-complex-mul lw-complex-add lw-complex-sub lw-complex-scale
                 lw-quadratic-radius lw-complex-geometric-average lw-complex-geometric-average-bound)))

(local (defthm lw-co-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-co-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-co-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-co-zero-times (equal (* 0 a) 0)))
(local (defthm lw-co-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-co-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-co-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-co-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-co-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-co-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-cauchy-orbit-step (degree) (/ (* 2 (+ 1 (nfix degree)))))
(defun lw-cauchy-orbit-rotation (degree) (lw-phase-rotation (lw-cauchy-orbit-step degree)))
(defun lw-cauchy-orbit-gap (degree) (/ (lw-cauchy-orbit-step degree) 4))

(defthm lw-cauchy-orbit-step-adequate
  (implies (natp degree)
           (and (rationalp (lw-cauchy-orbit-step degree)) (< 0 (lw-cauchy-orbit-step degree))
                (<= (lw-cauchy-orbit-step degree) 1) (<= (* 2 degree (lw-cauchy-orbit-step degree)) 1)))
  :hints (("Goal" :use ((:instance lw-positive-division-bound (numerator 1) (divisor (* 2 (+ 1 degree))) (bound 1))
                        (:instance inverse-of-* (x (* 2 (+ 1 degree))))
                        (:instance lw-co-multiply-order (a (* 2 degree)) (b (* 2 (+ 1 degree))) (factor (/ (* 2 (+ 1 degree))))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil)))

(local (defthm lw-co-rotation-imaginary
         (implies (and (rationalp value) (<= 0 value) (<= value 1))
                  (<= (/ value 2) (cdr (lw-phase-rotation value))))
         :hints (("Goal" :use ((:instance lw-positive-division-lower-bound
                                (numerator (* 4 value)) (divisor (+ 4 (* value value))) (bound (/ value 2))))
                         :in-theory (enable lw-phase-rotation lw-phase-denominator lw-complex-scale) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-co-quadratic-margin
         (implies (and (rationalp value) (< 0 value) (posp index) (<= (* 2 index value) 1))
                  (<= (lw-quadratic-radius index value) (/ (* index value) 4)))
         :hints (("Goal" :use ((:instance lw-co-nonnegative-product (a value) (b value))
                              (:instance lw-co-nonnegative-product (a index) (b (* value value)))
                              (:instance lw-co-multiply-order (a (* 2 index value)) (b 1) (factor (/ (* index value) 4))))
                         :in-theory (enable lw-quadratic-radius) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-co-imaginary-from-remainder
         (implies (and (lw-complexp point) (lw-complexp power) (lw-complexp remainder)
                       (rationalp value) (< 0 value) (posp index) (rationalp radius)
                       (equal remainder (lw-complex-sub (lw-complex-sub power (cons 1 0))
                                                       (lw-complex-scale index (lw-complex-sub point (cons 1 0)))))
                       (<= (/ value 2) (cdr point)) (<= (abs (cdr remainder)) radius)
                       (<= radius (/ (* index value) 4)))
                  (<= (/ (* index value) 4) (cdr power)))
         :hints (("Goal" :use ((:instance lw-co-multiply-order (a (/ value 2)) (b (cdr point)) (factor index)))
                         :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))
         :rule-classes nil))

(defthm lw-cayley-power-imaginary-lower
  (implies (and (rationalp value) (< 0 value) (<= value 1) (posp index) (<= (* 2 index value) 1))
           (<= (/ (* index value) 4) (cdr (lw-complex-power (lw-phase-rotation value) index))))
  :hints (("Goal"
           :use (lw-co-rotation-imaginary lw-co-quadratic-margin lw-phase-rotation-unit lw-phase-rotation-chord
                 lw-phase-rotation-rational
                 (:instance lw-complex-power-rational (point (lw-phase-rotation value)))
                 (:instance lw-complex-power-quadratic-bound (point (lw-phase-rotation value)) (error value))
                 (:instance lw-complex-power-remainder-identity (point (lw-phase-rotation value)))
                 (:instance lw-complex-disk-coordinates
                   (point (lw-complex-power-remainder (lw-phase-rotation value) index)) (radius (lw-quadratic-radius index value)))
                 (:instance lw-co-imaginary-from-remainder
                   (point (lw-phase-rotation value)) (power (lw-complex-power (lw-phase-rotation value) index))
                   (remainder (lw-complex-power-remainder (lw-phase-rotation value) index)) (radius (lw-quadratic-radius index value)))))))

(local (in-theory (disable lw-cauchy-orbit-step lw-cauchy-orbit-rotation lw-cauchy-orbit-gap lw-cauchy-orbit-step-adequate
                           lw-cayley-power-imaginary-lower)))

(defthm lw-cauchy-orbit-power-imaginary
  (implies (and (natp degree) (posp index) (<= index degree))
           (<= (lw-cauchy-orbit-gap degree) (cdr (lw-complex-power (lw-cauchy-orbit-rotation degree) index))))
  :hints (("Goal" :use (lw-cauchy-orbit-step-adequate
                        (:instance lw-cayley-power-imaginary-lower (value (lw-cauchy-orbit-step degree)))
                        (:instance lw-co-multiply-order (a index) (b degree) (factor (* 2 (lw-cauchy-orbit-step degree))))
                        (:instance lw-co-multiply-order (a 1) (b index) (factor (/ (lw-cauchy-orbit-step degree) 4))))
                  :in-theory (enable lw-cauchy-orbit-gap lw-cauchy-orbit-rotation) :nonlinearp nil)))

(defthm lw-cauchy-orbit-data
  (implies (natp degree)
           (and (lw-complexp (lw-cauchy-orbit-rotation degree)) (lw-complex-diskp (lw-cauchy-orbit-rotation degree) 1)
                (rationalp (lw-cauchy-orbit-gap degree)) (< 0 (lw-cauchy-orbit-gap degree))))
  :hints (("Goal" :use (lw-cauchy-orbit-step-adequate
                        (:instance lw-phase-rotation-unit (value (lw-cauchy-orbit-step degree))))
                  :in-theory (enable lw-cauchy-orbit-rotation lw-cauchy-orbit-gap))))

(local (defthm lw-co-square-nonnegative
         (implies (rationalp a) (<= 0 (* a a))) :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-co-imaginary-norm-lower
         (implies (and (lw-complexp point) (rationalp lower) (<= 0 lower) (<= lower (cdr point)))
                  (<= (* lower lower) (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
         :hints (("Goal" :use ((:instance lw-co-square-nonnegative (a (- 1 (car point))))
                              (:instance lw-co-multiply-order (a lower) (b (cdr point)) (factor lower))
                              (:instance lw-co-multiply-order (a lower) (b (cdr point)) (factor (cdr point))))
                         :in-theory (enable lw-complexp lw-complex-sub lw-complex-norm-square)))
         :rule-classes nil))

(local (in-theory (disable lw-cauchy-orbit-data lw-cauchy-orbit-power-imaginary)))

(defthm lw-cauchy-orbit-power-separated
  (implies (and (natp degree) (posp index) (<= index degree))
           (<= (* (lw-cauchy-orbit-gap degree) (lw-cauchy-orbit-gap degree))
               (lw-complex-norm-square (lw-complex-sub (cons 1 0) (lw-complex-power (lw-cauchy-orbit-rotation degree) index)))))
  :hints (("Goal" :use (lw-cauchy-orbit-data lw-cauchy-orbit-power-imaginary
                        (:instance lw-co-imaginary-norm-lower (point (lw-complex-power (lw-cauchy-orbit-rotation degree) index)) (lower (lw-cauchy-orbit-gap degree)))))))

(local (in-theory (disable lw-cauchy-orbit-power-separated lw-complex-unit-power lw-complex-disk-enlarge lw-disk-enlarge)))

(defthm lw-cauchy-orbit-geometric-average
  (implies (and (natp degree) (posp index) (<= index degree) (posp count))
           (lw-complex-diskp (lw-complex-geometric-average (lw-complex-power (lw-cauchy-orbit-rotation degree) index) count)
                             (* (/ count) (/ 2 (lw-cauchy-orbit-gap degree)))))
  :hints (("Goal" :use (lw-cauchy-orbit-data lw-cauchy-orbit-power-separated
                        (:instance lw-complex-unit-power (point (lw-cauchy-orbit-rotation degree)))
                        (:instance lw-complex-geometric-average-bound (point (lw-complex-power (lw-cauchy-orbit-rotation degree) index)) (lower (lw-cauchy-orbit-gap degree)))))))

(local (in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket)))
(local (defthm lw-co-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-co-left-commutes)))))

(defun lw-cauchy-moment-count (degree error)
  (+ 1 (lw-ceiling-rational (/ (/ 2 (lw-cauchy-orbit-gap degree)) error))))

(defthm lw-cauchy-moment-count-natural
  (and (natp (lw-cauchy-moment-count degree error)) (< 0 (lw-cauchy-moment-count degree error)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-cauchy-moment-count-adequate
  (implies (and (natp degree) (rationalp error) (< 0 error))
           (<= (* (/ (lw-cauchy-moment-count degree error)) (/ 2 (lw-cauchy-orbit-gap degree))) error))
  :hints (("Goal" :use (lw-cauchy-orbit-data
                        (:instance lw-ceiling-rational-bracket (value (/ (/ 2 (lw-cauchy-orbit-gap degree)) error)))
                        (:instance lw-co-multiply-order
                          (a (/ (/ 2 (lw-cauchy-orbit-gap degree)) error)) (b (lw-cauchy-moment-count degree error)) (factor error))
                        (:instance lw-co-inverse-factor (divisor error) (coefficient (/ 2 (lw-cauchy-orbit-gap degree))))
                        (:instance lw-positive-division-bound (numerator (/ 2 (lw-cauchy-orbit-gap degree))) (divisor (lw-cauchy-moment-count degree error)) (bound error)))
                  :in-theory (disable lw-co-inverse-factor) :nonlinearp nil)))

(local (in-theory (disable lw-cauchy-moment-count lw-cauchy-moment-count-adequate lw-cauchy-orbit-geometric-average)))

(defthm lw-cauchy-computed-moment-bound
  (implies (and (natp degree) (posp index) (<= index degree) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-geometric-average (lw-complex-power (lw-cauchy-orbit-rotation degree) index) (lw-cauchy-moment-count degree error)) error))
  :hints (("Goal" :use (lw-cauchy-moment-count-adequate
                        (:instance lw-cauchy-orbit-geometric-average (count (lw-cauchy-moment-count degree error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-geometric-average (lw-complex-power (lw-cauchy-orbit-rotation degree) index) (lw-cauchy-moment-count degree error)))
                          (radius (* (/ (lw-cauchy-moment-count degree error)) (/ 2 (lw-cauchy-orbit-gap degree)))) (cap error))))))

(local (defthm lw-co-norm-cons
         (equal (lw-complex-norm-square (cons x y)) (+ (* x x) (* y y)))
         :hints (("Goal" :in-theory (enable lw-complex-norm-square)))))
(local (defthm lw-co-complex-cons
         (equal (lw-complexp (cons x y)) (and (rationalp x) (rationalp y)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))

(local (defthm lw-co-cayley-quotient
         (implies (rationalp value)
                  (equal (lw-phase-rotation value)
                         (lw-complex-mul (cons 2 value) (lw-complex-reciprocal (cons 2 (- value))))))
         :hints (("Goal" :in-theory (enable lw-phase-rotation lw-phase-denominator lw-complex-reciprocal
                                           lw-complex-norm-square lw-complex-conjugate lw-complex-scale lw-complex-mul)))))

(defthm lw-cayley-norm-square-one
  (implies (rationalp value) (equal (lw-complex-norm-square (lw-phase-rotation value)) 1))
  :hints (("Goal" :use (lw-phase-denominator-positive (:instance inverse-of-* (x (+ 4 (* value value)))))
                  :in-theory (e/d (lw-phase-denominator) (inverse-of-*)))))

(local (in-theory (disable lw-co-cayley-quotient)))

(defthm lw-cauchy-orbit-power-norm-one
  (implies (and (natp degree) (natp index))
           (equal (lw-complex-norm-square (lw-complex-power (lw-cauchy-orbit-rotation degree) index)) 1))
  :hints (("Goal" :use (lw-cauchy-orbit-step-adequate lw-cauchy-orbit-data)
                  :in-theory (enable lw-cauchy-orbit-rotation))))

(defun lw-cauchy-orbit-moment (degree frequency count)
  (if (< frequency 0)
      (lw-complex-conjugate (lw-complex-geometric-average (lw-complex-power (lw-cauchy-orbit-rotation degree) (nfix (- frequency))) count))
    (lw-complex-geometric-average (lw-complex-power (lw-cauchy-orbit-rotation degree) (nfix frequency)) count)))

(local (in-theory (disable lw-cauchy-computed-moment-bound lw-complex-conjugate lw-complex-conjugate-disk)))

(defthm lw-cauchy-computed-signed-moment-bound
  (implies (and (natp degree) (integerp frequency) (not (equal frequency 0)) (<= (abs frequency) degree)
                (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-cauchy-orbit-moment degree frequency (lw-cauchy-moment-count degree error)) error))
  :hints (("Goal" :use ((:instance lw-cauchy-computed-moment-bound (index (abs frequency)))
                        (:instance lw-complex-conjugate-disk
                          (point (lw-complex-geometric-average (lw-complex-power (lw-cauchy-orbit-rotation degree) (abs frequency)) (lw-cauchy-moment-count degree error))) (radius error))))))

(local (defthm lw-co-geometric-one
         (implies (natp count) (equal (lw-complex-geometric-sum (cons 1 0) count) (cons count 0)))
         :hints (("Goal" :induct (lw-complex-geometric-sum (cons 1 0) count)
                         :in-theory (enable lw-complex-geometric-sum lw-complex-add lw-complex-mul)))))

(defthm lw-cauchy-orbit-zero-moment
  (implies (posp count) (equal (lw-cauchy-orbit-moment degree 0 count) (cons 1 0)))
  :hints (("Goal" :expand ((lw-complex-power (lw-cauchy-orbit-rotation degree) 0))
                  :in-theory (enable lw-complex-geometric-average lw-complex-scale))))
