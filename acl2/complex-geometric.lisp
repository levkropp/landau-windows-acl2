(in-package "ACL2")

(include-book "complex-bounds")
(include-book "rpow-continuity")

; Exact rational complex inverses and finite resolvent expansions. These
; supply arithmetic operations for the pole and finite Cauchy arguments.

(local (defthm lw-cg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cg-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cg-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-cg-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-cg-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-cg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-cg-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cg-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cg-square-nonnegative
         (implies (rationalp a) (<= 0 (* a a)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-ring-rational
  (implies (and (lw-complexp left) (lw-complexp right))
           (and (lw-complexp (lw-complex-add left right))
                (lw-complexp (lw-complex-sub left right))
                (lw-complexp (lw-complex-mul left right)))))
(local (defthm lw-cg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cg-left-commutes)))))

(defun lw-complex-conjugate (point) (cons (car point) (- (cdr point))))
(defun lw-complex-norm-square (point)
  (+ (* (car point) (car point)) (* (cdr point) (cdr point))))

(defthm lw-complex-conjugate-rational
  (implies (lw-complexp point) (lw-complexp (lw-complex-conjugate point))))

(defthm lw-complex-norm-square-valid
  (implies (lw-complexp point)
           (and (rationalp (lw-complex-norm-square point)) (<= 0 (lw-complex-norm-square point))))
  :hints (("Goal" :use ((:instance lw-cg-square-nonnegative (a (car point)))
                        (:instance lw-cg-square-nonnegative (a (cdr point)))))))

(defthm lw-complex-norm-square-positive
  (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
           (< 0 (lw-complex-norm-square point)))
  :hints (("Goal" :use ((:instance lw-cg-square-nonnegative (a (car point)))
                        (:instance lw-cg-square-nonnegative (a (cdr point))))
                  :cases ((equal (car point) 0)) :nonlinearp t)))

(defthm lw-complex-norm-square-product
  (implies (and (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-norm-square (lw-complex-mul left right))
                  (* (lw-complex-norm-square left) (lw-complex-norm-square right)))))

(defthm lw-complex-mul-commutative
  (implies (and (lw-complexp left) (lw-complexp right))
           (equal (lw-complex-mul left right) (lw-complex-mul right left))))

(defthm lw-complex-mul-distribute
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-mul a (lw-complex-add b c))
                  (lw-complex-add (lw-complex-mul a b) (lw-complex-mul a c)))))

(defthm lw-complex-mul-subtract
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
           (equal (lw-complex-mul a (lw-complex-sub b c))
                  (lw-complex-sub (lw-complex-mul a b) (lw-complex-mul a c)))))

(defun lw-complex-reciprocal (point)
  (lw-complex-scale (/ (lw-complex-norm-square point)) (lw-complex-conjugate point)))

(defthm lw-complex-reciprocal-rational
  (implies (lw-complexp point) (lw-complexp (lw-complex-reciprocal point))))

(defthm lw-complex-reciprocal-inverse
  (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
           (and (equal (lw-complex-mul point (lw-complex-reciprocal point)) (cons 1 0))
                (equal (lw-complex-mul (lw-complex-reciprocal point) point) (cons 1 0))))
  :hints (("Goal" :use (lw-complex-norm-square-positive
                        (:instance lw-cg-inverse-factor (divisor (lw-complex-norm-square point)) (coefficient 1)))
                  :in-theory (disable lw-cg-inverse-factor) :nonlinearp nil)))

(defthm lw-complex-norm-square-reciprocal
  (implies (and (lw-complexp point) (not (equal point (cons 0 0))))
           (equal (lw-complex-norm-square (lw-complex-reciprocal point)) (/ (lw-complex-norm-square point))))
  :hints (("Goal" :use (lw-complex-norm-square-positive
                        (:instance lw-cg-inverse-factor
                          (divisor (lw-complex-norm-square point)) (coefficient (/ (lw-complex-norm-square point)))))
                  :in-theory (disable lw-cg-inverse-factor) :nonlinearp nil)))

(defthm lw-complex-disk-norm-square
  (equal (lw-complex-diskp point radius)
         (and (lw-complexp point) (rationalp radius) (<= 0 radius)
              (<= (lw-complex-norm-square point) (* radius radius))))
  :rule-classes nil)

(defthm lw-complex-disk-coordinates
  (implies (lw-complex-diskp point radius)
           (and (<= (abs (car point)) radius) (<= (abs (cdr point)) radius)))
  :hints (("Goal" :use ((:instance lw-cg-square-nonnegative (a (car point)))
                        (:instance lw-cg-square-nonnegative (a (cdr point))))
                  :cases ((<= 0 (car point)) (<= 0 (cdr point))) :nonlinearp t)))

(defthm lw-complex-conjugate-disk
  (implies (lw-complex-diskp point radius) (lw-complex-diskp (lw-complex-conjugate point) radius)))

(local (defthm lw-cg-cancel-equality
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (equal (* factor a) (* factor b))) (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cg-inverse-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
                  (equal (/ (* a b)) (* (/ a) (/ b))))
         :hints (("Goal" :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
                              (:instance inverse-of-* (x (* a b)))
                              (:instance lw-cg-cancel-equality
                                (factor (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))
(local (defthm lw-cg-positive-square
         (implies (and (rationalp a) (< 0 a)) (< 0 (* a a)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (in-theory (disable lw-complexp lw-complex-norm-square lw-complex-conjugate lw-complex-reciprocal
                           lw-complex-norm-square-reciprocal lw-complex-diskp lw-diskp lw-complex-add lw-complex-sub
                           lw-complex-mul lw-complex-scale lw-complex-power lw-rational-power
                           lw-complex-disk-enlarge lw-disk-enlarge lw-complex-mul-disk lw-reciprocal-antitone)))

(defthm lw-complex-reciprocal-disk-bound
  (implies (and (lw-complexp point) (rationalp lower) (< 0 lower)
                (<= (* lower lower) (lw-complex-norm-square point)))
           (lw-complex-diskp (lw-complex-reciprocal point) (/ lower)))
  :hints (("Goal" :use ((:instance lw-complex-disk-norm-square (point (lw-complex-reciprocal point)) (radius (/ lower)))
                        (:instance lw-complex-norm-square-reciprocal)
                        (:instance lw-cg-inverse-product (a lower) (b lower))
                        (:instance lw-cg-positive-square (a lower))
                        (:instance lw-reciprocal-antitone (left (* lower lower)) (right (lw-complex-norm-square point))))
                  :cases ((equal point (cons 0 0))) :nonlinearp nil)))

(local (defthm lw-cg-power-zero
         (implies (zp index) (equal (lw-complex-power point index) (cons 1 0)))
         :hints (("Goal" :in-theory (enable lw-complex-power)))))
(local (defthm lw-cg-rational-power-zero
         (implies (zp index) (equal (lw-rational-power radius index) 1))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))

(defthm lw-complex-power-disk
  (implies (and (lw-complex-diskp point radius) (natp index))
           (lw-complex-diskp (lw-complex-power point index) (lw-rational-power radius index)))
  :hints (("Goal" :induct (lw-complex-power point index)
                  :in-theory (enable (:induction lw-complex-power)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-mul-disk (left point) (right (lw-complex-power point (- index 1)))
                         (other-radius (lw-rational-power radius (- index 1)))))
                 :expand ((lw-complex-power point index) (lw-rational-power radius index))
                 :do-not-induct t))))

(defun lw-complex-geometric-sum (point count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) (cons 0 0)
    (lw-complex-add (cons 1 0) (lw-complex-mul point (lw-complex-geometric-sum point (- count 1))))))

(defthm lw-complex-geometric-sum-rational
  (implies (lw-complexp point) (lw-complexp (lw-complex-geometric-sum point count))))

(defthm lw-complex-mul-zero
  (implies (lw-complexp point)
           (and (equal (lw-complex-mul point (cons 0 0)) (cons 0 0))
                (equal (lw-complex-mul (cons 0 0) point) (cons 0 0))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-mul))))

(local (defthm lw-cg-equal-mul
         (implies (equal a b) (equal (lw-complex-mul point a) (lw-complex-mul point b)))
         :rule-classes nil))

(local (defthm lw-cg-geometric-step
         (implies (and (lw-complexp point) (lw-complexp previous) (lw-complexp power)
                       (equal (lw-complex-mul (lw-complex-sub (cons 1 0) point) previous)
                              (lw-complex-sub (cons 1 0) power)))
                  (equal (lw-complex-mul (lw-complex-sub (cons 1 0) point)
                                         (lw-complex-add (cons 1 0) (lw-complex-mul point previous)))
                         (lw-complex-sub (cons 1 0) (lw-complex-mul point power))))
         :hints (("Goal" :use ((:instance lw-cg-equal-mul
                                (a (lw-complex-mul (lw-complex-sub (cons 1 0) point) previous))
                                (b (lw-complex-sub (cons 1 0) power))))
                         :in-theory (enable lw-complexp lw-complex-sub lw-complex-add lw-complex-mul) :nonlinearp nil))
         :rule-classes nil))

(defthm lw-complex-geometric-telescope
  (implies (and (lw-complexp point) (natp count))
           (equal (lw-complex-mul (lw-complex-sub (cons 1 0) point) (lw-complex-geometric-sum point count))
                  (lw-complex-sub (cons 1 0) (lw-complex-power point count))))
  :hints (("Goal" :induct (lw-complex-geometric-sum point count))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cg-geometric-step (previous (lw-complex-geometric-sum point (- count 1))) (power (lw-complex-power point (- count 1)))))
                 :expand ((lw-complex-power point count))
                 :do-not-induct t))))

(local (defthm lw-cg-one-minus-radius
         (implies (and (rationalp x) (rationalp y) (rationalp radius) (<= 0 radius) (< radius 1)
                       (<= (+ (* x x) (* y y)) (* radius radius)))
                  (<= (* (- 1 radius) (- 1 radius)) (+ (* (- 1 x) (- 1 x)) (* y y))))
         :hints (("Goal" :use ((:instance lw-cg-square-nonnegative (a y))
                              (:instance lw-cg-square-nonnegative (a (- x radius)))
                              (:instance lw-cg-nonnegative-product (a (- 1 radius)) (b (- radius x))))
                         :cases ((<= x radius)) :nonlinearp t))
         :rule-classes nil))

(defthm lw-complex-one-minus-norm-lower
  (implies (and (lw-complex-diskp point radius) (< radius 1))
           (<= (* (- 1 radius) (- 1 radius))
               (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
  :hints (("Goal" :use ((:instance lw-cg-one-minus-radius (x (car point)) (y (cdr point))))
                  :in-theory (enable lw-complex-diskp lw-complexp lw-diskp lw-complex-sub lw-complex-norm-square))))

(local (in-theory (disable lw-complex-one-minus-norm-lower lw-complex-reciprocal-disk-bound lw-complex-mul-commutative)))

(defthm lw-complex-resolvent-bound
  (implies (and (lw-complex-diskp point radius) (< radius 1))
           (lw-complex-diskp (lw-complex-reciprocal (lw-complex-sub (cons 1 0) point)) (/ (- 1 radius))))
  :hints (("Goal" :use (lw-complex-one-minus-norm-lower
                        (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-sub (cons 1 0) point)) (lower (- 1 radius)))))))

(defthm lw-complex-disk-excludes-one
  (implies (and (lw-complex-diskp point radius) (< radius 1)) (not (equal point (cons 1 0))))
  :hints (("Goal" :use (lw-complex-one-minus-norm-lower (:instance lw-cg-positive-square (a (- 1 radius))))
                  :cases ((equal point (cons 1 0))))))

(defthm lw-complex-one-minus-nonzero
  (implies (and (lw-complexp point) (not (equal point (cons 1 0))))
           (not (equal (lw-complex-sub (cons 1 0) point) (cons 0 0))))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub))))

(defthm lw-complex-reciprocal-cancel-product
  (implies (and (lw-complexp a) (lw-complexp b) (not (equal a (cons 0 0))))
           (and (equal (lw-complex-mul (lw-complex-reciprocal a) (lw-complex-mul a b)) b)
                (equal (lw-complex-mul a (lw-complex-mul (lw-complex-reciprocal a) b)) b)))
  :hints (("Goal" :use ((:instance lw-complex-mul-associative (left (lw-complex-reciprocal a)) (middle a) (right b))
                        (:instance lw-complex-mul-associative (left a) (middle (lw-complex-reciprocal a)) (right b)))
                  :in-theory (disable lw-complex-mul-associative))))

(local (in-theory (disable lw-complex-geometric-telescope)))

(defthm lw-complex-linear-solve
  (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c)
                (not (equal a (cons 0 0))) (equal (lw-complex-mul a b) c))
           (equal b (lw-complex-mul (lw-complex-reciprocal a) c)))
  :hints (("Goal" :use (lw-complex-reciprocal-cancel-product)
                  :in-theory (disable lw-complex-reciprocal-cancel-product)))
  :rule-classes nil)

(defthm lw-complex-subtract-cancel
  (implies (and (lw-complexp a) (lw-complexp b))
           (equal (lw-complex-sub a (lw-complex-sub a b)) b))
  :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub))))

(defthm lw-complex-geometric-remainder-identity
  (implies (and (lw-complexp point) (not (equal point (cons 1 0))) (natp count))
           (equal (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (cons 1 0) point)) (lw-complex-geometric-sum point count))
                  (lw-complex-mul (lw-complex-reciprocal (lw-complex-sub (cons 1 0) point)) (lw-complex-power point count))))
  :hints (("Goal" :use (lw-complex-geometric-telescope
                        (:instance lw-complex-linear-solve
                          (a (lw-complex-sub (cons 1 0) point)) (b (lw-complex-geometric-sum point count))
                          (c (lw-complex-sub (cons 1 0) (lw-complex-power point count)))))
                  :in-theory (disable lw-complex-geometric-sum) :do-not-induct t)))

(local (in-theory (disable lw-complex-geometric-remainder-identity lw-complex-resolvent-bound lw-complex-power-disk
                           lw-complex-geometric-sum)))

(defthm lw-complex-geometric-remainder-bound
  (implies (and (lw-complex-diskp point radius) (< radius 1) (natp count))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (cons 1 0) point)) (lw-complex-geometric-sum point count))
            (* (/ (- 1 radius)) (lw-rational-power radius count))))
  :hints (("Goal" :use (lw-complex-geometric-remainder-identity lw-complex-resolvent-bound (:instance lw-complex-power-disk (index count))
                        (:instance lw-complex-mul-disk
                          (left (lw-complex-reciprocal (lw-complex-sub (cons 1 0) point))) (radius (/ (- 1 radius)))
                          (right (lw-complex-power point count)) (other-radius (lw-rational-power radius count)))))))

(defthm lw-complex-norm-lower-nonzero
  (implies (and (lw-complexp point) (rationalp lower) (< 0 lower)
                (<= (* lower lower) (lw-complex-norm-square point)))
           (not (equal point (cons 0 0))))
  :hints (("Goal" :use ((:instance lw-cg-positive-square (a lower))) :cases ((equal point (cons 0 0))))))

(local (defthm lw-cg-sub-add-negative
         (implies (and (lw-complexp left) (lw-complexp right))
                  (equal (lw-complex-sub left right) (lw-complex-add left (lw-complex-scale -1 right))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-add lw-complex-scale)))))

(defthm lw-complex-sub-disk
  (implies (and (lw-complex-diskp left radius) (lw-complex-diskp right other-radius))
           (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
  :hints (("Goal" :use ((:instance lw-complex-scale-disk (factor -1) (point right) (radius other-radius))
                        (:instance lw-complex-add-disk (right (lw-complex-scale -1 right))))
                  :in-theory (disable lw-complex-scale-disk lw-complex-add-disk))))

(local (in-theory (disable lw-complex-sub-disk lw-complex-unit-power)))

(defthm lw-complex-geometric-unit-sum-bound
  (implies (and (lw-complex-diskp point 1) (natp count) (rationalp lower) (< 0 lower)
                (<= (* lower lower) (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
           (lw-complex-diskp (lw-complex-geometric-sum point count) (/ 2 lower)))
  :hints (("Goal"
           :use (lw-complex-geometric-telescope
                 (:instance lw-complex-linear-solve (a (lw-complex-sub (cons 1 0) point))
                   (b (lw-complex-geometric-sum point count)) (c (lw-complex-sub (cons 1 0) (lw-complex-power point count))))
                 (:instance lw-complex-norm-lower-nonzero (point (lw-complex-sub (cons 1 0) point)))
                 (:instance lw-complex-reciprocal-disk-bound (point (lw-complex-sub (cons 1 0) point)))
                 (:instance lw-complex-unit-power (index count))
                 (:instance lw-complex-sub-disk (left (cons 1 0)) (radius 1) (right (lw-complex-power point count)) (other-radius 1))
                 (:instance lw-complex-mul-disk
                   (left (lw-complex-reciprocal (lw-complex-sub (cons 1 0) point))) (radius (/ lower))
                   (right (lw-complex-sub (cons 1 0) (lw-complex-power point count))) (other-radius 2))))))

(defun lw-complex-geometric-average (point count)
  (lw-complex-scale (/ count) (lw-complex-geometric-sum point count)))

(local (in-theory (disable lw-complex-geometric-unit-sum-bound)))

(defthm lw-complex-geometric-average-bound
  (implies (and (lw-complex-diskp point 1) (posp count) (rationalp lower) (< 0 lower)
                (<= (* lower lower) (lw-complex-norm-square (lw-complex-sub (cons 1 0) point))))
           (lw-complex-diskp (lw-complex-geometric-average point count) (* (/ count) (/ 2 lower))))
  :hints (("Goal" :use (lw-complex-geometric-unit-sum-bound
                        (:instance lw-complex-scale-disk (factor (/ count)) (point (lw-complex-geometric-sum point count)) (radius (/ 2 lower))))
                  :in-theory (disable lw-complex-scale-disk))))

(defthm lw-complex-norm-square-power
  (implies (and (lw-complexp point) (natp index))
           (equal (lw-complex-norm-square (lw-complex-power point index))
                  (lw-rational-power (lw-complex-norm-square point) index)))
  :hints (("Goal" :induct (lw-complex-power point index) :in-theory (enable (:induction lw-complex-power)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-norm-square-product (left point) (right (lw-complex-power point (- index 1)))))
                 :expand ((lw-complex-power point index) (lw-rational-power (lw-complex-norm-square point) index))
                 :in-theory (disable lw-complex-norm-square-product) :do-not-induct t))))
