(in-package "ACL2")

(include-book "landau-bounds")

(defthm lw-rational-power-one
  (equal (lw-rational-power 1 exponent) 1))

(local (defthm lw-root-halved-width-add
         (implies (and (rationalp left) (rationalp right))
                  (equal (lw-halved-width (+ left right) steps)
                         (+ (lw-halved-width left steps) (lw-halved-width right steps))))))

(local (defthm lw-root-halved-width-negate
         (implies (rationalp width)
                  (equal (lw-halved-width (- width) steps)
                         (- (lw-halved-width width steps))))))

(defthm lw-rational-power-nonnegative
  (implies (and (rationalp base) (<= 0 base))
           (<= 0 (lw-rational-power base exponent)))
  :hints (("Goal" :induct (lw-rational-power base exponent) :nonlinearp t)))

(defthm lw-rational-power-monotone-base
  (implies (and (rationalp left) (rationalp right)
                (<= 0 left) (<= left right))
           (<= (lw-rational-power left exponent) (lw-rational-power right exponent)))
  :hints (("Goal" :induct (lw-rational-power left exponent) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-rational-power-nonnegative
                         (base left) (exponent (- exponent 1)))
                        (:instance lw-rational-power-nonnegative
                         (base right) (exponent (- exponent 1))))
                 :in-theory (disable lw-rational-power lw-rational-power-nonnegative)
                 :nonlinearp t))))

(defthm lw-rational-power-monotone-exponent
  (implies (and (rationalp base) (<= 1 base)
                (natp small) (natp large) (<= small large))
           (<= (lw-rational-power base small) (lw-rational-power base large)))
  :hints (("Goal" :induct (lw-rational-power base large) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-rational-power-at-least-one
                         (exponent (- large 1))))
                 :in-theory (disable lw-rational-power lw-rational-power-at-least-one)
                 :nonlinearp t))))

(defun lw-root-bracket (target degree lower upper steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons lower upper)
    (let ((middle (/ (+ lower upper) 2)))
      (if (<= (lw-rational-power middle degree) target)
          (lw-root-bracket target degree middle upper (- steps 1))
        (lw-root-bracket target degree lower middle (- steps 1))))))

(defthm lw-root-bracket-sound
  (implies (and (rationalp target) (posp degree)
                (rationalp lower) (rationalp upper) (<= 0 lower) (<= lower upper)
                (<= (lw-rational-power lower degree) target)
                (<= target (lw-rational-power upper degree)))
           (let ((bounds (lw-root-bracket target degree lower upper steps)))
             (and (lw-intervalp bounds)
                  (<= lower (car bounds)) (<= (cdr bounds) upper)
                  (<= (lw-rational-power (car bounds) degree) target)
                  (<= target (lw-rational-power (cdr bounds) degree)))))
  :hints (("Goal" :induct (lw-root-bracket target degree lower upper steps)
                  :in-theory (disable lw-rational-power) :nonlinearp t)))

(defthm lw-root-bracket-width
  (implies (and (rationalp lower) (rationalp upper))
           (equal (- (cdr (lw-root-bracket target degree lower upper steps))
                     (car (lw-root-bracket target degree lower upper steps)))
                  (lw-halved-width (- upper lower) steps)))
  :hints (("Goal" :induct (lw-root-bracket target degree lower upper steps)
                  :in-theory (disable lw-rational-power) :nonlinearp t)))

(defun lw-rpow-bounds (value numerator denominator epsilon)
  (let ((steps (lw-halving-depth (- value 1) epsilon
                                  (lw-precision-fuel (- value 1) epsilon))))
    (lw-root-bracket (lw-rational-power value numerator) denominator 1 value steps)))

(defthm lw-rpow-bounds-sound
  (implies (and (rationalp value) (<= 1 value)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp epsilon) (< 0 epsilon))
           (let ((bounds (lw-rpow-bounds value numerator denominator epsilon)))
             (and (lw-intervalp bounds)
                  (<= 1 (car bounds)) (<= (cdr bounds) value)
                  (<= (lw-rational-power (car bounds) denominator)
                      (lw-rational-power value numerator))
                  (<= (lw-rational-power value numerator)
                      (lw-rational-power (cdr bounds) denominator)))))
  :hints (("Goal" :use ((:instance lw-rational-power-at-least-one
                          (base value) (exponent numerator))
                        (:instance lw-rational-power-monotone-exponent
                          (base value) (small numerator) (large denominator))
                        (:instance lw-root-bracket-sound
                          (target (lw-rational-power value numerator))
                          (degree denominator) (lower 1) (upper value)
                          (steps (lw-halving-depth (- value 1) epsilon
                                   (lw-precision-fuel (- value 1) epsilon)))))
                  :in-theory (disable lw-root-bracket lw-root-bracket-sound
                                      lw-rational-power-monotone-exponent lw-rational-power
                                      lw-rational-power-at-least-one
                                      lw-halving-depth lw-precision-fuel))))

(defthm lw-rpow-bounds-width
  (implies (and (rationalp value) (<= 1 value)
                (rationalp epsilon) (< 0 epsilon))
           (<= (- (cdr (lw-rpow-bounds value numerator denominator epsilon))
                  (car (lw-rpow-bounds value numerator denominator epsilon))) epsilon))
  :hints (("Goal" :use ((:instance lw-halving-depth-adequate
                          (width (- value 1)) (fuel (lw-precision-fuel (- value 1) epsilon)))
                        (:instance lw-precision-fuel-adequate (width (- value 1))))
                  :in-theory (disable lw-root-bracket lw-halving-depth lw-precision-fuel
                                      lw-halving-depth-adequate lw-precision-fuel-adequate))))

(assert-event (let ((bounds (lw-rpow-bounds 2 1 2 1/1000)))
                (and (<= (* (car bounds) (car bounds)) 2)
                     (<= 2 (* (cdr bounds) (cdr bounds)))
                     (<= (- (cdr bounds) (car bounds)) 1/1000))))
(assert-event (let ((bounds (lw-rpow-bounds 10 2 3 1/100)))
                (and (<= (lw-rational-power (car bounds) 3) 100)
                     (<= 100 (lw-rational-power (cdr bounds) 3)))))
