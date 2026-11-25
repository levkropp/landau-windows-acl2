(in-package "ACL2")

(include-book "rpow-bounds")
(include-book "log-bounds")

(defun lw-no-divisor (value trial)
  (declare (xargs :measure (nfix trial)))
  (if (or (not (natp trial)) (< trial 2))
      t
    (and (not (equal (mod value trial) 0))
         (lw-no-divisor value (- trial 1)))))

(defun lw-primep (value)
  (and (integerp value) (<= 2 value) (lw-no-divisor value (- value 1))))

(defthm lw-no-divisor-sound
  (implies (and (lw-no-divisor value trial)
                (integerp divisor) (<= 2 divisor)
                (natp trial) (<= divisor trial))
           (not (equal (mod value divisor) 0)))
  :hints (("Goal" :induct (lw-no-divisor value trial))))

(defthm lw-primep-lower-bound
  (implies (lw-primep value) (and (integerp value) (<= 2 value))))

(defthm lw-primep-no-proper-divisor
  (implies (and (lw-primep value) (integerp divisor)
                (<= 2 divisor) (< divisor value))
           (not (equal (mod value divisor) 0)))
  :hints (("Goal" :use ((:instance lw-no-divisor-sound (trial (- value 1))))
                  :in-theory (disable lw-no-divisor lw-no-divisor-sound))))

(defun lw-power-exponent (value base limit)
  (declare (xargs :measure (nfix limit)))
  (if (zp limit)
      nil
    (if (equal (lw-rational-power base limit) value)
        limit
      (lw-power-exponent value base (- limit 1)))))

(defthm lw-power-exponent-sound
  (implies (lw-power-exponent value base limit)
           (and (posp (lw-power-exponent value base limit))
                (<= (lw-power-exponent value base limit) limit)
                (equal (lw-rational-power base (lw-power-exponent value base limit)) value)))
  :hints (("Goal" :induct (lw-power-exponent value base limit)
                  :in-theory (disable lw-rational-power))))

(defthm lw-power-exponent-complete
  (implies (and (posp exponent) (natp limit) (<= exponent limit)
                (equal (lw-rational-power base exponent) value))
           (lw-power-exponent value base limit))
  :hints (("Goal" :induct (lw-power-exponent value base limit)
                  :in-theory (disable lw-rational-power))))

(defun lw-prime-power-search (value candidate)
  (declare (xargs :measure (nfix candidate)))
  (if (or (not (natp candidate)) (< candidate 2))
      nil
    (let ((exponent (and (lw-primep candidate)
                         (lw-power-exponent value candidate (nfix value)))))
      (if exponent
          (cons candidate exponent)
        (lw-prime-power-search value (- candidate 1))))))

(defthm lw-prime-power-search-sound
  (implies (lw-prime-power-search value candidate)
           (let ((found (lw-prime-power-search value candidate)))
             (and (consp found) (lw-primep (car found))
                  (<= (car found) candidate) (posp (cdr found))
                  (<= (cdr found) (nfix value))
                  (equal (lw-rational-power (car found) (cdr found)) value))))
  :hints (("Goal" :induct (lw-prime-power-search value candidate)
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (disable lw-primep lw-power-exponent lw-rational-power))
          (and stable-under-simplificationp
               '(:use ((:instance lw-power-exponent-sound
                         (base candidate) (limit (nfix value))))
                 :in-theory (disable lw-power-exponent lw-power-exponent-sound
                                     lw-primep lw-rational-power)))))

(defthm lw-prime-power-search-complete
  (implies (and (lw-primep base) (posp exponent) (natp value)
                (<= exponent value) (natp candidate) (<= base candidate)
                (equal (lw-rational-power base exponent) value))
           (lw-prime-power-search value candidate))
  :hints (("Goal" :induct (lw-prime-power-search value candidate)
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (disable lw-primep lw-power-exponent lw-rational-power))
          (and stable-under-simplificationp
               '(:use ((:instance lw-primep-lower-bound (value base))
                        (:instance lw-power-exponent-complete
                          (value (lw-rational-power base exponent))
                          (limit (lw-rational-power base exponent))))
                 :in-theory (disable lw-primep lw-primep-lower-bound
                                     lw-power-exponent lw-power-exponent-complete
                                     lw-rational-power)))))

(defthm lw-prime-power-exponent-bound
  (implies (and (lw-primep base) (posp exponent))
           (<= exponent (lw-rational-power base exponent)))
  :hints (("Goal" :use ((:instance lw-primep-lower-bound (value base))
                        (:instance lw-rational-power-bernoulli))
                  :in-theory (disable lw-primep lw-primep-lower-bound lw-rational-power
                                      lw-rational-power-bernoulli)
                  :nonlinearp t)))

(defthm lw-prime-power-base-bound
  (implies (and (lw-primep base) (posp exponent))
           (<= base (lw-rational-power base exponent)))
  :hints (("Goal" :use ((:instance lw-primep-lower-bound (value base))
                        (:instance lw-rational-power-monotone-exponent
                          (small 1) (large exponent)))
                  :in-theory (disable lw-primep lw-primep-lower-bound
                                      lw-rational-power-monotone-exponent))))

(defun lw-prime-power-data (value)
  (lw-prime-power-search value (nfix value)))

(defthm lw-prime-power-data-sound
  (implies (lw-prime-power-data value)
           (let ((found (lw-prime-power-data value)))
             (and (consp found) (lw-primep (car found))
                  (<= (car found) (nfix value)) (posp (cdr found))
                  (<= (cdr found) (nfix value))
                  (equal (lw-rational-power (car found) (cdr found)) value))))
  :hints (("Goal" :use ((:instance lw-prime-power-search-sound (candidate (nfix value))))
                  :in-theory (disable lw-prime-power-search lw-prime-power-search-sound
                                      lw-primep lw-rational-power))))

(defthm lw-prime-power-data-complete
  (implies (and (natp value) (lw-primep base) (posp exponent)
                (equal (lw-rational-power base exponent) value))
           (lw-prime-power-data value))
  :hints (("Goal" :use (lw-prime-power-exponent-bound lw-prime-power-base-bound
                        (:instance lw-prime-power-search-complete (candidate value)))
                  :in-theory (disable lw-primep lw-rational-power lw-prime-power-search
                                      lw-prime-power-exponent-bound lw-prime-power-base-bound
                                      lw-prime-power-search-complete))))

(defun lw-mangoldt-bounds (value epsilon)
  (let ((found (lw-prime-power-data value)))
    (if found (lw-log-bounds (car found) epsilon) (cons 0 0))))

(defthm lw-mangoldt-bounds-interval
  (implies (and (rationalp epsilon) (< 0 epsilon))
           (lw-intervalp (lw-mangoldt-bounds value epsilon)))
  :hints (("Goal" :use (lw-prime-power-data-sound
                        (:instance lw-primep-lower-bound
                          (value (car (lw-prime-power-data value)))))
                  :in-theory (disable lw-prime-power-data lw-prime-power-data-sound
                                      lw-primep lw-primep-lower-bound lw-log-bounds))))

(defthm lw-mangoldt-bounds-width
  (implies (and (rationalp epsilon) (< 0 epsilon))
           (<= (- (cdr (lw-mangoldt-bounds value epsilon))
                  (car (lw-mangoldt-bounds value epsilon))) epsilon))
  :hints (("Goal" :use (lw-prime-power-data-sound
                        (:instance lw-log-bounds-width
                          (value (car (lw-prime-power-data value))))
                        (:instance lw-primep-lower-bound
                          (value (car (lw-prime-power-data value)))))
                  :in-theory (disable lw-prime-power-data lw-prime-power-data-sound
                                      lw-primep lw-primep-lower-bound lw-log-bounds
                                      lw-log-bounds-width))))

(assert-event (equal (lw-prime-power-data 81) '(3 . 4)))
(assert-event (equal (lw-prime-power-data 16) '(2 . 4)))
(assert-event (equal (lw-prime-power-data 13) '(13 . 1)))
(assert-event (not (lw-prime-power-data 6)))
(assert-event (not (lw-prime-power-data 1)))
