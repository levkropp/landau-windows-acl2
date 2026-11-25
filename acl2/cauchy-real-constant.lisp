(in-package "ACL2")

(include-book "cauchy-extraction")

; Only the real constant term is needed for counting poles.
(defun lw-cauchy-real-boundary-check (coefficients point count cap)
  (if (zp count) t
    (and (<= (abs (car (lw-complex-polynomial coefficients (lw-complex-power point (- count 1)) 0))) cap)
         (lw-cauchy-real-boundary-check coefficients point (- count 1) cap))))

(local (in-theory
        (disable lw-complex-polynomial lw-complex-coefficientsp
                 lw-cauchy-coefficient-count lw-cauchy-orbit-rotation
                 lw-cauchy-evaluation-sum lw-cauchy-evaluation-sum-expansion
                 lw-cauchy-polynomial-average lw-cauchy-polynomial-average-moments)))

(local
 (defthm lw-crc-car-rational
   (implies (lw-complexp point) (rationalp (car point)))
   :hints (("Goal" :in-theory (enable lw-complexp)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-crc-power-zero
   (equal (lw-complex-conjugate (lw-complex-power point 0)) (cons 1 0))
   :hints (("Goal" :in-theory (enable lw-complex-power lw-complex-conjugate)))))

(local
 (defthm lw-crc-sum-step
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (posp count))
            (equal (car (lw-cauchy-evaluation-sum coefficients point 0 0 count))
                   (+ (car (lw-complex-polynomial coefficients (lw-complex-power point (- count 1)) 0)) (car (lw-cauchy-evaluation-sum coefficients point 0 0 (- count 1))))))
   :hints (("Goal" :expand ((:free (target offset) (lw-cauchy-evaluation-sum coefficients point target offset count)))
                   :in-theory (enable lw-complex-add lw-complex-mul-one)))))

(local
 (defthm lw-crc-sum-zero
   (equal (car (lw-cauchy-evaluation-sum coefficients point 0 0 0)) 0)
   :hints (("Goal" :in-theory (enable lw-cauchy-evaluation-sum)))))

(local
 (defthm lw-crc-product-negative
   (implies (and (rationalp factor) (rationalp value))
            (equal (* factor (- value)) (- (* factor value))))
   :hints (("Goal" :use ((:instance distributivity (x factor) (y value) (z (- value))))
                   :in-theory (disable distributivity)))
   :rule-classes nil))

(local
 (defthm lw-crc-sum-bound
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                 (natp count) (rationalp cap) (<= 0 cap)
                 (lw-cauchy-real-boundary-check coefficients point count cap))
            (and (<= (car (lw-cauchy-evaluation-sum coefficients point 0 0 count)) (* count cap))
                 (<= (- (* count cap)) (car (lw-cauchy-evaluation-sum coefficients point 0 0 count)))))
   :hints (("Goal" :induct (lw-cauchy-real-boundary-check coefficients point count cap)
                   :in-theory (enable abs)))))

(local
 (defthm lw-crc-scale-order
   (implies (and (rationalp lower) (rationalp upper) (rationalp factor)
                 (<= lower upper) (<= 0 factor))
            (<= (* factor lower) (* factor upper)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-crc-inverse-cancel
   (implies (and (posp count) (rationalp cap))
            (and (equal (* (/ count) (* count cap)) cap)
                 (equal (* (/ count) (* count (- cap))) (- cap))))
   :hints (("Goal"
            :use ((:instance associativity-of-* (x (/ count)) (y count) (z cap))
                  (:instance associativity-of-* (x (/ count)) (y count) (z (- cap)))
                  (:instance commutativity-of-* (x (/ count)) (y count))
                  (:instance inverse-of-* (x count)))
            :in-theory (disable associativity-of-* commutativity-of-* inverse-of-*)))
   :rule-classes nil))

(local
 (defthm lw-crc-divide-bound
   (implies (and (posp count) (rationalp total) (rationalp cap)
                 (<= (* count (- cap)) total) (<= total (* count cap)))
            (and (<= (- cap) (* (/ count) total))
                 (<= (* (/ count) total) cap)))
   :hints (("Goal"
            :use (lw-crc-inverse-cancel
                  (:instance lw-crc-scale-order
                    (lower (* count (- cap))) (upper total) (factor (/ count)))
                  (:instance lw-crc-scale-order
                    (lower total) (upper (* count cap)) (factor (/ count))))
            :in-theory (disable associativity-of-*)))
   :rule-classes nil))

(local
 (defthm lw-crc-average-bound
   (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                 (posp count) (rationalp cap) (<= 0 cap)
                 (lw-cauchy-real-boundary-check coefficients (lw-cauchy-orbit-rotation degree) count cap))
            (and (<= (- cap) (car (lw-cauchy-polynomial-average coefficients degree 0 count)))
                 (<= (car (lw-cauchy-polynomial-average coefficients degree 0 count)) cap)))
   :hints (("Goal"
            :use (lw-cauchy-orbit-data
                  (:instance lw-crc-sum-bound (point (lw-cauchy-orbit-rotation degree)))
                  (:instance lw-crc-product-negative (factor count) (value cap))
                  (:instance lw-crc-divide-bound
                    (total (car (lw-cauchy-evaluation-sum coefficients (lw-cauchy-orbit-rotation degree) 0 0 count)))))
            :in-theory (e/d (lw-cauchy-polynomial-average lw-complex-scale)
                            (lw-crc-sum-bound lw-cauchy-real-boundary-check))))
   :rule-classes nil))

(defthm lw-cauchy-finite-real-constant-bound
  (implies (and (lw-complex-coefficientsp coefficients) (consp coefficients)
                (natp degree) (<= (len coefficients) (+ 1 degree))
                (rationalp error) (< 0 error) (rationalp cap) (<= 0 cap)
                (lw-cauchy-real-boundary-check coefficients (lw-cauchy-orbit-rotation degree) (lw-cauchy-coefficient-count coefficients degree error) cap))
           (<= (abs (car (car coefficients))) (+ cap error)))
  :hints (("Goal"
           :use ((:instance lw-cauchy-computed-coefficient-recovery (target 0))
                 (:instance lw-crc-average-bound (count (lw-cauchy-coefficient-count coefficients degree error)))
                 (:instance lw-complex-disk-coordinates (point (lw-complex-sub (lw-cauchy-polynomial-average coefficients degree 0 (lw-cauchy-coefficient-count coefficients degree error)) (nth 0 coefficients))) (radius error)))
           :in-theory (e/d (lw-complex-sub abs)
                           (lw-cauchy-real-boundary-check
                            lw-cauchy-computed-coefficient-recovery lw-complex-disk-coordinates)))))
