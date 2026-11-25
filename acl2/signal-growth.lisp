(in-package "ACL2")

(include-book "signal-continuity")

(local
 (defthm lw-sg-multiply-order
   (implies (and (rationalp left) (rationalp right) (<= left right)
                 (rationalp factor) (<= 0 factor))
            (<= (* left factor) (* right factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm lw-mangoldt-ramp-lower-growth
  (implies (and (rationalp value) (<= 0 value) (posp index)
                (rationalp epsilon) (< 0 epsilon))
           (and (<= 0 (* (lw-ramp value index) (car (lw-mangoldt-bounds index epsilon))))
                (<= (* (lw-ramp value index) (car (lw-mangoldt-bounds index epsilon))) value)))
  :hints (("Goal" :use (lw-mangoldt-lower-coarse lw-ramp-rescale
                        (:instance lw-sg-multiply-order
                          (left (car (lw-mangoldt-bounds index epsilon))) (right index)
                          (factor (lw-ramp value index))))
                  :in-theory (disable lw-mangoldt-bounds lw-mangoldt-lower-coarse lw-ramp-rescale)
                  :nonlinearp t)))

(defthm lw-smoothed-sum-lower-linear-growth
  (implies (and (rationalp value) (<= 0 value) (natp count)
                (rationalp epsilon) (< 0 epsilon))
           (and (<= 0 (car (lw-smoothed-sum-bounds value count epsilon)))
                (<= (car (lw-smoothed-sum-bounds value count epsilon)) (* count value))))
  :hints (("Goal" :induct (lw-smoothed-sum-bounds value count epsilon)
                  :in-theory (disable lw-ramp lw-mangoldt-bounds))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mangoldt-ramp-lower-growth (index count)))
                 :in-theory (disable lw-smoothed-sum-bounds lw-ramp lw-mangoldt-bounds
                                     lw-mangoldt-ramp-lower-growth)))))

(local (defthm lw-sg-smoothed-zero
         (equal (lw-smoothed-sum-bounds value 0 epsilon) (cons 0 0))))

(defthm lw-smoothed-sum-lower-quadratic-growth
  (implies (and (rationalp value) (<= 0 value) (natp count)
                (rationalp epsilon) (< 0 epsilon))
           (<= (car (lw-smoothed-sum-bounds value count epsilon)) (* value value)))
  :hints (("Goal" :induct (lw-smoothed-sum-bounds value count epsilon)
                  :in-theory (disable (:definition lw-smoothed-sum-bounds) lw-smoothed-sum-bounds-zero-tail))
          (and stable-under-simplificationp
               '(:cases ((<= count value))
                 :use (lw-smoothed-sum-lower-linear-growth lw-smoothed-sum-bounds-zero-tail)
                 :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-zero-tail
                                     lw-smoothed-sum-lower-linear-growth)
                 :nonlinearp t))))

(defthm lw-log-upper-coarse
  (implies (and (rationalp value) (< 1 value)
                (rationalp epsilon) (< 0 epsilon) (<= epsilon 1))
           (and (<= 0 (cdr (lw-log-bounds value epsilon)))
                (<= (cdr (lw-log-bounds value epsilon)) value)))
  :hints (("Goal" :use (lw-log-bounds-lower-coarse lw-log-bounds-width lw-log-bounds-interval)
                  :in-theory (disable lw-log-bounds lw-log-bounds-lower-coarse
                                      lw-log-bounds-width lw-log-bounds-interval
                                      lw-log-bounds-monotone-overlap lw-log-bounds-overlap))))

; Lower approximations at every precision used for quadrature have a
; uniform two-sided growth bound, independent of padding/truncation count.
(defthm lw-gz-lower-quadratic-growth
  (implies (and (rationalp value) (< 1 value) (natp count)
                (rationalp epsilon) (< 0 epsilon) (<= epsilon 1))
           (and (<= (- (* value value)) (car (lw-gz-bounds-raw value count epsilon)))
                (<= (car (lw-gz-bounds-raw value count epsilon)) (* 4 value value))))
  :hints (("Goal" :use (lw-smoothed-sum-lower-linear-growth
                        lw-smoothed-sum-lower-quadratic-growth
                        lw-log-upper-coarse lw-euler-bounds-coarse
                        lw-smoothed-sum-bounds-valid lw-log-bounds-interval lw-euler-bounds-interval)
                  :in-theory (disable lw-smoothed-sum-bounds lw-log-bounds lw-euler-bounds
                                      lw-smoothed-sum-lower-linear-growth lw-smoothed-sum-lower-quadratic-growth
                                      lw-log-upper-coarse lw-euler-bounds-coarse
                                      lw-smoothed-sum-bounds-valid lw-log-bounds-interval lw-euler-bounds-interval
                                      lw-euler-bounds-overlap lw-log-bounds-overlap lw-log-bounds-monotone-overlap)
                  :nonlinearp t)))

(defthm lw-gz-lower-absolute-growth
  (implies (and (rationalp value) (< 1 value) (natp count)
                (rationalp epsilon) (< 0 epsilon) (<= epsilon 1))
           (<= (abs (car (lw-gz-bounds-raw value count epsilon))) (* 4 value value)))
  :hints (("Goal" :use (lw-gz-lower-quadratic-growth)
                  :in-theory (disable lw-gz-bounds-raw lw-gz-lower-quadratic-growth)
                  :nonlinearp t)))

(assert-event
 (let* ((value 3/2) (epsilon 1/2) (bound (lw-gz-bounds-raw value 2 epsilon)))
   (and (<= (- (* value value)) (car bound)) (<= (abs (car bound)) (* 4 value value)))))
