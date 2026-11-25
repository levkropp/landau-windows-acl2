; Part Five's finite arithmetic illustrations. The complex analytic
; Landau theorem is not assumed or re-labelled as one of these lemmas.
(in-package "ACL2")
(include-book "../acl2/landau-bounds")

(defun video-positive-part (x)
  (max x 0))

(defthm video-positive-part-identity
  (implies (rationalp x)
           (equal (+ (abs x) x)
                  (* 2 (video-positive-part x))))
  :hints (("Goal" :in-theory (enable abs max))))

(defun video-plain-three (x y z)
  (+ x y z))

(defun video-signed-three (x y z)
  (+ x (- y) z))

(local
 (defthm video-three-triangle
   (implies (and (rationalp x) (rationalp y) (rationalp z))
            (<= (abs (video-signed-three x y z))
                (+ (abs x) (abs y) (abs z))))
   :hints (("Goal" :in-theory (enable abs)))))

(defthm video-three-one-sided
  (implies (and (rationalp x) (rationalp y) (rationalp z))
           (<= (+ (abs (video-signed-three x y z))
                  (video-plain-three x y z))
               (* 2 (+ (video-positive-part x)
                       (video-positive-part y)
                       (video-positive-part z)))))
  :hints (("Goal" :in-theory (enable abs max)))
  :rule-classes nil)

(defthm video-one-sided-examples
  (and (equal (video-signed-three -3 2 -1) -6)
       (equal (video-plain-three -3 2 -1) -2)
       (equal (+ (abs (video-signed-three -3 2 -1))
                 (video-plain-three -3 2 -1)) 4)
       (equal (+ (abs (video-signed-three -10 2 -1))
                 (video-plain-three -10 2 -1)) 4))
  :rule-classes nil)

(defthm video-geometric-demo
  (and (equal (lw-geometric-index 3/2 8) 17)
       (implies (and (natp k) (<= 17 k))
                (<= 8 (lw-rational-power 3/2 k))))
  :hints (("Goal" :use ((:instance lw-geometric-threshold
                          (base 3/2) (target 8) (exponent k)))
                  :in-theory (disable lw-geometric-threshold
                                      lw-rational-power)))
  :rule-classes nil)

(defthm video-midpoint-gap
  (implies (and (rationalp beta) (< 1/2 beta) (< beta 1))
           (let ((epsilon (/ (- beta 1/2) 2)))
             (and (< 0 epsilon)
                  (< 1/2 (+ 1/2 epsilon))
                  (< (+ 1/2 epsilon) beta)
                  (< (+ 1/2 epsilon) 1))))
  :rule-classes nil)

(defthm video-window-endpoints
  (and (equal (* 8 8) (* 4 4 4))
       (equal (* 64 64) (* 16 16 16))
       (equal (* 512 512) (* 64 64 64)))
  :rule-classes nil)

(assert-event (equal (lw-rational-power 3/2 6) 729/64))
(assert-event (equal (lw-rational-power 3/2 17) 129140163/131072))
(assert-event (equal (video-positive-part -10) 0))
(assert-event (equal (video-positive-part 2) 2))
