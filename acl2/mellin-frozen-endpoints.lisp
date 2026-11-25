(in-package "ACL2")

(include-book "mellin-clipped-family-endpoints")

; Assemble every component of the frozen finite transform on the common
; mesh, with computed endpoints and an explicit total error radius.

(local (in-theory
 (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
          lw-mellin-clipped-basis-dyadic lw-mellin-frozen-basis-dyadic
          lw-mellin-clipped-ramp-linearization lw-mellin-clipped-basis-before-cutpoint
          lw-mellin-clipped-prime-dyadic
          lw-mellin-common-depth lw-mellin-common-endpoint lw-mellin-component-minimum-depth
          lw-mellin-component-endpoint-value lw-mellin-moment-endpoint-value
          lw-mellin-exponential-moment-cap lw-complex-exp-uniform-cap
          lw-exp-lipschitz-cap lw-mellin-weight lw-mellin-phase
          lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
          lw-complex-disk-enlarge lw-disk-enlarge lw-complex-sub-add-first
          lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-mellin-frozen-dyadic lw-mellin-dyadic-sum
 lw-mellin-clipped-linear-dyadic lw-mellin-prime-endpoint lw-mellin-prime-endpoint-mass
 lw-mellin-common-base-radius lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
 lw-signal-exponential-precision lw-signal-exponential-cost lw-kernel-spatial-cap lw-halved-width)))

(local (defthm lw-mfx-left-commutes
 (equal (* a (* b c)) (* b (* a c)))
 :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                       (:instance associativity-of-* (x b) (y a) (z c))
                       (:instance commutativity-of-* (x a) (y b)))
                 :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mfx-left-distributes
 (equal (* (+ a b) c) (+ (* a c) (* b c)))
 :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                 :in-theory (disable distributivity)))))

(local (defthm lw-mfx-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mfx-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mfx-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mfx-times-negative (a b) (b a)))
                         :in-theory (disable lw-mfx-times-negative)))))

(local (defthm lw-mfx-same-midpoint
 (implies (rationalp value) (equal (+ (* 1/2 value) (* 1/2 value)) value))))

(local (defthm lw-mfx-frozen-zero-width
 (implies (rationalp value)
  (equal (lw-mellin-frozen-basis-dyadic kind value value depth sigma height index exp-error prime log-error sample-error)
         (cons 0 0)))
 :hints (("Goal" :induct (lw-dyadic-leaf-count depth)
                 :in-theory (enable lw-complex-add lw-complex-scale))
         (and stable-under-simplificationp
          '(:expand ((lw-mellin-frozen-basis-dyadic
                       kind value value depth sigma height index exp-error prime log-error sample-error))
            :do-not-induct t)))))

(local (defthm lw-mfx-clipped-at-zero
 (implies (and (rationalp start) (<= 0 start) (rationalp end) (<= start end))
  (equal (lw-mellin-clipped-basis-dyadic kind start end depth 0 sigma height index exp-error prime log-error sample-error)
         (lw-mellin-frozen-basis-dyadic kind start end depth sigma height index exp-error prime log-error sample-error)))
 :hints (("Goal"
  :induct (lw-mellin-clipped-basis-dyadic kind start end depth 0 sigma height index exp-error prime log-error sample-error)
  :in-theory (enable lw-mellin-clipped-basis-dyadic lw-mellin-frozen-basis-dyadic)))))

(defthm lw-mellin-common-unclipped-comparison
 (implies
  (and (member-equal kind '(0 1 3))
       (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-frozen-basis-dyadic
     kind start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth)
     sigma height 0 exp-error prime log-error sample-error)
    (lw-mellin-common-endpoint kind cap start length 0 sigma height error))
   (+ (* length (lw-mellin-exponential-moment-cap kind cap)
         (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error)))
 :hints (("Goal" :use ((:instance lw-mellin-common-component-comparison (cutpoint 0)))
                 :in-theory (disable lw-mellin-common-component-comparison)
                 :do-not-induct t)))

(local (defthm lw-mfx-family-difference
 (equal
  (lw-complex-sub
   (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
   (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
  (lw-complex-add
   (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y)))
   (lw-complex-scale factor (lw-complex-sub c z))))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add lw-complex-scale)))
 :rule-classes nil))

(local (defthm lw-mfx-family-disk
 (implies (and (lw-complex-diskp (lw-complex-sub a x) radius)
               (lw-complex-diskp (lw-complex-sub b y) moment-radius)
               (lw-complex-diskp (lw-complex-sub c z) correction-radius) (rationalp factor))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-add (lw-complex-sub a b) (lw-complex-scale factor c))
    (lw-complex-add (lw-complex-sub x y) (lw-complex-scale factor z)))
   (+ radius moment-radius (* (abs factor) correction-radius))))
 :hints (("Goal"
   :use (lw-mfx-family-difference
         (:instance lw-complex-scale-disk (point (lw-complex-sub b y)) (radius moment-radius) (factor -1))
         (:instance lw-complex-scale-disk (point (lw-complex-sub c z)) (radius correction-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-sub a x)) (right (lw-complex-scale -1 (lw-complex-sub b y)))
          (other-radius moment-radius))
         (:instance lw-complex-add-disk
          (left (lw-complex-add (lw-complex-sub a x) (lw-complex-scale -1 (lw-complex-sub b y))))
          (right (lw-complex-scale factor (lw-complex-sub c z)))
          (radius (+ radius moment-radius)) (other-radius (* (abs factor) correction-radius))))
   :in-theory (disable lw-complex-scale-disk lw-complex-add-disk) :do-not-induct t))
 :rule-classes nil))

(defun lw-mellin-frozen-endpoint (cap start length sigma height model-error error)
 (let ((count (lw-log-signal-ramp-count cap)) (epsilon (lw-signal-exponential-precision cap model-error)))
  (lw-complex-add
   (lw-complex-sub
    (lw-mellin-prime-endpoint cap start length sigma height count count model-error epsilon error)
    (lw-mellin-common-endpoint 1 cap start length 0 sigma height error))
   (lw-complex-scale (+ 1 (car (lw-euler-bounds epsilon)))
    (lw-mellin-common-endpoint 0 cap start length 0 sigma height error)))))

(defun lw-mellin-frozen-endpoint-radius (cap length model-error sample-error error)
 (let* ((epsilon (lw-signal-exponential-precision cap model-error))
        (base (lw-mellin-common-base-radius cap length epsilon sample-error error)))
  (+ (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) epsilon) base)
     (* length cap (+ epsilon (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error
     (* (abs (+ 1 (car (lw-euler-bounds epsilon)))) base))))

(local (in-theory (disable lw-mellin-frozen-endpoint lw-mellin-frozen-endpoint-radius)))

(local (defthm lw-mfx-parameters
 (implies (and (rationalp cap) (<= 0 cap) (rationalp model-error) (< 0 model-error))
  (and (natp (lw-log-signal-ramp-count cap))
       (rationalp (lw-signal-exponential-precision cap model-error))
       (< 0 (lw-signal-exponential-precision cap model-error))
       (rationalp (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error))))))
 :hints (("Goal"
   :use (lw-log-signal-spatial-cap-valid
         (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
         (:instance lw-signal-exponential-parameters (error model-error))
         (:instance lw-euler-bounds-interval (epsilon (lw-signal-exponential-precision cap model-error))))
   :in-theory (e/d (lw-log-signal-ramp-count lw-intervalp)
     (lw-log-signal-spatial-cap-valid lw-signal-exponential-parameters lw-euler-bounds-interval))
   :do-not-induct t))
 :rule-classes nil))

(defthm lw-mellin-clipped-linear-endpoint-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-mellin-clipped-linear-dyadic cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error)
    (lw-mellin-frozen-endpoint cap start length sigma height model-error error))
   (lw-mellin-frozen-endpoint-radius cap length model-error sample-error error)))
 :hints (("Goal"
  :use (lw-mfx-parameters
        (:instance lw-mellin-prime-endpoint-comparison (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap)) (primitive-error (lw-signal-exponential-precision cap model-error)))
        (:instance lw-mellin-common-unclipped-comparison (kind 1) (exp-error (lw-signal-exponential-precision cap model-error)) (prime 2) (log-error 1))
        (:instance lw-mellin-common-unclipped-comparison (kind 0) (exp-error (lw-signal-exponential-precision cap model-error)) (prime 2) (log-error 1))
        (:instance lw-mfx-family-disk
         (a (lw-mellin-clipped-prime-dyadic start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) sample-error)) (x (lw-mellin-prime-endpoint cap start length sigma height (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) model-error (lw-signal-exponential-precision cap model-error) error)) (b (lw-mellin-frozen-basis-dyadic 1 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 (lw-signal-exponential-precision cap model-error) 2 1 sample-error)) (y (lw-mellin-common-endpoint 1 cap start length 0 sigma height error)) (c (lw-mellin-frozen-basis-dyadic 0 start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 (lw-signal-exponential-precision cap model-error) 2 1 sample-error)) (z (lw-mellin-common-endpoint 0 cap start length 0 sigma height error)) (factor (+ 1 (car (lw-euler-bounds (lw-signal-exponential-precision cap model-error)))))
         (radius (* (lw-mellin-prime-endpoint-mass (lw-log-signal-ramp-count cap) (lw-signal-exponential-precision cap model-error)) (lw-mellin-common-base-radius cap length (lw-signal-exponential-precision cap model-error) sample-error error))) (moment-radius (+ (* length cap (+ (lw-signal-exponential-precision cap model-error) (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error)) (correction-radius (lw-mellin-common-base-radius cap length (lw-signal-exponential-precision cap model-error) sample-error error))))
  :in-theory
  (e/d (lw-mellin-clipped-linear-dyadic lw-mellin-frozen-endpoint lw-mellin-frozen-endpoint-radius
        lw-mellin-common-base-radius lw-mellin-exponential-moment-cap)
       (lw-mellin-prime-endpoint-comparison lw-mellin-common-unclipped-comparison))
  :nonlinearp nil :do-not-induct t)))

; Restore the crossing cells and then the actual logarithmic signal.
; These estimates concern the actual zeroth Mellin samples on the
; common computed mesh; no transform identity is assumed.

(local (defthm lw-mfx-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-mfx-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mfx-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-frozen-grid-endpoint-comparison
 (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-frozen-dyadic cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error) (lw-mellin-frozen-endpoint cap start length sigma height model-error error)) (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error) (lw-mellin-frozen-endpoint-radius cap length model-error sample-error error))))
 :hints (("Goal"
  :use (lw-mellin-common-depth-adequate lw-mellin-clipped-linear-endpoint-comparison
        (:instance lw-mellin-clipped-family-comparison
         (end (+ start length)) (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (index 0))
        (:instance lw-mfx-triangle
         (left (lw-mellin-frozen-dyadic cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error)) (middle (lw-mellin-clipped-linear-dyadic cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error)) (right (lw-mellin-frozen-endpoint cap start length sigma height model-error error)) (radius (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error)) (other-radius (lw-mellin-frozen-endpoint-radius cap length model-error sample-error error))))
  :in-theory (disable lw-mellin-common-depth-adequate lw-mellin-clipped-linear-endpoint-comparison
                      lw-mellin-clipped-family-comparison)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-grid-endpoint-comparison
 (implies (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
       (rationalp length) (<= 0 length) (<= (+ start length) cap)
       (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-mellin-dyadic-sum start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 sample-error) (lw-mellin-frozen-endpoint cap start length sigma height model-error error)) (+ (* length (lw-kernel-spatial-cap cap 1) (+ sample-error model-error)) (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error) (lw-mellin-frozen-endpoint-radius cap length model-error sample-error error))))
 :hints (("Goal"
  :use (lw-mellin-common-depth-adequate lw-mellin-frozen-grid-endpoint-comparison
        (:instance lw-mellin-frozen-dyadic-comparison
         (end (+ start length)) (depth (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (index 0))
        (:instance lw-mfx-triangle
         (left (lw-mellin-dyadic-sum start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 sample-error)) (middle (lw-mellin-frozen-dyadic cap start (+ start length) (lw-mellin-common-depth cap start length sigma height error minimum-depth) sigma height 0 model-error sample-error)) (right (lw-mellin-frozen-endpoint cap start length sigma height model-error error))
         (radius (* length (lw-kernel-spatial-cap cap 1) (+ sample-error model-error))) (other-radius (+ (* (lw-halved-width length (lw-mellin-common-depth cap start length sigma height error minimum-depth)) (lw-kernel-spatial-cap cap 1) model-error) (lw-mellin-frozen-endpoint-radius cap length model-error sample-error error)))))
  :in-theory (disable lw-mellin-common-depth-adequate lw-mellin-frozen-grid-endpoint-comparison
                      lw-mellin-frozen-dyadic-comparison)
  :nonlinearp nil :do-not-induct t)))

; Compare the repository's bounded Mellin constructor with this endpoint
; expression. The common depth also refines the constructor's native grid;
; the cross-depth error is retained explicitly for later budget allocation.

(local (in-theory (disable lw-mellin-bounded-integral lw-mellin-integral-depth lw-mellin-integral-precision
                          lw-mellin-spatial-slope lw-mellin-spatial-error-factor)))

(defun lw-mellin-bounded-endpoint-radius (cap sigma height model-error integral-error error)
 (+ (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
              (+ (lw-halved-width cap (lw-mellin-integral-depth cap sigma height integral-error)) (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error (lw-mellin-integral-depth cap sigma height integral-error)))))
             (* (lw-mellin-spatial-error-factor cap 1) (+ (lw-mellin-integral-precision cap integral-error) (lw-mellin-integral-precision cap integral-error))))) (+ (* cap (lw-kernel-spatial-cap cap 1) (+ (lw-mellin-integral-precision cap integral-error) model-error))
           (* (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error (lw-mellin-integral-depth cap sigma height integral-error))) (lw-kernel-spatial-cap cap 1) model-error)
           (lw-mellin-frozen-endpoint-radius cap cap model-error (lw-mellin-integral-precision cap integral-error) error))))

(local (in-theory (disable lw-mellin-bounded-endpoint-radius)))

(defthm lw-mellin-bounded-endpoint-comparison
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 1 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp integral-error) (< 0 integral-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-mellin-bounded-integral cap sigma height 0 integral-error) (lw-mellin-frozen-endpoint cap 0 cap sigma height model-error error))
   (lw-mellin-bounded-endpoint-radius cap sigma height model-error integral-error error)))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-depth-adequate (error integral-error))
        (:instance lw-mellin-integral-precision-valid (error integral-error))
        (:instance lw-mellin-common-depth-adequate (start 0) (length cap) (minimum-depth (lw-mellin-integral-depth cap sigma height integral-error)))
        (:instance lw-mellin-grid-endpoint-comparison
         (start 0) (length cap) (sample-error (lw-mellin-integral-precision cap integral-error)) (minimum-depth (lw-mellin-integral-depth cap sigma height integral-error)))
        (:instance lw-mellin-dyadic-cross-depth
         (left-depth (lw-mellin-integral-depth cap sigma height integral-error)) (right-depth (lw-mellin-common-depth cap 0 cap sigma height error (lw-mellin-integral-depth cap sigma height integral-error))) (index 0) (left-error (lw-mellin-integral-precision cap integral-error)) (right-error (lw-mellin-integral-precision cap integral-error)))
        (:instance lw-mfx-triangle
         (left (lw-mellin-bounded-integral cap sigma height 0 integral-error))
         (middle (lw-mellin-dyadic-sum 0 cap (lw-mellin-common-depth cap 0 cap sigma height error (lw-mellin-integral-depth cap sigma height integral-error)) sigma height 0 (lw-mellin-integral-precision cap integral-error))) (right (lw-mellin-frozen-endpoint cap 0 cap sigma height model-error error)) (radius (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
              (+ (lw-halved-width cap (lw-mellin-integral-depth cap sigma height integral-error)) (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error (lw-mellin-integral-depth cap sigma height integral-error)))))
             (* (lw-mellin-spatial-error-factor cap 1) (+ (lw-mellin-integral-precision cap integral-error) (lw-mellin-integral-precision cap integral-error)))))) (other-radius (+ (* cap (lw-kernel-spatial-cap cap 1) (+ (lw-mellin-integral-precision cap integral-error) model-error))
           (* (lw-halved-width cap (lw-mellin-common-depth cap 0 cap sigma height error (lw-mellin-integral-depth cap sigma height integral-error))) (lw-kernel-spatial-cap cap 1) model-error)
           (lw-mellin-frozen-endpoint-radius cap cap model-error (lw-mellin-integral-precision cap integral-error) error)))))
  :in-theory (e/d (lw-mellin-bounded-integral lw-mellin-bounded-endpoint-radius)
    (lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
     lw-mellin-common-depth-adequate lw-mellin-grid-endpoint-comparison lw-mellin-dyadic-cross-depth))
  :nonlinearp nil :do-not-induct t)))

