(in-package "ACL2")

(include-book "mellin-frozen-tail")

; Compare the actual bounded Mellin constructor with one frozen finite
; signal family on every dyadic refinement. The model precision is
; uniform over nodes, depth and moment index.

(local (in-theory
        (disable lw-smoothed-sum-bounds lw-mangoldt-bounds lw-ramp
                 lw-log-ramp-extension lw-exp-lipschitz-cap
                 lw-log-signal-point lw-log-signal-delta lw-log-signal-cap
                 lw-log-signal-margin lw-log-signal-lipschitz lw-log-signal-budget
                 lw-log-signal-spatial-cap lw-signal-count lw-signal-precision
                 lw-log-signal-linear-precision lw-interval-add lw-interval-scale
                 lw-log-bounds lw-euler-bounds lw-exp-bounds lw-exp-index lw-exp-term lw-exp-sum
                 lw-smoothed-ramp-unit-error lw-smoothed-ramp-log-error lw-log-signal-ramp-count
                 lw-smoothed-ramp-extension-sum lw-smoothed-sum-bounds-zero-tail lw-exp-bounds-valid
                 lw-signal-exponential-value lw-signal-exponential-linear
                 lw-signal-exponential-cost lw-signal-exponential-precision
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp lw-diskp
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-mellin-sample lw-mellin-signal lw-mellin-weight lw-mellin-phase
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-log-signal-bounds
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-kernel-spatial-cap lw-mellin-frozen-sample lw-mellin-dyadic-sum
                 lw-mellin-integral-precision lw-mellin-integral-depth lw-mellin-bounded-integral
                 lw-mellin-spatial-error-factor lw-mellin-signal-spatial-cap)))

(local (defthm lw-mfq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mfq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mfq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-mfq-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mfq-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mfq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mfq-left-commutes)))))
(local (defthm lw-mfq-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mfq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mfq-abs-product
         (implies (and (rationalp a) (rationalp b)) (equal (abs (* a b)) (* (abs a) (abs b))))
         :hints (("Goal" :cases ((<= 0 a) (<= 0 b)) :nonlinearp t))))
(local (defthm lw-mfq-sum-error
         (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                       (rationalp radius) (rationalp other-radius)
                       (<= (abs (- a b)) radius) (<= (abs (- c d)) other-radius))
                  (<= (abs (- (+ a c) (+ b d))) (+ radius other-radius)))
         :hints (("Goal" :cases ((<= a b) (<= c d)))) :rule-classes nil))
(local (defthm lw-mfq-weighted-error
         (implies
          (and (rationalp a) (rationalp b) (rationalp weight) (<= 0 weight)
               (rationalp index) (< 0 index) (<= weight index)
               (rationalp radius) (<= 0 radius) (<= (abs (- a b)) (* radius (/ index))))
          (<= (abs (- (* weight a) (* weight b))) radius))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x index))
                        (:instance lw-mfq-multiply-order
                          (a (abs (- a b))) (b (* radius (/ index))) (factor weight))
                        (:instance lw-mfq-multiply-order
                          (a weight) (b index) (factor (* radius (/ index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))




(local (defthm lw-mfq-signal-error-upper
         (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 0 sigma)
                       (rationalp step) (<= 0 step) (rationalp sample-error) (< 0 sample-error))
                  (<= (lw-mellin-signal-error value sigma index step sample-error) sample-error))
         :hints (("Goal"
                  :use ((:instance lw-mellin-kernel-cap-valid)
                        (:instance lw-mellin-component-error-at-most-request
                          (error sample-error) (factor (lw-mellin-kernel-cap value sigma index step))))
                  :in-theory (e/d (lw-mellin-signal-error)
                                  (lw-mellin-kernel-cap-valid lw-mellin-component-error-at-most-request))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-mfq-weight-budget
         (implies (and (rationalp weight) (<= 0 weight) (rationalp top) (<= weight top)
                       (rationalp left) (rationalp right) (<= left right)
                       (rationalp model) (<= 0 model) (<= 0 right))
                  (<= (* weight (+ left model)) (* top (+ right model))))
         :hints (("Goal"
                  :use ((:instance lw-mfq-multiply-order (a left) (b right) (factor weight))
                        (:instance lw-mfq-multiply-order (a weight) (b top) (factor (+ right model))))
                  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(defthm lw-mellin-frozen-sample-uniform-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp step) (<= 0 step)
                (rationalp model-error) (< 0 model-error)
                (rationalp sample-error) (< 0 sample-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-sample value sigma height index step sample-error)
                            (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error))
            (* (lw-kernel-spatial-cap cap step) (+ sample-error model-error))))
  :hints (("Goal"
           :use (lw-mfq-signal-error-upper
                 (:instance lw-mellin-frozen-sample-comparison)
                 (:instance lw-mellin-error-budgets (error sample-error))
                 (:instance lw-mellin-weight-bounded (error sample-error))
                 (:instance lw-kernel-weight-bounds-valid (error (lw-mellin-kernel-error value sample-error)))
                 (:instance lw-kernel-weight-scale-spatial-cap)
                 (:instance lw-mfq-weight-budget
                   (weight (lw-mellin-weight value sigma index step sample-error))
                   (top (lw-kernel-spatial-cap cap step))
                   (left (lw-mellin-signal-error value sigma index step sample-error))
                   (right sample-error) (model model-error))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-sample value sigma height index step sample-error)
                     (lw-mellin-frozen-sample cap value sigma height index step model-error sample-error)))
                   (radius (* (lw-mellin-weight value sigma index step sample-error)
                              (+ (lw-mellin-signal-error value sigma index step sample-error) model-error)))
                   (cap (* (lw-kernel-spatial-cap cap step) (+ sample-error model-error)))))
           :in-theory
           (e/d (lw-mellin-weight lw-intervalp)
                (lw-mellin-frozen-sample-comparison lw-mellin-error-budgets lw-mellin-weight-bounded
                 lw-kernel-weight-bounds-valid lw-kernel-weight-scale-spatial-cap
                 lw-kernel-weight-bounds-overlap))
           :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-frozen-dyadic (cap start end depth sigma height index model-error sample-error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (lw-complex-scale (- end start) (lw-mellin-frozen-sample cap start sigma height index 1 model-error sample-error))
    (let ((middle (/ (+ start end) 2)))
      (lw-complex-add
        (lw-mellin-frozen-dyadic cap start middle (- depth 1) sigma height index model-error sample-error)
        (lw-mellin-frozen-dyadic cap middle end (- depth 1) sigma height index model-error sample-error)))))

(defthm lw-mellin-frozen-dyadic-rational
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (natp depth) (rationalp sigma) (<= 0 sigma) (rationalp height)
        (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complexp (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)))
  :hints (("Goal"
           :induct (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
           :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-frozen-sample-rational (value start) (step 1)))
                 :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale)
                                 (lw-mellin-frozen-sample-rational))))))

(local (defthm lw-mfq-scale-difference
         (implies (and (lw-complexp a) (lw-complexp b) (rationalp factor))
                  (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                         (lw-complex-scale factor (lw-complex-sub a b))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))
         :rule-classes nil))

(local (defthm lw-mfq-scale-comparison
         (implies (and (lw-complexp a) (lw-complexp b) (rationalp factor) (<= 0 factor)
                       (lw-complex-diskp (lw-complex-sub a b) radius))
                  (lw-complex-diskp
                   (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                   (* factor radius)))
         :hints (("Goal"
                  :use (lw-mfq-scale-difference
                        (:instance lw-complex-scale-disk (point (lw-complex-sub a b))))
                  :in-theory (disable lw-complex-scale-disk) :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mfq-add-differences
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
                  (equal (lw-complex-sub (lw-complex-add a c) (lw-complex-add b d))
                         (lw-complex-add (lw-complex-sub a b) (lw-complex-sub c d))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-add)))
         :rule-classes nil))

(local (defthm lw-mfq-add-comparison
         (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                       (lw-complex-diskp (lw-complex-sub a b) radius)
                       (lw-complex-diskp (lw-complex-sub c d) other-radius))
                  (lw-complex-diskp
                   (lw-complex-sub (lw-complex-add a c) (lw-complex-add b d))
                   (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mfq-add-differences
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub a b)) (right (lw-complex-sub c d))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-frozen-dyadic-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-dyadic-sum start end depth sigma height index sample-error)
     (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error))
    (* (- end start) (lw-kernel-spatial-cap cap 1) (+ sample-error model-error))))
  :hints (("Goal"
           :induct (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
           :in-theory (enable lw-mellin-frozen-dyadic lw-mellin-dyadic-sum))
          (and stable-under-simplificationp
               '(:use (
                 (:instance lw-mellin-frozen-sample-uniform-comparison (value start) (step 1))
                 (:instance lw-mellin-sample-rational (value start) (step 1) (error sample-error))
                 (:instance lw-mellin-frozen-sample-rational (value start) (step 1))
                 (:instance lw-mfq-scale-comparison
                   (a (lw-mellin-sample start sigma height index 1 sample-error))
                   (b (lw-mellin-frozen-sample cap start sigma height index 1 model-error sample-error))
                   (factor (- end start))
                   (radius (* (lw-kernel-spatial-cap cap 1) (+ sample-error model-error))))
                 (:instance lw-mfq-add-comparison
                   (a (lw-mellin-dyadic-sum start (/ (+ start end) 2) (- depth 1) sigma height index sample-error))
                   (b (lw-mellin-frozen-dyadic cap start (/ (+ start end) 2) (- depth 1)
                                              sigma height index model-error sample-error))
                   (c (lw-mellin-dyadic-sum (/ (+ start end) 2) end (- depth 1) sigma height index sample-error))
                   (d (lw-mellin-frozen-dyadic cap (/ (+ start end) 2) end (- depth 1)
                                              sigma height index model-error sample-error))
                   (radius (* (- (/ (+ start end) 2) start)
                              (lw-kernel-spatial-cap cap 1) (+ sample-error model-error)))
                   (other-radius (* (- end (/ (+ start end) 2))
                                    (lw-kernel-spatial-cap cap 1) (+ sample-error model-error)))))
                 :in-theory
                 (disable lw-mellin-frozen-dyadic lw-mellin-dyadic-sum
                          lw-mellin-frozen-sample-uniform-comparison lw-mellin-sample-rational
                          lw-mellin-frozen-sample-rational)
                 :nonlinearp nil))))

(local (in-theory (disable lw-mellin-frozen-dyadic)))

(local (defthm lw-mfq-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b))
                  (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mfq-spatial-factor-dominates
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (rationalp (lw-kernel-spatial-cap cap 1))
                       (<= 0 (lw-kernel-spatial-cap cap 1))
                       (rationalp (lw-mellin-spatial-error-factor cap 1))
                       (<= (lw-kernel-spatial-cap cap 1) (lw-mellin-spatial-error-factor cap 1))))
         :hints (("Goal"
                  :use ((:instance lw-kernel-spatial-parameters (sigma 0) (step 1))
                        lw-mellin-signal-spatial-parameters
                        (:instance lw-mfq-nonnegative-product
                          (a (lw-mellin-signal-spatial-cap cap)) (b (lw-kernel-spatial-cap cap 1))))
                  :in-theory (e/d (lw-mellin-spatial-error-factor)
                                  (lw-kernel-spatial-parameters lw-mellin-signal-spatial-parameters
                                   lw-mellin-spatial-parameters lw-kernel-spatial-slope
                                   lw-mellin-signal-spatial-slope))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defun lw-mellin-frozen-precision (cap error)
  (min 1 (lw-mellin-integral-precision cap error)))

(defthm lw-mellin-frozen-precision-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-frozen-precision cap error))
                (< 0 (lw-mellin-frozen-precision cap error))
                (<= (lw-mellin-frozen-precision cap error) 1)
                (<= (lw-mellin-frozen-precision cap error) (lw-mellin-integral-precision cap error))))
  :hints (("Goal"
           :use ((:instance lw-mellin-integral-precision-valid (sigma 0) (height 0)))
           :in-theory (disable lw-mellin-integral-precision-valid)
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-frozen-precision)))

(local (defthm lw-mfq-joint-budget
         (implies (and (rationalp cap) (<= 0 cap) (rationalp kernel) (<= 0 kernel)
                       (rationalp factor) (<= kernel factor)
                       (rationalp xi) (<= 0 xi) (rationalp chi) (<= 0 chi) (<= chi xi)
                       (rationalp error) (<= (* cap factor xi) (/ error 4)))
                  (<= (* cap kernel (+ xi chi)) (/ error 2)))
         :hints (("Goal"
                  :use ((:instance lw-mfq-nonnegative-product (a cap) (b xi))
                        (:instance lw-mfq-nonnegative-product (a cap) (b kernel))
                        (:instance lw-mfq-multiply-order (a kernel) (b factor) (factor (* cap xi)))
                        (:instance lw-mfq-multiply-order (a chi) (b xi) (factor (* cap kernel))))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-frozen-joint-budget
  (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
           (<= (* cap (lw-kernel-spatial-cap cap 1)
                  (+ (lw-mellin-integral-precision cap error) (lw-mellin-frozen-precision cap error)))
               (/ error 2)))
  :hints (("Goal"
           :use (lw-mfq-spatial-factor-dominates
                 lw-mellin-frozen-precision-valid
                 (:instance lw-mellin-integral-precision-valid (sigma 0) (height 0))
                 (:instance lw-mfq-joint-budget
                   (kernel (lw-kernel-spatial-cap cap 1)) (factor (lw-mellin-spatial-error-factor cap 1))
                   (xi (lw-mellin-integral-precision cap error)) (chi (lw-mellin-frozen-precision cap error))))
           :in-theory (disable lw-mellin-frozen-precision-valid lw-mellin-integral-precision-valid)
           :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-frozen-bounded (cap sigma height index error)
  (lw-mellin-frozen-dyadic cap 0 cap (lw-mellin-integral-depth cap sigma height error)
                         sigma height index (lw-mellin-frozen-precision cap error)
                         (lw-mellin-integral-precision cap error)))

(defthm lw-mellin-frozen-bounded-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-frozen-bounded cap sigma height index error)))
  :hints (("Goal"
           :use (lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                 lw-mellin-frozen-precision-valid
                 (:instance lw-mellin-frozen-dyadic-rational
                   (start 0) (end cap) (depth (lw-mellin-integral-depth cap sigma height error))
                   (model-error (lw-mellin-frozen-precision cap error))
                   (sample-error (lw-mellin-integral-precision cap error))))
           :in-theory (disable lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                               lw-mellin-frozen-precision-valid lw-mellin-frozen-dyadic-rational)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-frozen-bounded-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index error)
                            (lw-mellin-frozen-bounded cap sigma height index error))
            (/ error 2)))
  :hints (("Goal"
           :use (lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                 lw-mellin-frozen-precision-valid lw-mellin-frozen-joint-budget
                 (:instance lw-mellin-frozen-dyadic-comparison
                   (start 0) (end cap) (depth (lw-mellin-integral-depth cap sigma height error))
                   (model-error (lw-mellin-frozen-precision cap error))
                   (sample-error (lw-mellin-integral-precision cap error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index error)
                                         (lw-mellin-frozen-bounded cap sigma height index error)))
                   (radius (* cap (lw-kernel-spatial-cap cap 1)
                              (+ (lw-mellin-integral-precision cap error)
                                 (lw-mellin-frozen-precision cap error))))
                   (cap (/ error 2))))
           :in-theory (e/d (lw-mellin-bounded-integral)
                           (lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                            lw-mellin-frozen-precision-valid lw-mellin-frozen-joint-budget
                            lw-mellin-frozen-dyadic-comparison))
           :nonlinearp nil :do-not-induct t)))


