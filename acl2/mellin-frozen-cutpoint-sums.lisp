(in-package "ACL2")

(include-book "mellin-frozen-cutpoints")

; Sum the breakpoint-insertion errors with the actual Mangoldt weights.
; The frozen model's existing precision budget absorbs every crossing.

(local (in-theory
        (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
                 lw-exp-lipschitz-cap lw-log-ramp-extension
                 lw-mellin-weight lw-mellin-phase lw-mellin-frozen-basis-dyadic
                 lw-mellin-clipped-basis-dyadic lw-mellin-clipped-ramp-linearization
                 lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint
                 lw-mellin-frozen-prime-dyadic lw-mellin-frozen-linear-dyadic
                 lw-mellin-frozen-dyadic lw-mellin-frozen-dyadic-linearization
                 lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error
                 lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
                 lw-signal-exponential-cost lw-signal-exponential-precision
                 lw-mellin-cutpoint-jump lw-kernel-spatial-cap
                 lw-mellin-frozen-bounded lw-mellin-frozen-linear-bounded
                 lw-mellin-frozen-bounded-linearization
                 lw-mellin-bounded-integral lw-mellin-integral-depth lw-mellin-integral-precision
                 lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                 lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope lw-kernel-spatial-slope
                 lw-mellin-frozen-precision
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-disk-enlarge lw-disk-enlarge
                 lw-halved-width)))

(local (defthm lw-mcs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mcs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mcs-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mcs-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mcs-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mcs-times-negative (a b) (b a)))
                         :in-theory (disable lw-mcs-times-negative)))))
(local (defthm lw-mcs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mcs-left-commutes)))))
(local (defthm lw-mcs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mcs-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mcs-weighted-jump
         (implies
          (and (rationalp weight) (<= 0 weight) (rationalp prime) (< 0 prime) (<= weight prime)
               (rationalp jump) (<= 0 jump) (rationalp radius)
               (<= jump (/ radius prime)) (rationalp budget) (<= radius budget))
          (<= (* weight jump) budget))
         :hints (("Goal"
                  :use ((:instance lw-mcs-multiply-order (a weight) (b prime) (factor jump))
                        (:instance lw-mcs-multiply-order (a jump) (b (/ radius prime)) (factor prime)))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mcs-unit-data
         (implies (and (natp total) (rationalp model-error) (< 0 model-error))
                  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
                       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
         :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-mcs-jump-term
         (implies
          (and (natp count) (< 1 count) (natp total)
               (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error))
          (let ((jump (lw-mellin-cutpoint-jump
                       count (lw-smoothed-ramp-log-error count total model-error) primitive-error))
                (weight (car (lw-mangoldt-bounds count primitive-error))))
            (and (rationalp (* weight jump)) (<= 0 (* weight jump))
                 (<= (* weight jump)
                     (+ (lw-smoothed-ramp-unit-error total model-error) (* 2 primitive-error))))))
         :hints (("Goal"
                  :use (lw-mcs-unit-data
                        (:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
                        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
                        (:instance lw-mellin-cutpoint-jump-rational
                          (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error))
                          (exp-error primitive-error))
                        (:instance lw-mellin-cutpoint-jump-bound
                          (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error))
                          (exp-error primitive-error))
                        (:instance lw-exp-lipschitz-cap-valid (cap count))
                        (:instance lw-mcs-nonnegative-product
                          (a (car (lw-mangoldt-bounds count primitive-error)))
                          (b (lw-mellin-cutpoint-jump count
                               (lw-smoothed-ramp-log-error count total model-error) primitive-error)))
                        (:instance lw-mcs-weighted-jump
                          (weight (car (lw-mangoldt-bounds count primitive-error)))
                          (prime count)
                          (jump (lw-mellin-cutpoint-jump count
                                 (lw-smoothed-ramp-log-error count total model-error) primitive-error))
                          (radius (+ (* (lw-exp-lipschitz-cap count)
                                        (lw-smoothed-ramp-log-error count total model-error))
                                     (* 2 primitive-error)))
                          (budget (+ (lw-smoothed-ramp-unit-error total model-error) (* 2 primitive-error)))))
                  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                                      lw-mellin-cutpoint-jump-rational lw-mellin-cutpoint-jump-bound
                                      lw-exp-lipschitz-cap-valid)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defun lw-mellin-cutpoint-jump-sum (count total model-error primitive-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1)) 0
    (+ (* (car (lw-mangoldt-bounds count primitive-error))
          (lw-mellin-cutpoint-jump count (lw-smoothed-ramp-log-error count total model-error) primitive-error))
       (lw-mellin-cutpoint-jump-sum (- count 1) total model-error primitive-error))))

(defthm lw-mellin-cutpoint-jump-sum-rational
  (implies (and (natp count) (natp total) (rationalp model-error) (< 0 model-error)
                (rationalp primitive-error) (< 0 primitive-error))
           (and (rationalp (lw-mellin-cutpoint-jump-sum count total model-error primitive-error))
                (<= 0 (lw-mellin-cutpoint-jump-sum count total model-error primitive-error))))
  :hints (("Goal" :induct (lw-mellin-cutpoint-jump-sum count total model-error primitive-error))
          (and stable-under-simplificationp
               '(:use (lw-mcs-jump-term) :do-not-induct t))))

(defthm lw-mellin-cutpoint-jump-sum-bound
  (implies (and (natp count) (natp total) (rationalp model-error) (< 0 model-error)
                (rationalp primitive-error) (< 0 primitive-error))
           (<= (lw-mellin-cutpoint-jump-sum count total model-error primitive-error)
               (* count (+ (lw-smoothed-ramp-unit-error total model-error) (* 2 primitive-error)))))
  :hints (("Goal" :induct (lw-mellin-cutpoint-jump-sum count total model-error primitive-error))
          (and stable-under-simplificationp
               '(:use (lw-mcs-jump-term lw-mcs-unit-data) :nonlinearp nil :do-not-induct t))))


(local (defthm lw-mcs-family-data
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (natp (lw-log-signal-ramp-count cap))
                       (rationalp (lw-signal-exponential-cost cap))
                       (<= (lw-log-signal-ramp-count cap) (lw-signal-exponential-cost cap))))
         :hints (("Goal"
                  :use (lw-log-signal-spatial-cap-valid
                        (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
                        (:instance lw-mcs-nonnegative-product
                          (a (+ 1 (lw-log-signal-ramp-count cap))) (b (lw-log-signal-spatial-cap cap))))
                  :in-theory (e/d (lw-signal-exponential-cost lw-log-signal-ramp-count)
                                  (lw-log-signal-spatial-cap-valid))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-cutpoint-family-jump-budget
  (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error))
           (<= (lw-mellin-cutpoint-jump-sum
                (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) error
                (lw-signal-exponential-precision cap error))
               error))
  :hints (("Goal"
           :use (lw-mcs-family-data lw-signal-exponential-parameters
                 (:instance lw-mellin-cutpoint-jump-sum-bound
                   (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
                   (model-error error) (primitive-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-mcs-multiply-order
                   (a (lw-log-signal-ramp-count cap)) (b (lw-signal-exponential-cost cap))
                   (factor (* 2 (lw-signal-exponential-precision cap error)))))
           :in-theory (disable lw-mellin-cutpoint-jump-sum lw-signal-exponential-parameters
                               lw-mellin-cutpoint-jump-sum-bound)
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-cutpoint-jump-sum)))

(local (defthm lw-mcs-scale-difference
         (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                (lw-complex-scale factor (lw-complex-sub a b)))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))
(local (defthm lw-mcs-add-differences
         (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))
(local (defthm lw-mcs-sub-self
         (equal (lw-complex-sub a a) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-mcs-zero-disk
         (lw-complex-diskp (cons 0 0) 0)
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-diskp lw-diskp)))))

(defun lw-mellin-clipped-prime-dyadic
  (start end depth sigma height index count total model-error primitive-error sample-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1))
      (cons 0 0)
    (let* ((eta (lw-smoothed-ramp-log-error count total model-error))
           (cutpoint (car (lw-log-bounds count eta))))
      (lw-complex-add
       (lw-complex-scale
        (car (lw-mangoldt-bounds count primitive-error))
        (lw-mellin-clipped-basis-dyadic
         2 start end depth cutpoint sigma height index primitive-error count eta sample-error))
       (lw-mellin-clipped-prime-dyadic
        start end depth sigma height index (- count 1) total model-error primitive-error sample-error)))))

(local (defthm lw-mcs-weighted-ramp-comparison
         (implies
          (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
               (rationalp end) (<= start end) (<= end cap) (natp depth)
               (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
               (natp count) (< 1 count) (natp total)
               (rationalp model-error) (< 0 model-error)
               (rationalp primitive-error) (< 0 primitive-error)
               (rationalp sample-error) (< 0 sample-error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-complex-scale
             (car (lw-mangoldt-bounds count primitive-error))
             (lw-mellin-frozen-basis-dyadic
              2 start end depth sigma height index primitive-error count
              (lw-smoothed-ramp-log-error count total model-error) sample-error))
            (lw-complex-scale
             (car (lw-mangoldt-bounds count primitive-error))
             (lw-mellin-clipped-basis-dyadic
              2 start end depth (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
              sigma height index primitive-error count
              (lw-smoothed-ramp-log-error count total model-error) sample-error)))
           (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
              (car (lw-mangoldt-bounds count primitive-error))
              (lw-mellin-cutpoint-jump count (lw-smoothed-ramp-log-error count total model-error) primitive-error))))
         :hints (("Goal"
                  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
                        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
                        (:instance lw-mellin-clipped-ramp-mesh-bound
                          (prime count) (exp-error primitive-error)
                          (log-error (lw-smoothed-ramp-log-error count total model-error)))
                        (:instance lw-complex-scale-disk
                          (factor (car (lw-mangoldt-bounds count primitive-error)))
                          (point (lw-complex-sub
                            (lw-mellin-frozen-basis-dyadic
                             2 start end depth sigma height index primitive-error count
                             (lw-smoothed-ramp-log-error count total model-error) sample-error)
                            (lw-mellin-clipped-basis-dyadic
                             2 start end depth
                             (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
                             sigma height index primitive-error count
                             (lw-smoothed-ramp-log-error count total model-error) sample-error)))
                          (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                                     (lw-mellin-cutpoint-jump
                                      count (lw-smoothed-ramp-log-error count total model-error) primitive-error)))))
                  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                                      lw-mellin-clipped-ramp-mesh-bound lw-complex-scale-disk)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-clipped-prime-dyadic-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (natp count) (natp total) (rationalp model-error) (< 0 model-error)
        (rationalp primitive-error) (< 0 primitive-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-frozen-prime-dyadic
      start end depth sigma height index count total model-error primitive-error sample-error)
     (lw-mellin-clipped-prime-dyadic
      start end depth sigma height index count total model-error primitive-error sample-error))
    (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
       (lw-mellin-cutpoint-jump-sum count total model-error primitive-error))))
  :hints
  (("Goal"
    :induct (lw-mellin-clipped-prime-dyadic
             start end depth sigma height index count total model-error primitive-error sample-error)
    :in-theory (enable lw-mellin-frozen-prime-dyadic lw-mellin-clipped-prime-dyadic lw-mellin-cutpoint-jump-sum))
   (and stable-under-simplificationp
        '(:use
          (lw-mcs-weighted-ramp-comparison
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-complex-scale
                (car (lw-mangoldt-bounds count primitive-error))
                (lw-mellin-frozen-basis-dyadic
                 2 start end depth sigma height index primitive-error count
                 (lw-smoothed-ramp-log-error count total model-error) sample-error))
               (lw-complex-scale
                (car (lw-mangoldt-bounds count primitive-error))
                (lw-mellin-clipped-basis-dyadic
                 2 start end depth (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
                 sigma height index primitive-error count
                 (lw-smoothed-ramp-log-error count total model-error) sample-error))))
             (right (lw-complex-sub
               (lw-mellin-frozen-prime-dyadic
                start end depth sigma height index (- count 1) total model-error primitive-error sample-error)
               (lw-mellin-clipped-prime-dyadic
                start end depth sigma height index (- count 1) total model-error primitive-error sample-error)))
             (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                        (car (lw-mangoldt-bounds count primitive-error))
                        (lw-mellin-cutpoint-jump count (lw-smoothed-ramp-log-error count total model-error) primitive-error)))
             (other-radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                              (lw-mellin-cutpoint-jump-sum (- count 1) total model-error primitive-error)))))
          :in-theory (disable lw-mellin-frozen-prime-dyadic lw-mellin-clipped-prime-dyadic
                              lw-mellin-cutpoint-jump-sum lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))

(local (in-theory (disable lw-mellin-clipped-prime-dyadic)))

(defun lw-mellin-clipped-linear-dyadic (cap start end depth sigma height index model-error sample-error)
  (let ((count (lw-log-signal-ramp-count cap))
        (epsilon (lw-signal-exponential-precision cap model-error)))
    (lw-complex-add
     (lw-complex-sub
      (lw-mellin-clipped-prime-dyadic
       start end depth sigma height index count count model-error epsilon sample-error)
      (lw-mellin-frozen-basis-dyadic
       1 start end depth sigma height index epsilon 2 1 sample-error))
     (lw-complex-scale
      (+ 1 (car (lw-euler-bounds epsilon)))
      (lw-mellin-frozen-basis-dyadic
       0 start end depth sigma height index epsilon 2 1 sample-error)))))

(local (defthm lw-mcs-family-difference
         (equal
          (lw-complex-sub
           (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
           (lw-mellin-clipped-linear-dyadic cap start end depth sigma height index model-error sample-error))
          (lw-complex-sub
           (lw-mellin-frozen-prime-dyadic
            start end depth sigma height index (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap)
            model-error (lw-signal-exponential-precision cap model-error) sample-error)
           (lw-mellin-clipped-prime-dyadic
            start end depth sigma height index (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap)
            model-error (lw-signal-exponential-precision cap model-error) sample-error)))
         :hints (("Goal"
                  :use (lw-mellin-frozen-dyadic-linearization)
                  :in-theory
                  (e/d (lw-mellin-frozen-linear-dyadic lw-mellin-clipped-linear-dyadic
                        lw-complex-sub lw-complex-add lw-complex-scale)
                       (lw-mellin-frozen-dyadic-linearization))
                  :do-not-induct t))
         :rule-classes nil))

(local (in-theory (disable lw-mellin-clipped-linear-dyadic)))

(local (defthm lw-mcs-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))
                       (<= (lw-halved-width width depth) width)))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))

(defthm lw-mellin-clipped-family-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
     (lw-mellin-clipped-linear-dyadic cap start end depth sigma height index model-error sample-error))
    (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1) model-error)))
  :hints (("Goal"
           :use (lw-mcs-family-data lw-mcs-family-difference
                 (:instance lw-signal-exponential-parameters (error model-error))
                 (:instance lw-mellin-cutpoint-family-jump-budget (error model-error))
                 (:instance lw-mellin-cutpoint-jump-sum-rational
                   (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
                   (primitive-error (lw-signal-exponential-precision cap model-error)))
                 (:instance lw-mellin-clipped-prime-dyadic-comparison
                   (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
                   (primitive-error (lw-signal-exponential-precision cap model-error)))
                 (:instance lw-mcs-mesh-data (width (- end start)))
                 (:instance lw-kernel-spatial-parameters (step 1))
                 (:instance lw-mcs-nonnegative-product
                   (a (lw-halved-width (- end start) depth)) (b (lw-kernel-spatial-cap cap 1)))
                 (:instance lw-mcs-multiply-order
                   (a (lw-mellin-cutpoint-jump-sum
                       (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap)
                       model-error (lw-signal-exponential-precision cap model-error)))
                   (b model-error) (factor (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
                     (lw-mellin-clipped-linear-dyadic cap start end depth sigma height index model-error sample-error)))
                   (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                              (lw-mellin-cutpoint-jump-sum
                               (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap)
                               model-error (lw-signal-exponential-precision cap model-error))))
                   (cap (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1) model-error))))
           :in-theory (disable lw-signal-exponential-parameters lw-mellin-cutpoint-family-jump-budget
                               lw-mellin-cutpoint-jump-sum-rational lw-mellin-clipped-prime-dyadic-comparison
                               lw-kernel-spatial-parameters)
           :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-clipped-bounded (cap sigma height index error)
  (lw-mellin-clipped-linear-dyadic
   cap 0 cap (lw-mellin-integral-depth cap sigma height error) sigma height index
   (lw-mellin-frozen-precision cap error) (lw-mellin-integral-precision cap error)))

(local (defthm lw-mcs-native-budget
         (implies
          (and (rationalp cap) (<= 0 cap) (rationalp mesh) (<= 0 mesh) (<= mesh cap)
               (rationalp kernel) (<= 0 kernel) (rationalp xi) (<= 0 xi)
               (rationalp chi) (<= 0 chi) (rationalp error)
               (<= (* cap kernel (+ xi chi)) (/ error 2)))
          (<= (* mesh kernel chi) (/ error 2)))
         :hints (("Goal"
                  :use ((:instance lw-mcs-nonnegative-product (a kernel) (b chi))
                        (:instance lw-mcs-nonnegative-product (a cap) (b kernel))
                        (:instance lw-mcs-multiply-order (a mesh) (b cap) (factor (* kernel chi)))
                        (:instance lw-mcs-multiply-order (a chi) (b (+ xi chi)) (factor (* cap kernel))))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-clipped-bounded-frozen-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
        (natp index) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-frozen-bounded cap sigma height index error)
     (lw-mellin-clipped-bounded cap sigma height index error))
    (/ error 2)))
  :hints (("Goal"
           :use (lw-mellin-frozen-precision-valid lw-mellin-integral-precision-valid
                 lw-mellin-integral-depth-adequate lw-mellin-frozen-joint-budget
                 (:instance lw-mcs-mesh-data
                   (width cap) (depth (lw-mellin-integral-depth cap sigma height error)))
                 (:instance lw-kernel-spatial-parameters (step 1))
                 (:instance lw-mellin-clipped-family-comparison
                   (start 0) (end cap) (depth (lw-mellin-integral-depth cap sigma height error))
                   (model-error (lw-mellin-frozen-precision cap error))
                   (sample-error (lw-mellin-integral-precision cap error)))
                 (:instance lw-mcs-native-budget
                   (mesh (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error)))
                   (kernel (lw-kernel-spatial-cap cap 1))
                   (xi (lw-mellin-integral-precision cap error)) (chi (lw-mellin-frozen-precision cap error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-frozen-bounded cap sigma height index error)
                     (lw-mellin-clipped-bounded cap sigma height index error)))
                   (radius (* (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error))
                              (lw-kernel-spatial-cap cap 1) (lw-mellin-frozen-precision cap error)))
                   (cap (/ error 2))))
           :in-theory
           (e/d (lw-mellin-frozen-bounded)
                (lw-mellin-frozen-precision-valid lw-mellin-integral-precision-valid
                 lw-mellin-integral-depth-adequate lw-mellin-frozen-joint-budget
                 lw-kernel-spatial-parameters lw-mellin-clipped-family-comparison))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-clipped-bounded)))

(local (defthm lw-mcs-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-mcs-difference-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mcs-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mcs-halves
         (implies (rationalp error) (equal (+ (/ error 2) (/ error 2)) error))))

(defthm lw-mellin-clipped-bounded-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
        (natp index) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-bounded-integral cap sigma height index error)
     (lw-mellin-clipped-bounded cap sigma height index error))
    error))
  :hints (("Goal"
           :use (lw-mcs-halves lw-mellin-frozen-bounded-comparison lw-mellin-clipped-bounded-frozen-comparison
                 (:instance lw-mcs-difference-triangle
                   (left (lw-mellin-bounded-integral cap sigma height index error))
                   (middle (lw-mellin-frozen-bounded cap sigma height index error))
                   (right (lw-mellin-clipped-bounded cap sigma height index error))
                   (radius (/ error 2)) (other-radius (/ error 2))))
           :in-theory (disable lw-mcs-halves lw-mellin-frozen-bounded-comparison
                               lw-mellin-clipped-bounded-frozen-comparison)
           :nonlinearp nil :do-not-induct t)))
