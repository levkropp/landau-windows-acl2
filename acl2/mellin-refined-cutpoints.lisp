(in-package "ACL2")

(include-book "mellin-frozen-cutpoint-sums")

(include-book "mellin-refined-linearization")

; Insert fixed logarithmic breakpoints with independent exponential sampling.
; The construction cap is independent of the enclosing quadrature interval.

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
                 lw-halved-width
                 lw-mellin-refined-dyadic lw-mellin-refined-linear-dyadic
                 lw-mellin-refined-prime-dyadic lw-mellin-refined-dyadic-linearization)))

(local (defthm lw-mrc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mrc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mrc-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrc-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mrc-times-negative (a b) (b a)))
                         :in-theory (disable lw-mrc-times-negative)))))

(local (defthm lw-mrc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mrc-left-commutes)))))

(local (defthm lw-mrc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrc-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrc-weighted-jump
         (implies
          (and (rationalp weight) (<= 0 weight) (rationalp prime) (< 0 prime) (<= weight prime)
               (rationalp jump) (<= 0 jump) (rationalp radius)
               (<= jump (/ radius prime)) (rationalp budget) (<= radius budget))
          (<= (* weight jump) budget))
         :hints (("Goal"
                  :use ((:instance lw-mrc-multiply-order (a weight) (b prime) (factor jump))
                        (:instance lw-mrc-multiply-order (a jump) (b (/ radius prime)) (factor prime)))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mrc-unit-data
         (implies (and (natp total) (rationalp model-error) (< 0 model-error))
                  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
                       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
         :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-mrc-jump-term
         (implies
          (and (natp count) (< 1 count) (natp total)
               (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error))
          (let ((jump (lw-mellin-cutpoint-jump
                       count (lw-smoothed-ramp-log-error count total model-error) exp-error))
                (weight (car (lw-mangoldt-bounds count primitive-error))))
            (and (rationalp (* weight jump)) (<= 0 (* weight jump))
                 (<= (* weight jump)
                     (+ (lw-smoothed-ramp-unit-error total model-error) (* 2 exp-error))))))
         :hints (("Goal"
                  :use (lw-mrc-unit-data
                        (:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
                        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
                        (:instance lw-mellin-cutpoint-jump-rational
                          (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error))
                          (exp-error exp-error))
                        (:instance lw-mellin-cutpoint-jump-bound
                          (prime count) (log-error (lw-smoothed-ramp-log-error count total model-error))
                          (exp-error exp-error))
                        (:instance lw-exp-lipschitz-cap-valid (cap count))
                        (:instance lw-mrc-nonnegative-product
                          (a (car (lw-mangoldt-bounds count primitive-error)))
                          (b (lw-mellin-cutpoint-jump count
                               (lw-smoothed-ramp-log-error count total model-error) exp-error)))
                        (:instance lw-mrc-weighted-jump
                          (weight (car (lw-mangoldt-bounds count primitive-error)))
                          (prime count)
                          (jump (lw-mellin-cutpoint-jump count
                                 (lw-smoothed-ramp-log-error count total model-error) exp-error))
                          (radius (+ (* (lw-exp-lipschitz-cap count)
                                        (lw-smoothed-ramp-log-error count total model-error))
                                     (* 2 exp-error)))
                          (budget (+ (lw-smoothed-ramp-unit-error total model-error) (* 2 exp-error)))))
                  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                                      lw-mellin-cutpoint-jump-rational lw-mellin-cutpoint-jump-bound
                                      lw-exp-lipschitz-cap-valid)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defun lw-mellin-refined-cutpoint-jump-sum (count total model-error primitive-error exp-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1)) 0
    (+ (* (car (lw-mangoldt-bounds count primitive-error))
          (lw-mellin-cutpoint-jump count (lw-smoothed-ramp-log-error count total model-error) exp-error))
       (lw-mellin-refined-cutpoint-jump-sum (- count 1) total model-error primitive-error exp-error))))

(defthm lw-mellin-refined-cutpoint-jump-sum-rational
  (implies (and (natp count) (natp total) (rationalp model-error) (< 0 model-error)
                (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error))
           (and (rationalp (lw-mellin-refined-cutpoint-jump-sum count total model-error primitive-error exp-error))
                (<= 0 (lw-mellin-refined-cutpoint-jump-sum count total model-error primitive-error exp-error))))
  :hints (("Goal" :induct (lw-mellin-refined-cutpoint-jump-sum count total model-error primitive-error exp-error))
          (and stable-under-simplificationp
               '(:use (lw-mrc-jump-term) :do-not-induct t))))

(defthm lw-mellin-refined-cutpoint-jump-sum-bound
  (implies (and (natp count) (natp total) (rationalp model-error) (< 0 model-error)
                (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error))
           (<= (lw-mellin-refined-cutpoint-jump-sum count total model-error primitive-error exp-error)
               (* count (+ (lw-smoothed-ramp-unit-error total model-error) (* 2 exp-error)))))
  :hints (("Goal" :induct (lw-mellin-refined-cutpoint-jump-sum count total model-error primitive-error exp-error))
          (and stable-under-simplificationp
               '(:use (lw-mrc-jump-term lw-mrc-unit-data) :nonlinearp nil :do-not-induct t))))

(local (defthm lw-mrc-family-data
         (implies (and (rationalp cap) (<= 0 cap))
                  (and (natp (lw-log-signal-ramp-count cap))
                       (rationalp (lw-signal-exponential-cost cap))
                       (<= (lw-log-signal-ramp-count cap) (lw-signal-exponential-cost cap))))
         :hints (("Goal"
                  :use (lw-log-signal-spatial-cap-valid
                        (:instance lw-signal-count-natural (value (lw-log-signal-spatial-cap cap)))
                        (:instance lw-mrc-nonnegative-product
                          (a (+ 1 (lw-log-signal-ramp-count cap))) (b (lw-log-signal-spatial-cap cap))))
                  :in-theory (e/d (lw-signal-exponential-cost lw-log-signal-ramp-count)
                                  (lw-log-signal-spatial-cap-valid))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-refined-cutpoint-family-jump-budget
  (implies (and (rationalp cap) (<= 0 cap) (rationalp error) (< 0 error)
                (rationalp exp-error) (< 0 exp-error)
                (<= exp-error (lw-signal-exponential-precision cap error)))
           (<= (lw-mellin-refined-cutpoint-jump-sum
                (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap) error
                (lw-signal-exponential-precision cap error) exp-error)
               error))
  :hints (("Goal"
           :use (lw-mrc-family-data lw-signal-exponential-parameters
                 (:instance lw-mellin-refined-cutpoint-jump-sum-bound
                   (count (lw-log-signal-ramp-count cap)) (total (lw-log-signal-ramp-count cap))
                   (model-error error) (primitive-error (lw-signal-exponential-precision cap error)))
                 (:instance lw-mrc-multiply-order
                   (a (lw-log-signal-ramp-count cap)) (b (lw-signal-exponential-cost cap))
                   (factor (* 2 (lw-signal-exponential-precision cap error))))
                 (:instance lw-mrc-multiply-order
                   (a exp-error) (b (lw-signal-exponential-precision cap error))
                   (factor (* 2 (lw-log-signal-ramp-count cap)))))
           :in-theory (disable lw-mellin-refined-cutpoint-jump-sum lw-signal-exponential-parameters
                               lw-mellin-refined-cutpoint-jump-sum-bound)
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-refined-cutpoint-jump-sum)))

(local (defthm lw-mrc-scale-difference
         (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                (lw-complex-scale factor (lw-complex-sub a b)))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mrc-add-differences
         (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(local (defthm lw-mrc-sub-self
         (equal (lw-complex-sub a a) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))

(local (defthm lw-mrc-zero-disk
         (lw-complex-diskp (cons 0 0) 0)
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-diskp lw-diskp)))))

(defun lw-mellin-refined-clipped-prime-dyadic
  (start end depth sigma height index count total model-error primitive-error sample-error exp-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1))
      (cons 0 0)
    (let* ((eta (lw-smoothed-ramp-log-error count total model-error))
           (cutpoint (car (lw-log-bounds count eta))))
      (lw-complex-add
       (lw-complex-scale
        (car (lw-mangoldt-bounds count primitive-error))
        (lw-mellin-clipped-basis-dyadic
         2 start end depth cutpoint sigma height index exp-error count eta sample-error))
       (lw-mellin-refined-clipped-prime-dyadic
        start end depth sigma height index (- count 1) total model-error primitive-error sample-error exp-error)))))

(local (defthm lw-mrc-weighted-ramp-comparison
         (implies
          (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
               (rationalp end) (<= start end) (<= end cap) (natp depth)
               (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
               (natp count) (< 1 count) (natp total)
               (rationalp model-error) (< 0 model-error)
               (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error)
               (rationalp sample-error) (< 0 sample-error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-complex-scale
             (car (lw-mangoldt-bounds count primitive-error))
             (lw-mellin-frozen-basis-dyadic
              2 start end depth sigma height index exp-error count
              (lw-smoothed-ramp-log-error count total model-error) sample-error))
            (lw-complex-scale
             (car (lw-mangoldt-bounds count primitive-error))
             (lw-mellin-clipped-basis-dyadic
              2 start end depth (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
              sigma height index exp-error count
              (lw-smoothed-ramp-log-error count total model-error) sample-error)))
           (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
              (car (lw-mangoldt-bounds count primitive-error))
              (lw-mellin-cutpoint-jump count (lw-smoothed-ramp-log-error count total model-error) exp-error))))
         :hints (("Goal"
                  :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
                        (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
                        (:instance lw-mellin-clipped-ramp-mesh-bound
                          (prime count) (exp-error exp-error)
                          (log-error (lw-smoothed-ramp-log-error count total model-error)))
                        (:instance lw-complex-scale-disk
                          (factor (car (lw-mangoldt-bounds count primitive-error)))
                          (point (lw-complex-sub
                            (lw-mellin-frozen-basis-dyadic
                             2 start end depth sigma height index exp-error count
                             (lw-smoothed-ramp-log-error count total model-error) sample-error)
                            (lw-mellin-clipped-basis-dyadic
                             2 start end depth
                             (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
                             sigma height index exp-error count
                             (lw-smoothed-ramp-log-error count total model-error) sample-error)))
                          (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                                     (lw-mellin-cutpoint-jump
                                      count (lw-smoothed-ramp-log-error count total model-error) exp-error)))))
                  :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse
                                      lw-mellin-clipped-ramp-mesh-bound lw-complex-scale-disk)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-refined-clipped-prime-dyadic-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (natp count) (natp total) (rationalp model-error) (< 0 model-error)
        (rationalp primitive-error) (< 0 primitive-error) (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-refined-prime-dyadic
      start end depth sigma height index count total model-error primitive-error sample-error exp-error)
     (lw-mellin-refined-clipped-prime-dyadic
      start end depth sigma height index count total model-error primitive-error sample-error exp-error))
    (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
       (lw-mellin-refined-cutpoint-jump-sum count total model-error primitive-error exp-error))))
  :hints
  (("Goal"
    :induct (lw-mellin-refined-clipped-prime-dyadic
             start end depth sigma height index count total model-error primitive-error sample-error exp-error)
    :in-theory (enable lw-mellin-refined-prime-dyadic lw-mellin-refined-clipped-prime-dyadic lw-mellin-refined-cutpoint-jump-sum))
   (and stable-under-simplificationp
        '(:use
          (lw-mrc-weighted-ramp-comparison
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-complex-scale
                (car (lw-mangoldt-bounds count primitive-error))
                (lw-mellin-frozen-basis-dyadic
                 2 start end depth sigma height index exp-error count
                 (lw-smoothed-ramp-log-error count total model-error) sample-error))
               (lw-complex-scale
                (car (lw-mangoldt-bounds count primitive-error))
                (lw-mellin-clipped-basis-dyadic
                 2 start end depth (car (lw-log-bounds count (lw-smoothed-ramp-log-error count total model-error)))
                 sigma height index exp-error count
                 (lw-smoothed-ramp-log-error count total model-error) sample-error))))
             (right (lw-complex-sub
               (lw-mellin-refined-prime-dyadic
                start end depth sigma height index (- count 1) total model-error primitive-error sample-error exp-error)
               (lw-mellin-refined-clipped-prime-dyadic
                start end depth sigma height index (- count 1) total model-error primitive-error sample-error exp-error)))
             (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                        (car (lw-mangoldt-bounds count primitive-error))
                        (lw-mellin-cutpoint-jump count (lw-smoothed-ramp-log-error count total model-error) exp-error)))
             (other-radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                              (lw-mellin-refined-cutpoint-jump-sum (- count 1) total model-error primitive-error exp-error)))))
          :in-theory (disable lw-mellin-refined-prime-dyadic lw-mellin-refined-clipped-prime-dyadic
                              lw-mellin-refined-cutpoint-jump-sum lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))

(local (in-theory (disable lw-mellin-refined-clipped-prime-dyadic)))

(defun lw-mellin-refined-clipped-linear-dyadic (cap start end depth sigma height index model-error sample-error exp-error)
  (let ((count (lw-log-signal-ramp-count cap))
        (epsilon (lw-signal-exponential-precision cap model-error)))
    (lw-complex-add
     (lw-complex-sub
      (lw-mellin-refined-clipped-prime-dyadic
       start end depth sigma height index count count model-error epsilon sample-error exp-error)
      (lw-mellin-frozen-basis-dyadic
       1 start end depth sigma height index exp-error 2 1 sample-error))
     (lw-complex-scale
      (+ 1 (car (lw-euler-bounds epsilon)))
      (lw-mellin-frozen-basis-dyadic
       0 start end depth sigma height index exp-error 2 1 sample-error)))))

(local (defthm lw-mrc-family-difference
         (equal
          (lw-complex-sub
           (lw-mellin-refined-dyadic cap start end depth sigma height index model-error sample-error exp-error)
           (lw-mellin-refined-clipped-linear-dyadic cap start end depth sigma height index model-error sample-error exp-error))
          (lw-complex-sub
           (lw-mellin-refined-prime-dyadic
            start end depth sigma height index (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap)
            model-error (lw-signal-exponential-precision cap model-error) sample-error exp-error)
           (lw-mellin-refined-clipped-prime-dyadic
            start end depth sigma height index (lw-log-signal-ramp-count cap) (lw-log-signal-ramp-count cap)
            model-error (lw-signal-exponential-precision cap model-error) sample-error exp-error)))
         :hints (("Goal"
                  :use (lw-mellin-refined-dyadic-linearization)
                  :in-theory
                  (e/d (lw-mellin-refined-linear-dyadic lw-mellin-refined-clipped-linear-dyadic
                        lw-complex-sub lw-complex-add lw-complex-scale)
                       (lw-mellin-refined-dyadic-linearization))
                  :do-not-induct t))
         :rule-classes nil))

(local (in-theory (disable lw-mellin-refined-clipped-linear-dyadic)))

(local (defthm lw-mrc-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))
                       (<= (lw-halved-width width depth) width)))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))

(defthm lw-mellin-refined-clipped-family-comparison
  (implies
   (and (rationalp model-cap) (<= 0 model-cap)
        (rationalp exp-error) (< 0 exp-error)
        (<= exp-error (lw-signal-exponential-precision model-cap model-error))
        (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (rationalp model-error) (< 0 model-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-refined-dyadic model-cap start end depth sigma height index model-error sample-error exp-error)
     (lw-mellin-refined-clipped-linear-dyadic model-cap start end depth sigma height index model-error sample-error exp-error))
    (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1) model-error)))
  :hints (("Goal"
           :use ((:instance lw-mrc-family-data (cap model-cap))
                 (:instance lw-mrc-family-difference (cap model-cap))
                 (:instance lw-signal-exponential-parameters (cap model-cap) (error model-error))
                 (:instance lw-mellin-refined-cutpoint-family-jump-budget (cap model-cap) (error model-error))
                 (:instance lw-mellin-refined-cutpoint-jump-sum-rational
                   (count (lw-log-signal-ramp-count model-cap)) (total (lw-log-signal-ramp-count model-cap))
                   (primitive-error (lw-signal-exponential-precision model-cap model-error)))
                 (:instance lw-mellin-refined-clipped-prime-dyadic-comparison
                   (count (lw-log-signal-ramp-count model-cap)) (total (lw-log-signal-ramp-count model-cap))
                   (primitive-error (lw-signal-exponential-precision model-cap model-error)))
                 (:instance lw-mrc-mesh-data (width (- end start)))
                 (:instance lw-kernel-spatial-parameters (step 1))
                 (:instance lw-mrc-nonnegative-product
                   (a (lw-halved-width (- end start) depth)) (b (lw-kernel-spatial-cap cap 1)))
                 (:instance lw-mrc-multiply-order
                   (a (lw-mellin-refined-cutpoint-jump-sum
                       (lw-log-signal-ramp-count model-cap) (lw-log-signal-ramp-count model-cap)
                       model-error (lw-signal-exponential-precision model-cap model-error) exp-error))
                   (b model-error) (factor (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-refined-dyadic model-cap start end depth sigma height index model-error sample-error exp-error)
                     (lw-mellin-refined-clipped-linear-dyadic model-cap start end depth sigma height index model-error sample-error exp-error)))
                   (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                              (lw-mellin-refined-cutpoint-jump-sum
                               (lw-log-signal-ramp-count model-cap) (lw-log-signal-ramp-count model-cap)
                               model-error (lw-signal-exponential-precision model-cap model-error) exp-error)))
                   (cap (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1) model-error))))
           :in-theory (disable lw-signal-exponential-parameters lw-mellin-refined-cutpoint-family-jump-budget
                               lw-mellin-refined-cutpoint-jump-sum-rational lw-mellin-refined-clipped-prime-dyadic-comparison
                               lw-kernel-spatial-parameters)
           :nonlinearp nil :do-not-induct t)))
