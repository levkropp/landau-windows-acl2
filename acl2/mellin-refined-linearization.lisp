(in-package "ACL2")

(include-book "mellin-frozen-linearization")

(include-book "mellin-refined-dyadic-tail")

; Exact linearity with independent point-exponential precision.
; Coefficients and logarithmic cutpoints keep their construction precision.
; The already certified basis sampler accepts this separate point precision.

(local (in-theory
        (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
                 lw-smoothed-ramp-log-error lw-log-ramp-extension lw-smoothed-ramp-extension-sum
                 lw-signal-exponential-refined-value lw-signal-exponential-linear
                 lw-signal-exponential-precision lw-signal-exponential-cost
                 lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
                 lw-mellin-sample lw-mellin-refined-sample lw-mellin-refined-dyadic
                 lw-mellin-weight lw-mellin-phase
                 lw-mellin-integral-depth lw-mellin-integral-precision
                 lw-mellin-bounded-integral lw-mellin-frozen-bounded lw-mellin-frozen-precision
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp)))

(local (defthm lw-mrl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mrl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrl-zero-times (equal (* 0 a) 0)))

(local (defthm lw-mrl-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrl-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mrl-times-negative (a b) (b a)))
                         :in-theory (disable lw-mrl-times-negative)))))

(defun lw-mellin-refined-prime-dyadic
  (start end depth sigma height index count total model-error primitive-error sample-error exp-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1))
      (cons 0 0)
    (lw-complex-add
     (lw-complex-scale
      (car (lw-mangoldt-bounds count primitive-error))
      (lw-mellin-frozen-basis-dyadic
       2 start end depth sigma height index exp-error count
       (lw-smoothed-ramp-log-error count total model-error) sample-error))
     (lw-mellin-refined-prime-dyadic
      start end depth sigma height index (- count 1) total model-error primitive-error sample-error exp-error))))

(defthm lw-mellin-refined-prime-dyadic-leaf
  (implies (zp depth)
   (equal
   (lw-mellin-refined-prime-dyadic start end depth sigma height index count total model-error primitive-error sample-error exp-error)
   (lw-complex-scale
    (* (- end start)
       (lw-smoothed-ramp-extension-sum
        start (car (lw-exp-bounds start exp-error)) count total model-error primitive-error)
       (lw-mellin-weight start sigma index 1 sample-error))
    (lw-mellin-phase start sigma height index 1 sample-error))))
  :hints (("Goal"
           :induct (lw-mellin-refined-prime-dyadic
                    start end depth sigma height index count total model-error primitive-error sample-error exp-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-smoothed-ramp-extension-sum
                              lw-complex-add lw-complex-scale))))

(defthm lw-mellin-refined-prime-dyadic-refinement
  (implies (not (zp depth))
           (equal
            (lw-mellin-refined-prime-dyadic
             start end depth sigma height index count total model-error primitive-error sample-error exp-error)
            (lw-complex-add
             (lw-mellin-refined-prime-dyadic
              start (/ (+ start end) 2) (- depth 1) sigma height index count total
              model-error primitive-error sample-error exp-error)
             (lw-mellin-refined-prime-dyadic
              (/ (+ start end) 2) end (- depth 1) sigma height index count total
              model-error primitive-error sample-error exp-error))))
  :hints (("Goal"
           :induct (lw-mellin-refined-prime-dyadic
                    start end depth sigma height index count total model-error primitive-error sample-error exp-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-complex-add lw-complex-scale))))

(local (in-theory (disable lw-mellin-refined-prime-dyadic)))

(defun lw-mellin-refined-linear-dyadic (cap start end depth sigma height index model-error sample-error exp-error)
  (let ((count (lw-log-signal-ramp-count cap))
        (epsilon (lw-signal-exponential-precision cap model-error)))
    (lw-complex-add
     (lw-complex-sub
      (lw-mellin-refined-prime-dyadic
       start end depth sigma height index count count model-error epsilon sample-error exp-error)
      (lw-mellin-frozen-basis-dyadic
       1 start end depth sigma height index exp-error 2 1 sample-error))
     (lw-complex-scale
      (+ 1 (car (lw-euler-bounds epsilon)))
      (lw-mellin-frozen-basis-dyadic
       0 start end depth sigma height index exp-error 2 1 sample-error)))))

(defthm lw-mellin-refined-dyadic-linearization
  (equal
   (lw-mellin-refined-dyadic cap start end depth sigma height index model-error sample-error exp-error)
   (lw-mellin-refined-linear-dyadic cap start end depth sigma height index model-error sample-error exp-error))
  :hints (("Goal"
           :induct (lw-mellin-refined-dyadic cap start end depth sigma height index model-error sample-error exp-error)
           :in-theory (enable lw-mellin-refined-dyadic lw-mellin-frozen-basis-dyadic
                              lw-signal-exponential-refined-value lw-signal-exponential-linear
                              lw-mellin-refined-sample
                              lw-complex-add lw-complex-sub lw-complex-scale))))
