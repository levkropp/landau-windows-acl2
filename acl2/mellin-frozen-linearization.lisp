(in-package "ACL2")

(include-book "mellin-frozen-quadrature")

; Exact finite interchange of the prime sum with dyadic quadrature.
; Every logarithmic breakpoint and primitive coefficient stays fixed.
; Endpoint normalization of each component is a separate obligation.

(local (in-theory
        (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
                 lw-smoothed-ramp-log-error lw-log-ramp-extension lw-smoothed-ramp-extension-sum
                 lw-signal-exponential-value lw-signal-exponential-linear
                 lw-signal-exponential-precision lw-signal-exponential-cost
                 lw-log-signal-ramp-count lw-log-signal-spatial-cap lw-signal-count
                 lw-mellin-sample lw-mellin-frozen-sample lw-mellin-frozen-dyadic
                 lw-mellin-weight lw-mellin-phase
                 lw-mellin-integral-depth lw-mellin-integral-precision
                 lw-mellin-bounded-integral lw-mellin-frozen-bounded lw-mellin-frozen-precision
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp)))

(local (defthm lw-mfl-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mfl-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mfl-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mfl-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mfl-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mfl-times-negative (a b) (b a)))
                         :in-theory (disable lw-mfl-times-negative)))))

(defun lw-mellin-frozen-basis-dyadic
  (kind start end depth sigma height index exp-error prime log-error sample-error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (let* ((point (car (lw-exp-bounds start exp-error)))
             (scalar (cond ((equal kind 0) point)
                           ((equal kind 1) (* start point))
                           ((equal kind 3) 1)
                           (t (lw-log-ramp-extension start point prime log-error)))))
        (lw-complex-scale
         (* (- end start) scalar (lw-mellin-weight start sigma index 1 sample-error))
         (lw-mellin-phase start sigma height index 1 sample-error)))
    (let ((middle (/ (+ start end) 2)))
      (lw-complex-add
       (lw-mellin-frozen-basis-dyadic
        kind start middle (- depth 1) sigma height index exp-error prime log-error sample-error)
       (lw-mellin-frozen-basis-dyadic
        kind middle end (- depth 1) sigma height index exp-error prime log-error sample-error)))))

(defun lw-mellin-frozen-prime-dyadic
  (start end depth sigma height index count total model-error primitive-error sample-error)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal count 1))
      (cons 0 0)
    (lw-complex-add
     (lw-complex-scale
      (car (lw-mangoldt-bounds count primitive-error))
      (lw-mellin-frozen-basis-dyadic
       2 start end depth sigma height index primitive-error count
       (lw-smoothed-ramp-log-error count total model-error) sample-error))
     (lw-mellin-frozen-prime-dyadic
      start end depth sigma height index (- count 1) total model-error primitive-error sample-error))))

(defthm lw-mellin-frozen-prime-dyadic-leaf
  (implies (zp depth)
   (equal
   (lw-mellin-frozen-prime-dyadic start end depth sigma height index count total model-error primitive-error sample-error)
   (lw-complex-scale
    (* (- end start)
       (lw-smoothed-ramp-extension-sum
        start (car (lw-exp-bounds start primitive-error)) count total model-error primitive-error)
       (lw-mellin-weight start sigma index 1 sample-error))
    (lw-mellin-phase start sigma height index 1 sample-error))))
  :hints (("Goal"
           :induct (lw-mellin-frozen-prime-dyadic
                    start end depth sigma height index count total model-error primitive-error sample-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-smoothed-ramp-extension-sum
                              lw-complex-add lw-complex-scale))))

(defthm lw-mellin-frozen-prime-dyadic-refinement
  (implies (not (zp depth))
           (equal
            (lw-mellin-frozen-prime-dyadic
             start end depth sigma height index count total model-error primitive-error sample-error)
            (lw-complex-add
             (lw-mellin-frozen-prime-dyadic
              start (/ (+ start end) 2) (- depth 1) sigma height index count total
              model-error primitive-error sample-error)
             (lw-mellin-frozen-prime-dyadic
              (/ (+ start end) 2) end (- depth 1) sigma height index count total
              model-error primitive-error sample-error))))
  :hints (("Goal"
           :induct (lw-mellin-frozen-prime-dyadic
                    start end depth sigma height index count total model-error primitive-error sample-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-complex-add lw-complex-scale))))

(local (in-theory (disable lw-mellin-frozen-prime-dyadic)))

(defun lw-mellin-frozen-linear-dyadic (cap start end depth sigma height index model-error sample-error)
  (let ((count (lw-log-signal-ramp-count cap))
        (epsilon (lw-signal-exponential-precision cap model-error)))
    (lw-complex-add
     (lw-complex-sub
      (lw-mellin-frozen-prime-dyadic
       start end depth sigma height index count count model-error epsilon sample-error)
      (lw-mellin-frozen-basis-dyadic
       1 start end depth sigma height index epsilon 2 1 sample-error))
     (lw-complex-scale
      (+ 1 (car (lw-euler-bounds epsilon)))
      (lw-mellin-frozen-basis-dyadic
       0 start end depth sigma height index epsilon 2 1 sample-error)))))

(defthm lw-mellin-frozen-dyadic-linearization
  (equal
   (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
   (lw-mellin-frozen-linear-dyadic cap start end depth sigma height index model-error sample-error))
  :hints (("Goal"
           :induct (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error sample-error)
           :in-theory (enable lw-mellin-frozen-dyadic lw-mellin-frozen-basis-dyadic
                              lw-signal-exponential-value lw-signal-exponential-linear
                              lw-mellin-frozen-sample
                              lw-complex-add lw-complex-sub lw-complex-scale))))

(local (in-theory (disable lw-mellin-frozen-linear-dyadic lw-mellin-frozen-basis-dyadic)))

(defun lw-mellin-frozen-linear-bounded (cap sigma height index error)
  (lw-mellin-frozen-linear-dyadic
   cap 0 cap (lw-mellin-integral-depth cap sigma height error) sigma height index
   (lw-mellin-frozen-precision cap error) (lw-mellin-integral-precision cap error)))

(defthm lw-mellin-frozen-bounded-linearization
  (equal (lw-mellin-frozen-bounded cap sigma height index error)
         (lw-mellin-frozen-linear-bounded cap sigma height index error))
  :hints (("Goal" :in-theory (enable lw-mellin-frozen-bounded))))

(defthm lw-mellin-frozen-linear-bounded-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-frozen-linear-bounded cap sigma height index error)))
  :hints (("Goal"
           :use (lw-mellin-frozen-bounded-rational)
           :in-theory (disable lw-mellin-frozen-linear-bounded lw-mellin-frozen-bounded-rational)
           :do-not-induct t)))

(defthm lw-mellin-frozen-linear-bounded-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index error)
                            (lw-mellin-frozen-linear-bounded cap sigma height index error))
            (/ error 2)))
  :hints (("Goal"
           :use (lw-mellin-frozen-bounded-comparison)
           :in-theory (disable lw-mellin-frozen-linear-bounded lw-mellin-frozen-bounded-comparison)
           :do-not-induct t)))

(defthm lw-mellin-frozen-ramp-before-cutpoint
  (implies
   (and (rationalp start) (rationalp end) (<= start end)
        (< end (car (lw-log-bounds prime log-error))))
   (equal
    (lw-mellin-frozen-basis-dyadic
     2 start end depth sigma height index exp-error prime log-error sample-error)
    (cons 0 0)))
  :hints (("Goal"
           :induct (lw-mellin-frozen-basis-dyadic
                    2 start end depth sigma height index exp-error prime log-error sample-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-log-ramp-extension
                              lw-complex-add lw-complex-scale))))

(defthm lw-mellin-frozen-ramp-after-cutpoint
  (implies
   (and (rationalp start) (rationalp end) (<= start end)
        (<= (car (lw-log-bounds prime log-error)) start))
   (equal
    (lw-mellin-frozen-basis-dyadic
     2 start end depth sigma height index exp-error prime log-error sample-error)
    (lw-complex-sub
     (lw-complex-scale
      (/ prime)
      (lw-mellin-frozen-basis-dyadic
       0 start end depth sigma height index exp-error prime log-error sample-error))
     (lw-mellin-frozen-basis-dyadic
      3 start end depth sigma height index exp-error prime log-error sample-error))))
  :hints (("Goal"
           :induct (lw-mellin-frozen-basis-dyadic
                    2 start end depth sigma height index exp-error prime log-error sample-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-log-ramp-extension
                              lw-complex-add lw-complex-sub lw-complex-scale))))
