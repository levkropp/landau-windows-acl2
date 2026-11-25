(in-package "ACL2")

(include-book "mellin-frozen-linearization")

; Insert a fixed rational logarithmic breakpoint into every dyadic leaf.
; The discrepancy is confined to one crossing cell, whose total clipped
; width is bounded by the actual dyadic mesh.

(local (in-theory
        (disable lw-log-bounds lw-exp-bounds lw-euler-bounds lw-mangoldt-bounds
                 lw-exp-lipschitz-cap lw-log-ramp-extension
                 lw-kernel-spatial-cap lw-kernel-weight-bounds lw-kernel-weight-scale
                 lw-mellin-weight lw-mellin-phase lw-mellin-frozen-basis-dyadic
                 lw-mellin-frozen-prime-dyadic lw-mellin-frozen-linear-dyadic
                 lw-mellin-frozen-dyadic lw-mellin-frozen-dyadic-linearization
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-disk-enlarge lw-disk-enlarge
                 lw-halved-width)))

(local (defthm lw-mfc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mfc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mfc-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mfc-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mfc-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mfc-times-negative (a b) (b a)))
                         :in-theory (disable lw-mfc-times-negative)))))
(local (defthm lw-mfc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mfc-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-dyadic-cutpoint-width (start end depth cutpoint)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (if (and (< start cutpoint) (< cutpoint end)) (- end cutpoint) 0)
    (let ((middle (/ (+ start end) 2)))
      (+ (lw-dyadic-cutpoint-width start middle (- depth 1) cutpoint)
         (lw-dyadic-cutpoint-width middle end (- depth 1) cutpoint)))))

(defthm lw-dyadic-cutpoint-width-rational
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end))
           (and (rationalp (lw-dyadic-cutpoint-width start end depth cutpoint))
                (<= 0 (lw-dyadic-cutpoint-width start end depth cutpoint))))
  :hints (("Goal" :induct (lw-dyadic-cutpoint-width start end depth cutpoint))))

(defthm lw-dyadic-cutpoint-width-outside
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end)
                (or (<= cutpoint start) (<= end cutpoint)))
           (equal (lw-dyadic-cutpoint-width start end depth cutpoint) 0))
  :hints (("Goal" :induct (lw-dyadic-cutpoint-width start end depth cutpoint))))

(local (defthm lw-mfc-midpoint-widths
         (implies (and (rationalp start) (rationalp end))
                  (and (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start)))
                       (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start)))))
         :rule-classes nil))

(local (defthm lw-mfc-half-mesh
         (implies (and (rationalp start) (rationalp end) (not (zp depth)))
                  (and
                   (equal (lw-halved-width (- (/ (+ start end) 2) start) (- depth 1))
                          (lw-halved-width (- end start) depth))
                   (equal (lw-halved-width (- end (/ (+ start end) 2)) (- depth 1))
                          (lw-halved-width (- end start) depth))))
         :hints (("Goal"
                  :use (lw-mfc-midpoint-widths
                        (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1))))
                  :expand ((lw-halved-width (- end start) depth))
                  :in-theory (disable lw-halved-width-half)))
         :rule-classes nil))

(defthm lw-dyadic-cutpoint-width-mesh-bound
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end))
           (<= (lw-dyadic-cutpoint-width start end depth cutpoint)
               (lw-halved-width (- end start) depth)))
  :hints (("Goal" :induct (lw-dyadic-cutpoint-width start end depth cutpoint)
                  :in-theory (enable lw-halved-width))
          (and stable-under-simplificationp
               '(:cases ((<= cutpoint (/ (+ start end) 2)))
                 :use (lw-mfc-half-mesh)
                 :expand ((lw-halved-width (- end start) depth))
                 :in-theory (disable lw-halved-width)))))

(defun lw-mellin-clipped-basis-dyadic
  (kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (if (<= end cutpoint)
          (cons 0 0)
        (lw-mellin-frozen-basis-dyadic
         kind (max start cutpoint) end 0 sigma height index exp-error prime log-error sample-error))
    (let ((middle (/ (+ start end) 2)))
      (lw-complex-add
       (lw-mellin-clipped-basis-dyadic
        kind start middle (- depth 1) cutpoint sigma height index exp-error prime log-error sample-error)
       (lw-mellin-clipped-basis-dyadic
        kind middle end (- depth 1) cutpoint sigma height index exp-error prime log-error sample-error)))))

(defthm lw-mellin-clipped-basis-before-cutpoint
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end) (<= end cutpoint))
           (equal
            (lw-mellin-clipped-basis-dyadic
             kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)
            (cons 0 0)))
  :hints (("Goal"
           :induct (lw-mellin-clipped-basis-dyadic
                    kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)
           :in-theory (enable lw-complex-add))))

(defthm lw-mellin-clipped-ramp-linearization
  (implies
   (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end)
        (<= (car (lw-log-bounds prime log-error)) cutpoint))
   (equal
    (lw-mellin-clipped-basis-dyadic
     2 start end depth cutpoint sigma height index exp-error prime log-error sample-error)
    (lw-complex-sub
     (lw-complex-scale
      (/ prime)
      (lw-mellin-clipped-basis-dyadic
       0 start end depth cutpoint sigma height index exp-error prime log-error sample-error))
     (lw-mellin-clipped-basis-dyadic
      3 start end depth cutpoint sigma height index exp-error prime log-error sample-error))))
  :hints (("Goal"
           :induct (lw-mellin-clipped-basis-dyadic
                    2 start end depth cutpoint sigma height index exp-error prime log-error sample-error)
           :in-theory (enable lw-mellin-frozen-basis-dyadic lw-log-ramp-extension
                              lw-complex-add lw-complex-sub lw-complex-scale))))

(local (in-theory (disable lw-mellin-clipped-basis-dyadic lw-dyadic-cutpoint-width)))

(local (defthm lw-mfc-log-data
         (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error))
                  (and (rationalp (car (lw-log-bounds prime log-error)))
                       (<= 0 (car (lw-log-bounds prime log-error)))))
         :hints (("Goal"
                  :use ((:instance lw-log-bounds-interval (value prime) (epsilon log-error))
                        (:instance lw-log-bounds-lower-coarse (value prime) (epsilon log-error)))
                  :in-theory (e/d (lw-intervalp) (lw-log-bounds-interval lw-log-bounds-lower-coarse))))
         :rule-classes nil))

(defthm lw-mellin-frozen-basis-dyadic-rational
  (implies
   (and (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (rationalp sigma) (<= 0 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp prime) (< 1 prime)
        (rationalp log-error) (< 0 log-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complexp
    (lw-mellin-frozen-basis-dyadic
     kind start end depth sigma height index exp-error prime log-error sample-error)))
  :hints (("Goal"
           :induct (lw-mellin-frozen-basis-dyadic
                    kind start end depth sigma height index exp-error prime log-error sample-error)
           :in-theory (enable (:induction lw-mellin-frozen-basis-dyadic)
                              (:definition lw-mellin-frozen-basis-dyadic)
                              lw-complexp lw-complex-add lw-complex-scale))
          (and stable-under-simplificationp
               '(:use ((:instance lw-exp-bounds-valid (value start) (epsilon exp-error))
                       (:instance lw-mellin-weight-bounded (value start) (step 1) (error sample-error))
                       (:instance lw-mellin-phase-rational (value start) (step 1) (error sample-error)))
                 :in-theory
                 (e/d (lw-complexp lw-complex-add lw-complex-scale lw-intervalp)
                      (lw-exp-bounds-valid lw-mellin-weight-bounded lw-mellin-phase-rational))
                 :do-not-induct t))))

(defthm lw-mellin-clipped-basis-dyadic-rational
  (implies
   (and (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp sigma) (<= 0 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp prime) (< 1 prime)
        (rationalp log-error) (< 0 log-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complexp
    (lw-mellin-clipped-basis-dyadic
     kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)))
  :hints (("Goal"
           :induct (lw-mellin-clipped-basis-dyadic
                    kind start end depth cutpoint sigma height index exp-error prime log-error sample-error)
           :in-theory (enable (:induction lw-mellin-clipped-basis-dyadic)
                              (:definition lw-mellin-clipped-basis-dyadic)
                              lw-complexp lw-complex-add))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-frozen-basis-dyadic-rational
                         (start (max start cutpoint)) (depth 0)))
                 :in-theory (e/d (lw-complexp lw-complex-add)
                                 (lw-mellin-frozen-basis-dyadic-rational))
                 :do-not-induct t))))

(defun lw-mellin-cutpoint-jump (prime log-error exp-error)
  (abs (- (/ (car (lw-exp-bounds (car (lw-log-bounds prime log-error)) exp-error)) prime) 1)))

(defthm lw-mellin-cutpoint-jump-rational
  (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error)
                (rationalp exp-error) (< 0 exp-error))
           (and (rationalp (lw-mellin-cutpoint-jump prime log-error exp-error))
                (<= 0 (lw-mellin-cutpoint-jump prime log-error exp-error))))
  :hints (("Goal"
           :use (lw-mfc-log-data
                 (:instance lw-exp-bounds-valid (value (car (lw-log-bounds prime log-error))) (epsilon exp-error)))
           :in-theory (e/d (lw-intervalp) (lw-exp-bounds-valid))
           :do-not-induct t)))

(local (defthm lw-mfc-divide-error
         (implies (and (rationalp y) (rationalp prime) (< 0 prime) (rationalp radius)
                       (<= (abs (- y prime)) radius))
                  (<= (abs (- (/ y prime) 1)) (/ radius prime)))
         :hints (("Goal" :use ((:instance inverse-of-* (x prime))
                              (:instance lw-mfc-multiply-order
                                (a (- y prime)) (b radius) (factor (/ prime)))
                              (:instance lw-mfc-multiply-order
                                (a (- prime y)) (b radius) (factor (/ prime))))
                         :cases ((<= y prime))
                         :in-theory (disable inverse-of-*) :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-cutpoint-jump-bound
  (implies (and (rationalp prime) (< 1 prime) (rationalp log-error) (< 0 log-error) (<= log-error 1)
                (rationalp exp-error) (< 0 exp-error))
           (<= (lw-mellin-cutpoint-jump prime log-error exp-error)
               (/ (+ (* (lw-exp-lipschitz-cap prime) log-error) (* 2 exp-error)) prime)))
  :hints (("Goal"
           :use (lw-mfc-log-data
                 (:instance lw-exp-bounds-valid (value (car (lw-log-bounds prime log-error))) (epsilon exp-error))
                 (:instance lw-exp-lipschitz-cap-valid (cap prime))
                 (:instance lw-exp-log-inverse-error (point prime))
                 (:instance lw-mfc-divide-error
                   (y (car (lw-exp-bounds (car (lw-log-bounds prime log-error)) exp-error)))
                   (radius (+ (* (lw-exp-lipschitz-cap prime) log-error) (* 2 exp-error)))))
           :in-theory (e/d (lw-intervalp)
                           (lw-exp-bounds-valid lw-exp-lipschitz-cap-valid lw-exp-log-inverse-error))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-mellin-cutpoint-jump)))

(local (defthm lw-mfc-weight-spatial
         (implies (and (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
                       (rationalp sigma) (<= 0 sigma) (natp index)
                       (rationalp sample-error) (< 0 sample-error))
                  (and (rationalp (lw-mellin-weight value sigma index 1 sample-error))
                       (<= 0 (lw-mellin-weight value sigma index 1 sample-error))
                       (<= (lw-mellin-weight value sigma index 1 sample-error) (lw-kernel-spatial-cap cap 1))))
         :hints (("Goal"
                  :use ((:instance lw-kernel-weight-bounds-valid
                          (step 1) (error (lw-mellin-kernel-error value sample-error)))
                        (:instance lw-kernel-weight-scale-spatial-cap (step 1)))
                  :in-theory
                  (e/d (lw-mellin-weight lw-intervalp)
                       (lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-spatial-cap
                        lw-mellin-kernel-error lw-kernel-weight-bounds-valid
                        lw-kernel-weight-scale-spatial-cap lw-kernel-weight-bounds-overlap))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mfc-zero-disk
         (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-diskp lw-complexp) :nonlinearp t))))
(local (defthm lw-mfc-sub-self
         (equal (lw-complex-sub point point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-mfc-zero-sub-scale
         (equal (lw-complex-sub (cons 0 0) (lw-complex-scale factor point))
                (lw-complex-scale (- factor) point))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-mfc-scaled-unit
         (implies (and (rationalp width) (<= 0 width) (rationalp scalar)
                       (rationalp weight) (<= 0 weight) (rationalp cap) (<= weight cap)
                       (lw-complex-diskp phase 1))
                  (lw-complex-diskp
                   (lw-complex-sub (cons 0 0) (lw-complex-scale (* width scalar weight) phase))
                   (* width cap (abs scalar))))
         :hints (("Goal"
                  :use ((:instance lw-complex-scale-disk
                          (point phase) (radius 1) (factor (- (* width scalar weight))))
                        (:instance lw-mfc-multiply-order
                          (a weight) (b cap) (factor (* width (abs scalar))))
                        (:instance lw-mfc-nonnegative-product (a width) (b (abs scalar)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-scale (- (* width scalar weight)) phase))
                          (radius (abs (- (* width scalar weight)))) (cap (* width cap (abs scalar)))))
                  :cases ((<= 0 scalar))
                  :in-theory (disable lw-complex-scale-disk)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mfc-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-mfc-leaf-comparison
         (implies
          (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
               (rationalp end) (<= start end) (<= end cap)
               (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
               (rationalp exp-error) (< 0 exp-error) (rationalp prime) (< 1 prime)
               (rationalp log-error) (< 0 log-error) (rationalp sample-error) (< 0 sample-error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-mellin-frozen-basis-dyadic
             2 start end 0 sigma height index exp-error prime log-error sample-error)
            (lw-mellin-clipped-basis-dyadic
             2 start end 0 (car (lw-log-bounds prime log-error))
             sigma height index exp-error prime log-error sample-error))
           (* (lw-dyadic-cutpoint-width start end 0 (car (lw-log-bounds prime log-error)))
              (lw-kernel-spatial-cap cap 1) (lw-mellin-cutpoint-jump prime log-error exp-error))))
         :hints (("Goal"
                  :use (lw-mfc-log-data
                        (:instance lw-mfc-weight-spatial (value (car (lw-log-bounds prime log-error))))
                        (:instance lw-exp-bounds-valid
                          (value (car (lw-log-bounds prime log-error))) (epsilon exp-error))
                        (:instance lw-kernel-spatial-parameters (step 1))
                        (:instance lw-mellin-phase-unit
                          (value (car (lw-log-bounds prime log-error))) (step 1) (error sample-error))
                        (:instance lw-mfc-scaled-unit
                          (width (- end (car (lw-log-bounds prime log-error))))
                          (scalar (- (/ (car (lw-exp-bounds (car (lw-log-bounds prime log-error)) exp-error)) prime) 1))
                          (weight (lw-mellin-weight (car (lw-log-bounds prime log-error)) sigma index 1 sample-error))
                          (cap (lw-kernel-spatial-cap cap 1))
                          (phase (lw-mellin-phase (car (lw-log-bounds prime log-error))
                                                  sigma height index 1 sample-error))))
                  :cases ((<= end (car (lw-log-bounds prime log-error)))
                          (<= (car (lw-log-bounds prime log-error)) start))
                  :in-theory
                  (e/d (lw-mellin-frozen-basis-dyadic lw-mellin-clipped-basis-dyadic
                        lw-log-ramp-extension lw-mellin-cutpoint-jump lw-dyadic-cutpoint-width lw-intervalp)
                       (lw-mellin-phase-unit lw-exp-bounds-valid lw-kernel-spatial-parameters
                        lw-mellin-clipped-ramp-linearization lw-mellin-frozen-ramp-after-cutpoint
                        lw-mellin-frozen-ramp-before-cutpoint))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mfc-add-differences
         (equal
          (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
          (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))

(defthm lw-mellin-clipped-ramp-comparison
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (rationalp exp-error) (< 0 exp-error) (rationalp prime) (< 1 prime)
        (rationalp log-error) (< 0 log-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-frozen-basis-dyadic
      2 start end depth sigma height index exp-error prime log-error sample-error)
     (lw-mellin-clipped-basis-dyadic
      2 start end depth (car (lw-log-bounds prime log-error))
      sigma height index exp-error prime log-error sample-error))
    (* (lw-dyadic-cutpoint-width start end depth (car (lw-log-bounds prime log-error)))
       (lw-kernel-spatial-cap cap 1) (lw-mellin-cutpoint-jump prime log-error exp-error))))
  :hints
  (("Goal"
    :induct (lw-mellin-clipped-basis-dyadic
             2 start end depth (car (lw-log-bounds prime log-error))
             sigma height index exp-error prime log-error sample-error)
    :in-theory
    (e/d ((:induction lw-mellin-clipped-basis-dyadic)
          (:definition lw-mellin-clipped-basis-dyadic) lw-mellin-frozen-basis-dyadic lw-dyadic-cutpoint-width)
         (lw-mellin-clipped-ramp-linearization
          lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint)))
   (and stable-under-simplificationp
        '(:use
          (lw-mfc-log-data lw-mfc-leaf-comparison
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-mellin-frozen-basis-dyadic
                2 start (/ (+ start end) 2) (- depth 1) sigma height index exp-error prime log-error sample-error)
               (lw-mellin-clipped-basis-dyadic
                2 start (/ (+ start end) 2) (- depth 1) (car (lw-log-bounds prime log-error))
                sigma height index exp-error prime log-error sample-error)))
             (right (lw-complex-sub
               (lw-mellin-frozen-basis-dyadic
                2 (/ (+ start end) 2) end (- depth 1) sigma height index exp-error prime log-error sample-error)
               (lw-mellin-clipped-basis-dyadic
                2 (/ (+ start end) 2) end (- depth 1) (car (lw-log-bounds prime log-error))
                sigma height index exp-error prime log-error sample-error)))
             (radius (* (lw-dyadic-cutpoint-width
                          start (/ (+ start end) 2) (- depth 1) (car (lw-log-bounds prime log-error)))
                        (lw-kernel-spatial-cap cap 1) (lw-mellin-cutpoint-jump prime log-error exp-error)))
             (other-radius (* (lw-dyadic-cutpoint-width
                                (/ (+ start end) 2) end (- depth 1) (car (lw-log-bounds prime log-error)))
                              (lw-kernel-spatial-cap cap 1) (lw-mellin-cutpoint-jump prime log-error exp-error)))))
          :expand
          ((lw-mellin-frozen-basis-dyadic
            2 start end 0 sigma height index exp-error prime log-error sample-error)
           (lw-mellin-frozen-basis-dyadic
            2 (car (lw-log-bounds prime log-error)) end 0
            sigma height index exp-error prime log-error sample-error)
           (lw-mellin-frozen-basis-dyadic
            2 (max start (car (lw-log-bounds prime log-error))) end 0
            sigma height index exp-error prime log-error sample-error)
           (lw-mellin-clipped-basis-dyadic
            2 start end 0 (car (lw-log-bounds prime log-error))
            sigma height index exp-error prime log-error sample-error)
           (lw-dyadic-cutpoint-width start end 0 (car (lw-log-bounds prime log-error))))
          :in-theory
          (disable lw-mellin-frozen-basis-dyadic lw-mellin-clipped-basis-dyadic lw-dyadic-cutpoint-width
                   lw-mellin-clipped-ramp-linearization lw-complex-add-disk
                   lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint)
          :nonlinearp nil :do-not-induct t))))

(local (defthm lw-mfc-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))

(defthm lw-mellin-clipped-ramp-mesh-bound
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (rationalp exp-error) (< 0 exp-error) (rationalp prime) (< 1 prime)
        (rationalp log-error) (< 0 log-error) (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-frozen-basis-dyadic
      2 start end depth sigma height index exp-error prime log-error sample-error)
     (lw-mellin-clipped-basis-dyadic
      2 start end depth (car (lw-log-bounds prime log-error))
      sigma height index exp-error prime log-error sample-error))
    (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
       (lw-mellin-cutpoint-jump prime log-error exp-error))))
  :hints (("Goal"
           :use (lw-mfc-log-data lw-mellin-clipped-ramp-comparison lw-mellin-cutpoint-jump-rational
                 (:instance lw-kernel-spatial-parameters (step 1))
                 (:instance lw-dyadic-cutpoint-width-mesh-bound
                   (cutpoint (car (lw-log-bounds prime log-error))))
                 (:instance lw-mfc-nonnegative-product
                   (a (lw-kernel-spatial-cap cap 1)) (b (lw-mellin-cutpoint-jump prime log-error exp-error)))
                 (:instance lw-mfc-multiply-order
                   (a (lw-dyadic-cutpoint-width start end depth (car (lw-log-bounds prime log-error))))
                   (b (lw-halved-width (- end start) depth))
                   (factor (* (lw-kernel-spatial-cap cap 1) (lw-mellin-cutpoint-jump prime log-error exp-error))))
                 (:instance lw-mfc-mesh-data (width (- end start)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-frozen-basis-dyadic
                      2 start end depth sigma height index exp-error prime log-error sample-error)
                     (lw-mellin-clipped-basis-dyadic
                      2 start end depth (car (lw-log-bounds prime log-error))
                      sigma height index exp-error prime log-error sample-error)))
                   (radius (* (lw-dyadic-cutpoint-width start end depth (car (lw-log-bounds prime log-error)))
                              (lw-kernel-spatial-cap cap 1) (lw-mellin-cutpoint-jump prime log-error exp-error)))
                   (cap (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                           (lw-mellin-cutpoint-jump prime log-error exp-error)))))
           :in-theory (disable lw-mellin-clipped-ramp-comparison lw-mellin-cutpoint-jump-rational
                               lw-kernel-spatial-parameters lw-dyadic-cutpoint-width-mesh-bound
                               lw-mellin-clipped-ramp-linearization
                               lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-clipped-ramp-computed-jump-bound
  (implies
   (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
        (rationalp exp-error) (< 0 exp-error) (rationalp prime) (< 1 prime)
        (rationalp log-error) (< 0 log-error) (<= log-error 1)
        (rationalp sample-error) (< 0 sample-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-frozen-basis-dyadic
      2 start end depth sigma height index exp-error prime log-error sample-error)
     (lw-mellin-clipped-basis-dyadic
      2 start end depth (car (lw-log-bounds prime log-error))
      sigma height index exp-error prime log-error sample-error))
    (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
       (/ (+ (* (lw-exp-lipschitz-cap prime) log-error) (* 2 exp-error)) prime))))
  :hints (("Goal"
           :use (lw-mellin-clipped-ramp-mesh-bound lw-mellin-cutpoint-jump-bound
                 (:instance lw-mfc-mesh-data (width (- end start)))
                 (:instance lw-kernel-spatial-parameters (step 1))
                 (:instance lw-exp-lipschitz-cap-valid (cap prime))
                 (:instance lw-mfc-nonnegative-product
                   (a (lw-halved-width (- end start) depth)) (b (lw-kernel-spatial-cap cap 1)))
                 (:instance lw-mfc-multiply-order
                   (a (lw-mellin-cutpoint-jump prime log-error exp-error))
                   (b (/ (+ (* (lw-exp-lipschitz-cap prime) log-error) (* 2 exp-error)) prime))
                   (factor (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-frozen-basis-dyadic
                      2 start end depth sigma height index exp-error prime log-error sample-error)
                     (lw-mellin-clipped-basis-dyadic
                      2 start end depth (car (lw-log-bounds prime log-error))
                      sigma height index exp-error prime log-error sample-error)))
                   (radius (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                              (lw-mellin-cutpoint-jump prime log-error exp-error)))
                   (cap (* (lw-halved-width (- end start) depth) (lw-kernel-spatial-cap cap 1)
                           (/ (+ (* (lw-exp-lipschitz-cap prime) log-error) (* 2 exp-error)) prime)))))
           :in-theory (disable lw-mellin-clipped-ramp-mesh-bound lw-mellin-cutpoint-jump-bound
                               lw-kernel-spatial-parameters lw-exp-lipschitz-cap-valid
                               lw-mellin-clipped-ramp-linearization
                               lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint)
           :nonlinearp nil :do-not-induct t)))
