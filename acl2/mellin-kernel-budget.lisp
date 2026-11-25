(in-package "ACL2")

(include-book "rpow-kernel")
(include-book "kernel-quadrature")

; Bound the actual window/growth budget in the failed-search theorem by
; shifted kernels. The spatial branch is the evaluator's own exact test.
(local (in-theory
        (disable lw-log-signal-window-cap lw-log-signal-point lw-log-signal-point-valid
                 lw-rational-power lw-exp-term lw-exp-sum lw-exp-bounds lw-exp-index lw-exp-neg-bounds
                 lw-kernel-weight-scale lw-kernel-weight-precision lw-ceiling-rational
                 lw-kernel-weight-bounds-overlap
                 lw-rpow-bounds-monotone-overlap
                 lw-log-signal-growth-kernel-bound lw-log-signal-rpow-kernel-bound
                 lw-signal-precision lw-signal-precision-positive lw-rpow-bounds lw-rpow-bounds-sound
                 lw-kernel-weight-bounds lw-kernel-weight-bounds-valid
                 lw-mellin-window-cap lw-mellin-weight lw-mellin-signal-error lw-mellin-kernel-error
                 lw-mellin-component-error lw-mellin-error-budgets
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-kernel-cap-valid
                 lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-computed-window-row lw-mellin-budget lw-mellin-dyadic-window-rows
                 lw-mellin-window-budget lw-mellin-bounded-window-rows
                 lw-mellin-integral-cutoff lw-mellin-integral-depth lw-mellin-integral-precision)))

(local (defthm lw-kb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-kb-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kb-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-kb-zero-times (equal (* 0 a) 0)))
(local (defthm lw-kb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-kb-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-kb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-kb-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-log-window-kernel-cap (value signal-error sigma index step shifted-error start ceiling numerator denominator)
  (let ((point (lw-log-signal-point value signal-error)))
    (if (and (<= start point) (<= (* point point) (* start start start)))
        (* 2 (+ ceiling 1) (cdr (lw-kernel-weight-bounds value (- sigma (/ numerator denominator)) index step shifted-error)))
      (* 16 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error))))))

(defthm lw-log-window-kernel-cap-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error)
                (rationalp sigma) (<= 2 sigma) (rationalp step) (<= 0 step)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (* (lw-log-signal-window-cap value signal-error start ceiling numerator denominator)
                  (car (lw-kernel-weight-bounds value sigma index step kernel-error)))
               (lw-log-window-kernel-cap value signal-error sigma index step shifted-error start ceiling numerator denominator)))
  :hints (("Goal"
           :use ((:instance lw-log-signal-point-valid (error signal-error))
                 (:instance lw-signal-precision-positive (value (lw-log-signal-point value signal-error)) (error 1/4))
                 (:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
                 (:instance lw-log-signal-rpow-kernel-bound (rate sigma)
                   (root-error (lw-signal-precision (lw-log-signal-point value signal-error) ceiling 1/4)))
                 (:instance lw-log-signal-growth-kernel-bound (error signal-error))
                 (:instance lw-rpow-bounds-sound (value (lw-log-signal-point value signal-error))
                   (epsilon (lw-signal-precision (lw-log-signal-point value signal-error) ceiling 1/4)))
                 (:instance lw-kernel-weight-bounds-valid (error kernel-error))
                 (:instance lw-kernel-weight-bounds-valid (sigma (- sigma (/ numerator denominator))) (error shifted-error))
                 (:instance lw-kb-multiply-order
                   (a (* (car (lw-rpow-bounds (lw-log-signal-point value signal-error) numerator denominator
                              (lw-signal-precision (lw-log-signal-point value signal-error) ceiling 1/4)))
                         (car (lw-kernel-weight-bounds value sigma index step kernel-error))))
                   (b (* 2 (cdr (lw-kernel-weight-bounds value (- sigma (/ numerator denominator)) index step shifted-error))))
                   (factor (+ ceiling 1))))
           :in-theory (union-theories
                       '(lw-log-signal-window-cap lw-log-window-kernel-cap lw-intervalp natp posp
                         rationalp-* rationalp-+ associativity-of-* commutativity-of-* lw-kb-left-commutes
                         distributivity lw-kb-left-distribute associativity-of-+ commutativity-of-+
                         (:executable-counterpart binary-*) (:executable-counterpart binary-+))
                       (theory 'minimal-theory)))))

(local (in-theory (disable lw-log-window-kernel-cap lw-log-window-kernel-cap-bound)))

(defthm lw-mellin-window-cap-kernel-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 2 sigma)
                (rationalp error) (< 0 error) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (* (lw-mellin-window-cap value sigma index error start ceiling numerator denominator)
                  (lw-mellin-weight value sigma index 1 error))
               (lw-log-window-kernel-cap value (lw-mellin-signal-error value sigma index 1 error)
                                         sigma index 1 shifted-error start ceiling numerator denominator)))
  :hints (("Goal" :use ((:instance lw-mellin-error-budgets (step 1))
                        (:instance lw-log-window-kernel-cap-bound (step 1)
                          (signal-error (lw-mellin-signal-error value sigma index 1 error))
                          (kernel-error (lw-mellin-kernel-error value error))))
                  :in-theory (enable lw-mellin-window-cap lw-mellin-weight))))

(defthm lw-log-window-kernel-cap-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp signal-error) (< 0 signal-error)
                (rationalp sigma) (<= 2 sigma) (rationalp step) (<= 0 step)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (and (rationalp (lw-log-window-kernel-cap value signal-error sigma index step shifted-error start ceiling numerator denominator))
                (<= 0 (lw-log-window-kernel-cap value signal-error sigma index step shifted-error start ceiling numerator denominator))))
  :hints (("Goal" :use ((:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
                        (:instance lw-kernel-weight-bounds-valid (sigma (- sigma 2)) (error shifted-error))
                        (:instance lw-kernel-weight-bounds-valid (sigma (- sigma (/ numerator denominator))) (error shifted-error)))
                  :in-theory (enable lw-log-window-kernel-cap) :nonlinearp t)))

(local (in-theory (disable lw-mellin-signal lw-mellin-phase lw-log-window-kernel-cap-valid lw-mellin-window-cap-kernel-bound)))

(defthm lw-mellin-computed-row-budget
  (equal (lw-mellin-budget (list (lw-mellin-computed-window-row value weight sigma height index error start ceiling numerator denominator)))
         (* weight (lw-mellin-window-cap value sigma index error start ceiling numerator denominator)
            (lw-mellin-weight value sigma index 1 error)))
  :hints (("Goal" :in-theory (enable lw-mellin-budget lw-mellin-computed-window-row))))

(local (in-theory (disable lw-mellin-computed-row-budget)))

(defthm lw-mellin-computed-row-kernel-budget
  (implies (and (rationalp value) (<= 0 value) (rationalp weight) (<= 0 weight)
                (rationalp sigma) (<= 2 sigma) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-budget (list (lw-mellin-computed-window-row value weight sigma height index error start ceiling numerator denominator)))
               (* weight (lw-log-window-kernel-cap value (lw-mellin-signal-error value sigma index 1 error)
                           sigma index 1 shifted-error start ceiling numerator denominator))))
  :hints (("Goal" :use (lw-mellin-computed-row-budget lw-mellin-window-cap-kernel-bound
                        (:instance lw-mellin-error-budgets (step 1))
                        (:instance lw-log-window-kernel-cap-valid (step 1)
                          (signal-error (lw-mellin-signal-error value sigma index 1 error)))
                        (:instance lw-log-signal-window-cap-valid (error (lw-mellin-signal-error value sigma index 1 error)))
                        (:instance lw-mellin-weight-bounded (step 1))
                        (:instance lw-kb-multiply-order
                          (a (* (lw-mellin-window-cap value sigma index error start ceiling numerator denominator)
                                (lw-mellin-weight value sigma index 1 error)))
                          (b (lw-log-window-kernel-cap value (lw-mellin-signal-error value sigma index 1 error)
                               sigma index 1 shifted-error start ceiling numerator denominator))
                          (factor weight)))
                  :in-theory (enable lw-mellin-window-cap))))

(defun lw-mellin-dyadic-kernel-budget (left right depth sigma index error shifted-error start ceiling numerator denominator)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (* (- right left) (lw-log-window-kernel-cap left (lw-mellin-signal-error left sigma index 1 error)
                         sigma index 1 shifted-error start ceiling numerator denominator))
    (let ((middle (/ (+ left right) 2)))
      (+ (lw-mellin-dyadic-kernel-budget left middle (- depth 1) sigma index error shifted-error start ceiling numerator denominator)
         (lw-mellin-dyadic-kernel-budget middle right (- depth 1) sigma index error shifted-error start ceiling numerator denominator)))))

(local (defthm lw-kb-budget-append
         (equal (lw-mellin-budget (append first second)) (+ (lw-mellin-budget first) (lw-mellin-budget second)))
         :hints (("Goal" :induct (append first second) :in-theory (enable lw-mellin-budget)))))

(local (in-theory (disable lw-mellin-computed-row-kernel-budget)))

(defthm lw-mellin-dyadic-window-kernel-budget
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= left right)
                (rationalp sigma) (<= 2 sigma) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-budget (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator))
               (lw-mellin-dyadic-kernel-budget left right depth sigma index error shifted-error start ceiling numerator denominator)))
  :hints (("Goal" :induct (lw-mellin-dyadic-kernel-budget left right depth sigma index error shifted-error start ceiling numerator denominator)
                  :in-theory (enable lw-mellin-dyadic-window-rows))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-computed-row-kernel-budget (value left) (weight (- right left))))
                 :do-not-induct t))))

; Use exactly the default improper evaluator's cutoff, depth and precision.
(defun lw-mellin-shifted-kernel-budget (sigma height index error shifted-error start ceiling numerator denominator)
  (let* ((cap (lw-mellin-integral-cutoff sigma index error)) (bounded-error (/ error 2)))
    (lw-mellin-dyadic-kernel-budget 0 cap (lw-mellin-integral-depth cap sigma height bounded-error)
      sigma index (lw-mellin-integral-precision cap bounded-error) shifted-error start ceiling numerator denominator)))

(local (in-theory (disable lw-mellin-dyadic-kernel-budget lw-mellin-dyadic-window-kernel-budget)))

(defthm lw-mellin-window-shifted-kernel-budget
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-window-budget sigma height index error start ceiling numerator denominator)
               (lw-mellin-shifted-kernel-budget sigma height index error shifted-error start ceiling numerator denominator)))
  :hints (("Goal" :use ((:instance lw-mellin-integral-cutoff-valid)
                        (:instance lw-mellin-integral-precision-valid (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2)))
                        (:instance lw-mellin-dyadic-window-kernel-budget
                          (left 0) (right (lw-mellin-integral-cutoff sigma index error))
                          (depth (lw-mellin-integral-depth (lw-mellin-integral-cutoff sigma index error) sigma height (/ error 2)))
                          (error (lw-mellin-integral-precision (lw-mellin-integral-cutoff sigma index error) (/ error 2)))))
                  :in-theory (enable lw-mellin-window-budget lw-mellin-shifted-kernel-budget lw-mellin-bounded-window-rows))))

(defthm lw-mellin-dyadic-kernel-budget-valid
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= left right)
                (rationalp sigma) (<= 2 sigma) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (and (rationalp (lw-mellin-dyadic-kernel-budget left right depth sigma index error shifted-error start ceiling numerator denominator))
                (<= 0 (lw-mellin-dyadic-kernel-budget left right depth sigma index error shifted-error start ceiling numerator denominator))))
  :hints (("Goal" :induct (lw-mellin-dyadic-kernel-budget left right depth sigma index error shifted-error start ceiling numerator denominator)
                  :in-theory (enable lw-mellin-dyadic-kernel-budget))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-error-budgets (value left) (step 1))
                       (:instance lw-log-window-kernel-cap-valid (value left) (step 1)
                         (signal-error (lw-mellin-signal-error left sigma index 1 error))))
                 :do-not-induct t :nonlinearp t))))

(local (in-theory (disable lw-mellin-dyadic-kernel-budget-valid)))

(defthm lw-mellin-shifted-kernel-budget-valid
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (and (rationalp (lw-mellin-shifted-kernel-budget sigma height index error shifted-error start ceiling numerator denominator))
                (<= 0 (lw-mellin-shifted-kernel-budget sigma height index error shifted-error start ceiling numerator denominator))))
  :hints (("Goal" :use ((:instance lw-mellin-integral-cutoff-valid)
                        (:instance lw-mellin-integral-precision-valid (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2)))
                        (:instance lw-mellin-dyadic-kernel-budget-valid
                          (left 0) (right (lw-mellin-integral-cutoff sigma index error))
                          (depth (lw-mellin-integral-depth (lw-mellin-integral-cutoff sigma index error) sigma height (/ error 2)))
                          (error (lw-mellin-integral-precision (lw-mellin-integral-cutoff sigma index error) (/ error 2)))))
                  :in-theory (enable lw-mellin-shifted-kernel-budget))))

(local (in-theory (disable lw-mellin-shifted-kernel-budget lw-mellin-shifted-kernel-budget-valid
                           lw-mellin-window-shifted-kernel-budget lw-mellin-integral lw-mellin-integral-rational
                           lw-failed-search-improper-mellin-bound lw-landau-window-search
                           lw-complex-diskp lw-complex-disk-enlarge lw-disk-enlarge)))

(defthm lw-failed-search-improper-shifted-kernel-bound
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-mellin-integral sigma height index error)
            (+ (* 2 (lw-mellin-shifted-kernel-budget sigma height index error shifted-error start ceiling numerator denominator))
               (- (car (lw-mellin-integral sigma 0 index error))) (/ error 2))))
  :hints (("Goal" :use (lw-failed-search-improper-mellin-bound lw-mellin-window-shifted-kernel-budget
                        lw-mellin-shifted-kernel-budget-valid (:instance lw-mellin-integral-rational (height 0))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-mellin-integral sigma height index error))
                          (radius (+ (* 2 (lw-mellin-window-budget sigma height index error start ceiling numerator denominator))
                                     (- (car (lw-mellin-integral sigma 0 index error))) (/ error 2)))
                          (cap (+ (* 2 (lw-mellin-shifted-kernel-budget sigma height index error shifted-error start ceiling numerator denominator))
                                  (- (car (lw-mellin-integral sigma 0 index error))) (/ error 2)))))
                  :in-theory (enable lw-complexp))))
