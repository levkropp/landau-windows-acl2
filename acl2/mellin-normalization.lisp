(in-package "ACL2")

(include-book "kernel-upper-mass")
(include-book "mellin-kernel-budget")
(include-book "log-exp")

; Sum the actual spatially selected kernel majorant on a uniform grid.
(local (in-theory
        (disable lw-kernel-grid-upper-sum lw-kernel-grid-upper-sum-valid lw-kernel-grid-upper-mass-bound
                 lw-log-window-kernel-cap lw-log-window-kernel-cap-valid lw-log-signal-grid-outside-window
                 lw-log-signal-point lw-log-signal-window-cap lw-rpow-bounds lw-signal-precision
                 lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-kernel-cap lw-mellin-signal-cap
                 lw-mellin-error-budgets lw-kernel-weight-bounds lw-kernel-weight-bounds-valid
                 lw-kernel-weight-bounds-overlap lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-exp-term lw-exp-sum lw-exp-bounds lw-rational-power
                 lw-kernel-window-left-count lw-kernel-window-right-address lw-kernel-window-upper-sum
                 lw-log-bounds (:executable-counterpart lw-log-bounds))))

(local (defthm lw-mk-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mk-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mk-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mk-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mk-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mk-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-mk-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mk-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mk-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mk-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defun lw-mk-range-induction (address small large)
         (declare (xargs :measure (nfix small)))
         (if (zp small) (list address large) (lw-mk-range-induction (+ address 1) (- small 1) (- large 1)))))
(local (defthm lw-mk-upper-zero
         (implies (zp count) (equal (lw-kernel-grid-upper-sum address count rate index step error) 0))
         :hints (("Goal" :in-theory (enable lw-kernel-grid-upper-sum)))))
(local (defthm lw-mk-upper-positive
         (implies (not (zp count))
                  (equal (lw-kernel-grid-upper-sum address count rate index step error)
                         (+ (* step (cdr (lw-kernel-weight-bounds (* address step) rate index 1 error)))
                            (lw-kernel-grid-upper-sum (+ address 1) (- count 1) rate index step error))))
         :hints (("Goal" :expand ((lw-kernel-grid-upper-sum address count rate index step error))))
         :rule-classes nil))

(defthm lw-kernel-grid-upper-monotone-count
  (implies (and (natp address) (natp small) (natp large) (<= small large)
                (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step))
           (<= (lw-kernel-grid-upper-sum address small rate index step error)
               (lw-kernel-grid-upper-sum address large rate index step error)))
  :hints (("Goal" :induct (lw-mk-range-induction address small large))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-grid-upper-sum-valid (count large)))
                 :expand ((lw-kernel-grid-upper-sum address small rate index step error)
                          (lw-kernel-grid-upper-sum address large rate index step error))
                 :do-not-induct t))))

(defun lw-kernel-grid-left-sum (address count cutoff rate index step error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (if (< address cutoff) (* step (cdr (lw-kernel-weight-bounds (* address step) rate index 1 error))) 0)
       (lw-kernel-grid-left-sum (+ address 1) (- count 1) cutoff rate index step error))))

(defun lw-kernel-grid-right-sum (address count cutoff rate index step error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (if (<= cutoff address) (* step (cdr (lw-kernel-weight-bounds (* address step) rate index 1 error))) 0)
       (lw-kernel-grid-right-sum (+ address 1) (- count 1) cutoff rate index step error))))

(defthm lw-kernel-grid-left-sum-bound
  (implies (and (natp address) (natp count) (natp cutoff) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step))
           (<= (lw-kernel-grid-left-sum address count cutoff rate index step error)
               (lw-kernel-grid-upper-sum address (nfix (- cutoff address)) rate index step error)))
  :hints (("Goal" :induct (lw-kernel-grid-left-sum address count cutoff rate index step error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-grid-upper-sum-valid (count (nfix (- cutoff address))))
                       (:instance lw-mk-upper-positive (count (- cutoff address))))
                 :expand ((lw-kernel-grid-upper-sum address (- cutoff address) rate index step error))
                 :do-not-induct t))))

(local (in-theory (disable lw-kernel-grid-upper-monotone-count)))

(defthm lw-kernel-grid-right-sum-bound
  (implies (and (natp address) (natp count) (natp cutoff) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step))
           (<= (lw-kernel-grid-right-sum address count cutoff rate index step error)
               (lw-kernel-grid-upper-sum (max address cutoff) count rate index step error)))
  :hints (("Goal" :induct (lw-kernel-grid-right-sum address count cutoff rate index step error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-grid-upper-sum-valid (address (max address cutoff)))
                       (:instance lw-kernel-grid-upper-monotone-count (address cutoff) (small (- count 1)) (large count)))
                 :expand ((lw-kernel-grid-upper-sum address count rate index step error))
                 :do-not-induct t))))

(local (in-theory (disable lw-kernel-grid-left-sum lw-kernel-grid-right-sum
                           lw-kernel-grid-left-sum-bound lw-kernel-grid-right-sum-bound)))

(defthm lw-log-window-kernel-cap-grid-bound
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp address) (rationalp step) (< 0 step) (rationalp signal-error) (< 0 signal-error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-log-window-kernel-cap (* address step) signal-error 252 index 1 shifted-error start ceiling numerator denominator)
               (+ (* 2 (+ ceiling 1) (cdr (lw-kernel-weight-bounds (* address step) (- 252 (/ numerator denominator)) index 1 shifted-error)))
                  (* 16 (+ (if (< address (lw-kernel-window-left-count (cdr (lw-log-bounds start 1/1000)) step))
                               (cdr (lw-kernel-weight-bounds (* address step) 250 index 1 shifted-error)) 0)
                           (if (<= (lw-kernel-window-right-address (car (lw-log-bounds start 1/1000)) step) address)
                               (cdr (lw-kernel-weight-bounds (* address step) 250 index 1 shifted-error)) 0))))))
  :hints (("Goal"
           :use ((:instance lw-log-signal-grid-outside-window)
                 (:instance lw-kernel-weight-bounds-valid (value (* address step)) (sigma 250) (step 1) (error shifted-error))
                 (:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
                 (:instance lw-kernel-weight-bounds-valid (value (* address step)) (sigma (- 252 (/ numerator denominator))) (step 1) (error shifted-error)))
           :in-theory (union-theories '(lw-log-window-kernel-cap lw-intervalp natp posp
                                       rationalp-* rationalp-+ associativity-of-* commutativity-of-* lw-mk-left-commutes
                                       distributivity lw-mk-left-distribute associativity-of-+ commutativity-of-+
                                       (:executable-counterpart binary-*) (:executable-counterpart binary-+))
                                     (theory 'minimal-theory)) :nonlinearp t)))

(defun lw-mellin-grid-kernel-budget (address count index step error shifted-error start ceiling numerator denominator)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (* step (lw-log-window-kernel-cap (* address step)
                 (lw-mellin-signal-error (* address step) 252 index 1 error)
                 252 index 1 shifted-error start ceiling numerator denominator))
       (lw-mellin-grid-kernel-budget (+ address 1) (- count 1) index step error shifted-error start ceiling numerator denominator))))

(local (in-theory (disable lw-log-window-kernel-cap-grid-bound)))

(defthm lw-mellin-grid-kernel-budget-masked
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp address) (natp count) (rationalp step) (< 0 step) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-grid-kernel-budget address count index step error shifted-error start ceiling numerator denominator)
               (+ (* 2 (+ ceiling 1) (lw-kernel-grid-upper-sum address count (- 252 (/ numerator denominator)) index step shifted-error))
                  (* 16 (+ (lw-kernel-grid-left-sum address count (lw-kernel-window-left-count (cdr (lw-log-bounds start 1/1000)) step) 250 index step shifted-error)
                           (lw-kernel-grid-right-sum address count (lw-kernel-window-right-address (car (lw-log-bounds start 1/1000)) step) 250 index step shifted-error))))))
  :hints (("Goal" :induct (lw-mellin-grid-kernel-budget address count index step error shifted-error start ceiling numerator denominator)
                  :in-theory (enable lw-kernel-grid-left-sum lw-kernel-grid-right-sum))
          (and stable-under-simplificationp
               '(:use ((:instance lw-log-window-kernel-cap-grid-bound
                         (signal-error (lw-mellin-signal-error (* address step) 252 index 1 error)))
                       (:instance lw-mk-upper-positive (rate (- 252 (/ numerator denominator))) (error shifted-error))
                       (:instance lw-mellin-error-budgets (value (* address step)) (sigma 252) (step 1))
                       (:instance lw-log-window-kernel-cap-valid (value (* address step)) (sigma 252) (step 1)
                         (signal-error (lw-mellin-signal-error (* address step) 252 index 1 error)))
                       (:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
                       (:instance lw-kernel-weight-bounds-valid (value (* address step)) (sigma 250) (step 1) (error shifted-error))
                       (:instance lw-kernel-weight-bounds-valid (value (* address step)) (sigma (- 252 (/ numerator denominator))) (step 1) (error shifted-error))
                       (:instance lw-mk-multiply-order
                         (a (lw-log-window-kernel-cap (* address step) (lw-mellin-signal-error (* address step) 252 index 1 error) 252 index 1 shifted-error start ceiling numerator denominator))
                         (b (+ (* 2 (+ ceiling 1) (cdr (lw-kernel-weight-bounds (* address step) (- 252 (/ numerator denominator)) index 1 shifted-error)))
                               (* 16 (+ (if (< address (lw-kernel-window-left-count (cdr (lw-log-bounds start 1/1000)) step))
                                            (cdr (lw-kernel-weight-bounds (* address step) 250 index 1 shifted-error)) 0)
                                        (if (<= (lw-kernel-window-right-address (car (lw-log-bounds start 1/1000)) step) address)
                                            (cdr (lw-kernel-weight-bounds (* address step) 250 index 1 shifted-error)) 0)))))
                         (factor step)))
                 :expand ((lw-kernel-grid-upper-sum address count (- 252 (/ numerator denominator)) index step shifted-error))
                 :do-not-induct t))))

(local (in-theory (disable lw-mellin-grid-kernel-budget lw-mellin-grid-kernel-budget-masked)))

(defthm lw-mellin-grid-kernel-budget-cover
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp count) (rationalp step) (< 0 step) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-grid-kernel-budget 0 count index step error shifted-error start ceiling numerator denominator)
               (+ (* 2 (+ ceiling 1) (lw-kernel-grid-upper-sum 0 count (- 252 (/ numerator denominator)) index step shifted-error))
                  (* 16 (lw-kernel-window-upper-sum (car (lw-log-bounds start 1/1000)) (cdr (lw-log-bounds start 1/1000)) count index step shifted-error)))))
  :hints (("Goal" :use ((:instance lw-mellin-grid-kernel-budget-masked (address 0))
                        (:instance lw-kernel-grid-left-sum-bound (address 0) (cutoff (lw-kernel-window-left-count (cdr (lw-log-bounds start 1/1000)) step)) (rate 250) (error shifted-error))
                        (:instance lw-kernel-grid-right-sum-bound (address 0) (cutoff (lw-kernel-window-right-address (car (lw-log-bounds start 1/1000)) step)) (rate 250) (error shifted-error)))
                  :in-theory (enable lw-kernel-window-upper-sum))))

(local (in-theory (disable lw-mellin-grid-kernel-budget-cover lw-kernel-window-upper-growth-budget
                           lw-kernel-window-grid-length lw-rational-power-monotone-base lw-reciprocal-antitone)))

(defun lw-mellin-grid-kernel-error-factor (start count step ceiling)
  (+ (* 2 (+ ceiling 1) (nfix count) step)
     (* 16 (lw-kernel-window-grid-length (cdr (lw-log-bounds start 1/1000)) count step))))

(defthm lw-mellin-grid-kernel-budget-estimate
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index) (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
                (natp count) (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (rationalp error) (< 0 error) (rationalp shifted-error) (< 0 shifted-error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-grid-kernel-budget 0 count index step error shifted-error start ceiling numerator denominator)
               (+ (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))
                  (* (lw-mellin-grid-kernel-error-factor start count step ceiling) shifted-error))))
  :hints (("Goal"
           :use (lw-mellin-grid-kernel-budget-cover
                 (:instance lw-log-bounds-interval (value start) (epsilon 1/1000))
                 (:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
                 (:instance lw-kernel-grid-upper-mass-bound (rate (- 252 (/ numerator denominator))) (error shifted-error))
                 (:instance lw-kernel-grid-upper-sum-valid (address 0) (rate (- 252 (/ numerator denominator))) (error shifted-error))
                 (:instance lw-kernel-window-upper-growth-budget
                   (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000))) (error shifted-error))
                 (:instance lw-mk-multiply-order (a (* 2 (- 252 (/ numerator denominator)))) (b 600) (factor (* step (+ 1 index))))
                 (:instance lw-mk-multiply-order
                   (a (lw-kernel-grid-upper-sum 0 count (- 252 (/ numerator denominator)) index step shifted-error))
                   (b (+ (* 2 (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))) (* count step shifted-error)))
                   (factor (* 2 (+ ceiling 1))))
                 (:instance lw-reciprocal-antitone (left (- 252 (/ numerator denominator))) (right 252))
                 (:instance lw-rational-power-monotone-base
                   (left 1/252) (right (/ (- 252 (/ numerator denominator)))) (exponent (+ 1 index))))
           :in-theory (disable lw-log-bounds-interval lw-rational-power-nonnegative) :nonlinearp nil)))

(defthm lw-mellin-grid-kernel-error-factor-valid
  (implies (and (natp count) (rationalp step) (< 0 step) (rationalp ceiling) (<= 0 ceiling))
           (and (rationalp (lw-mellin-grid-kernel-error-factor start count step ceiling))
                (<= 0 (lw-mellin-grid-kernel-error-factor start count step ceiling))))
  :hints (("Goal" :use ((:instance lw-kernel-window-upper-data-valid
                          (upper (cdr (lw-log-bounds start 1/1000)))))
                  :in-theory (disable lw-kernel-window-upper-data-valid) :nonlinearp t)))

(local (in-theory (disable lw-mellin-grid-kernel-error-factor lw-mellin-grid-kernel-error-factor-valid
                           lw-mellin-grid-kernel-budget-estimate)))

(defun lw-mellin-grid-kernel-precision (start count step ceiling target-error)
  (/ target-error (* 2 (+ 1 (lw-mellin-grid-kernel-error-factor start count step ceiling)))))

(defthm lw-mellin-grid-kernel-precision-budget
  (implies (and (natp count) (rationalp step) (< 0 step) (rationalp ceiling) (<= 0 ceiling)
                (rationalp target-error) (< 0 target-error))
           (and (rationalp (lw-mellin-grid-kernel-precision start count step ceiling target-error))
                (< 0 (lw-mellin-grid-kernel-precision start count step ceiling target-error))
                (<= (* (lw-mellin-grid-kernel-error-factor start count step ceiling)
                       (lw-mellin-grid-kernel-precision start count step ceiling target-error)) (/ target-error 2))))
  :hints (("Goal" :use (lw-mellin-grid-kernel-error-factor-valid
                        (:instance lw-positive-division-bound
                          (numerator (* (lw-mellin-grid-kernel-error-factor start count step ceiling) target-error))
                          (divisor (* 2 (+ 1 (lw-mellin-grid-kernel-error-factor start count step ceiling)))) (bound (/ target-error 2))))
                  :nonlinearp t)))

(local (in-theory (disable lw-mellin-grid-kernel-precision lw-mellin-grid-kernel-precision-budget)))

(defthm lw-mellin-grid-kernel-budget-normalized
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index) (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
                (natp count) (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (rationalp error) (< 0 error) (rationalp target-error) (< 0 target-error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-grid-kernel-budget 0 count index step error
                 (lw-mellin-grid-kernel-precision start count step ceiling target-error) start ceiling numerator denominator)
               (+ (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))) (/ target-error 2))))
  :hints (("Goal" :use (lw-mellin-grid-kernel-precision-budget
                        (:instance lw-mellin-grid-kernel-budget-estimate
                          (shifted-error (lw-mellin-grid-kernel-precision start count step ceiling target-error)))))))

(local (in-theory (disable lw-mellin-window-cap lw-mellin-weight lw-mellin-window-cap-kernel-bound
                           lw-log-signal-window-cap-valid lw-mellin-weight-bounded
                           lw-mellin-grid-kernel-budget-normalized)))

(defun lw-mellin-grid-window-budget (address count index step error start ceiling numerator denominator)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (* step (lw-mellin-window-cap (* address step) 252 index error start ceiling numerator denominator)
               (lw-mellin-weight (* address step) 252 index 1 error))
       (lw-mellin-grid-window-budget (+ address 1) (- count 1) index step error start ceiling numerator denominator))))

(defthm lw-mellin-grid-window-budget-valid
  (implies (and (natp address) (rationalp step) (< 0 step) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (and (rationalp (lw-mellin-grid-window-budget address count index step error start ceiling numerator denominator))
                (<= 0 (lw-mellin-grid-window-budget address count index step error start ceiling numerator denominator))))
  :hints (("Goal" :induct (lw-mellin-grid-window-budget address count index step error start ceiling numerator denominator))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-error-budgets (value (* address step)) (sigma 252) (step 1))
                       (:instance lw-log-signal-window-cap-valid (value (* address step)) (error (lw-mellin-signal-error (* address step) 252 index 1 error)))
                       (:instance lw-mellin-weight-bounded (value (* address step)) (sigma 252) (step 1)))
                 :in-theory (enable lw-mellin-window-cap) :do-not-induct t :nonlinearp t))))

(defthm lw-mellin-grid-window-kernel-budget
  (implies (and (natp address) (natp count) (rationalp step) (< 0 step) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-grid-window-budget address count index step error start ceiling numerator denominator)
               (lw-mellin-grid-kernel-budget address count index step error shifted-error start ceiling numerator denominator)))
  :hints (("Goal" :induct (lw-mellin-grid-window-budget address count index step error start ceiling numerator denominator)
                  :in-theory (enable (:definition lw-mellin-grid-kernel-budget)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-window-cap-kernel-bound (value (* address step)) (sigma 252))
                       (:instance lw-mellin-error-budgets (value (* address step)) (sigma 252) (step 1))
                       (:instance lw-log-signal-window-cap-valid (value (* address step)) (error (lw-mellin-signal-error (* address step) 252 index 1 error)))
                       (:instance lw-mellin-weight-bounded (value (* address step)) (sigma 252) (step 1))
                       (:instance lw-log-window-kernel-cap-valid (value (* address step)) (sigma 252) (step 1)
                         (signal-error (lw-mellin-signal-error (* address step) 252 index 1 error)))
                       (:instance lw-mk-multiply-order
                         (a (* (lw-mellin-window-cap (* address step) 252 index error start ceiling numerator denominator)
                               (lw-mellin-weight (* address step) 252 index 1 error)))
                         (b (lw-log-window-kernel-cap (* address step) (lw-mellin-signal-error (* address step) 252 index 1 error)
                              252 index 1 shifted-error start ceiling numerator denominator)) (factor step)))
                 :in-theory (enable lw-mellin-window-cap) :do-not-induct t))))

(local (in-theory (disable lw-mellin-grid-window-budget lw-mellin-grid-window-budget-valid lw-mellin-grid-window-kernel-budget)))

(defthm lw-mellin-grid-window-budget-normalized
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index) (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
                (natp count) (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (rationalp error) (< 0 error) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-grid-window-budget 0 count index step error start ceiling numerator denominator)
               (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))))
  :hints (("Goal"
           :cases ((<= (lw-mellin-grid-window-budget 0 count index step error start ceiling numerator denominator)
                       (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))))
           :use ((:instance lw-mellin-grid-window-budget-valid (address 0))
                 (:instance lw-mellin-grid-kernel-budget-normalized
                   (target-error (- (lw-mellin-grid-window-budget 0 count index step error start ceiling numerator denominator)
                                    (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))))))
                 (:instance lw-mellin-grid-window-kernel-budget (address 0)
                   (shifted-error (lw-mellin-grid-kernel-precision start count step ceiling
                                    (- (lw-mellin-grid-window-budget 0 count index step error start ceiling numerator denominator)
                                       (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))))))))))

(local (in-theory (disable lw-mellin-grid-window-budget-normalized lw-kernel-grid-count lw-kernel-grid-step
                           lw-kernel-grid-count-adequate lw-kernel-grid-step-valid lw-window-index
                           lw-kernel-window-threshold (:executable-counterpart lw-kernel-window-threshold)
                           lw-geometric-index (:executable-counterpart lw-geometric-index) lw-eventual-kernel-window-data)))

(defthm lw-eventual-mellin-computed-grid-window-budget
  (implies (and (rationalp start) (<= (lw-kernel-window-threshold) start)
                (rationalp cap) (< 0 cap) (rationalp mesh) (< 0 mesh) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (let* ((index (lw-window-index start))
                  (count (lw-kernel-grid-count cap 300 index mesh)) (step (lw-kernel-grid-step cap 300 index mesh)))
             (<= (lw-mellin-grid-window-budget 0 count index step error start ceiling numerator denominator)
                 (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))))))
  :hints (("Goal" :use ((:instance lw-eventual-kernel-window-data (target (max 64 (lw-geometric-index 5000/4977 128))))
                        (:instance lw-kernel-grid-count-adequate (rate 300) (index (lw-window-index start)))
                        (:instance lw-kernel-grid-step-valid (rate 300) (index (lw-window-index start)))
                        (:instance lw-mellin-grid-window-budget-normalized
                          (index (lw-window-index start))
                          (count (lw-kernel-grid-count cap 300 (lw-window-index start) mesh))
                          (step (lw-kernel-grid-step cap 300 (lw-window-index start) mesh))))
                  :in-theory (union-theories '(lw-kernel-window-threshold max natp lw-geometric-index-natural)
                                             (theory 'minimal-theory)))))
