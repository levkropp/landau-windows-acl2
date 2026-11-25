(in-package "ACL2")

(include-book "kernel-tilts")
(include-book "exp-geometric")
(include-book "log-growth")

; Turn exact finite tilts into geometric decay at the window's checked
; derivative band. All exponential comparisons use proved Taylor sums.
(local (in-theory
        (disable lw-rational-power lw-rational-power-add-exponents lw-rational-power-product
                 lw-kernel-grid-ratio lw-kernel-grid-ratio-valid lw-mellin-grid-weight-sum
                 lw-mellin-grid-weight-left-tail-normalized lw-mellin-grid-weight-right-tail-normalized
                 lw-geometric-left-decay lw-geometric-right-decay)))
(local (defthm lw-kw-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-kw-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kw-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-kw-zero-times (equal (* 0 a) 0)))
(local (defthm lw-kw-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-kw-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-kw-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-kw-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kw-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-kw-equal-times
         (implies (equal a b) (equal (* a factor) (* b factor))) :rule-classes nil))
(local (defthm lw-kw-cancel-equality
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (equal (* factor a) (* factor b))) (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-kw-reciprocal-involution
         (implies (and (rationalp value) (< 0 value)) (equal (/ (/ value)) value))
         :hints (("Goal" :use ((:instance inverse-of-* (x value)) (:instance inverse-of-* (x (/ value)))
                              (:instance lw-kw-cancel-equality (a (/ (/ value))) (b value) (factor (/ value))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))))

(defthm lw-kernel-window-left-ratio
  (implies (and (rationalp step) (< 0 step))
           (equal (/ (lw-kernel-grid-ratio 250 step) (lw-kernel-grid-ratio 300 step))
                  (+ 1 (/ (* 50 step) (+ 1 (* 250 step))))))
  :hints (("Goal" :use ((:instance inverse-of-* (x (+ 1 (* 250 step)))))
                  :in-theory (e/d (lw-kernel-grid-ratio) (inverse-of-*)))))

(defthm lw-kernel-window-right-ratio
  (implies (and (rationalp step) (< 0 step))
           (equal (/ (lw-kernel-grid-ratio 250 step) (lw-kernel-grid-ratio 200 step))
                  (- 1 (/ (* 50 step) (+ 1 (* 250 step))))))
  :hints (("Goal" :use ((:instance inverse-of-* (x (+ 1 (* 250 step)))))
                  :in-theory (e/d (lw-kernel-grid-ratio) (inverse-of-*)))))

(defthm lw-kernel-window-increment-bounds
  (implies (and (rationalp step) (< 0 step) (<= step 1/124750))
           (and (rationalp (/ (* 50 step) (+ 1 (* 250 step))))
                (< 0 (/ (* 50 step) (+ 1 (* 250 step))))
                (<= (* 499/10 step) (/ (* 50 step) (+ 1 (* 250 step))))
                (<= (/ (* 50 step) (+ 1 (* 250 step))) (* 50 step))))
  :hints (("Goal" :use ((:instance lw-positive-division-bound (numerator (* 50 step)) (divisor (+ 1 (* 250 step))) (bound (* 50 step)))
                        (:instance lw-positive-division-lower-bound (numerator (* 50 step)) (divisor (+ 1 (* 250 step))) (bound (* 499/10 step)))
                        (:instance lw-kw-multiply-order (a step) (b 1/124750) (factor (* 12475 step))))
                  :nonlinearp t)))

(local (in-theory (disable lw-kernel-window-left-ratio lw-kernel-window-right-ratio lw-kernel-window-increment-bounds)))

(defthm lw-kernel-window-left-factor
  (implies (and (natp cutoff) (natp index) (rationalp step) (< 0 step) (<= step 1/124750)
                (<= (* cutoff step) (/ index 300)))
           (<= (lw-rational-power (/ (lw-kernel-grid-ratio 250 step) (lw-kernel-grid-ratio 300 step)) cutoff)
               (lw-rational-power 237/200 index)))
  :hints (("Goal" :use (lw-kernel-window-left-ratio lw-kernel-window-increment-bounds
                        (:instance lw-kw-multiply-order (a (/ (* 50 step) (+ 1 (* 250 step)))) (b (* 50 step)) (factor cutoff))
                        (:instance lw-geometric-left-decay (increment (/ (* 50 step) (+ 1 (* 250 step)))))))))

(defthm lw-kernel-window-right-factor
  (implies (and (natp cutoff) (natp index) (rationalp step) (< 0 step) (<= step 1/124750)
                (rationalp lower) (<= 64 lower) (<= index (* 625/2 lower)) (<= (- (* 3/2 lower) 1) (* cutoff step)))
           (<= (lw-rational-power (/ (lw-kernel-grid-ratio 250 step) (lw-kernel-grid-ratio 200 step)) cutoff)
               (* 2 (lw-rational-power 79/100 index))))
  :hints (("Goal" :use (lw-kernel-window-right-ratio lw-kernel-window-increment-bounds
                        (:instance lw-kw-multiply-order (a (* 499/10 step)) (b (/ (* 50 step) (+ 1 (* 250 step)))) (factor cutoff))
                        (:instance lw-kw-multiply-order (a (- (* 3/2 lower) 1)) (b (* cutoff step)) (factor 499/10))
                        (:instance lw-geometric-right-decay
                          (ratio (- 1 (/ (* 50 step) (+ 1 (* 250 step))))))))))

(local (defthm lw-kw-power-successor
         (implies (natp index)
                  (equal (lw-rational-power base (+ 1 index))
                         (* base (lw-rational-power base index))))
         :hints (("Goal" :expand ((lw-rational-power base (+ 1 index)))))
         :rule-classes nil))

(local (defthm lw-kw-power-mixed
         (implies (and (rationalp a) (rationalp b) (natp index))
                  (equal (* (lw-rational-power a (+ 1 index)) (lw-rational-power b index))
                         (* a (lw-rational-power (* a b) index))))
         :hints (("Goal" :use ((:instance lw-kw-power-successor (base a))
                              (:instance lw-rational-power-product (left a) (right b) (exponent index)))
                         :in-theory (disable lw-rational-power-product)))
         :rule-classes nil))

(defun lw-kernel-window-radius (index)
  (* (lw-rational-power 79/80 (nfix index))
     (lw-rational-power 1/250 (+ 1 (nfix index)))))

(defthm lw-kernel-window-radius-valid
  (and (rationalp (lw-kernel-window-radius index))
       (<= 0 (lw-kernel-window-radius index)))
  :hints (("Goal" :use ((:instance lw-rational-power-nonnegative (base 79/80) (exponent (nfix index)))
                        (:instance lw-rational-power-nonnegative (base 1/250) (exponent (+ 1 (nfix index)))))
                  :in-theory (disable lw-rational-power-nonnegative) :nonlinearp t)))

(local (defthm lw-kw-left-scale
         (implies (natp index)
                  (equal (* (lw-rational-power 1/300 (+ 1 index)) (lw-rational-power 237/200 index))
                         (* 5/6 (lw-kernel-window-radius index))))
         :hints (("Goal" :use ((:instance lw-kw-power-mixed (a 1/300) (b 237/200))
                              (:instance lw-kw-power-mixed (a 1/250) (b 79/80)))))
         :rule-classes nil))

(local (defthm lw-kw-right-scale
         (implies (natp index)
                  (equal (* (lw-rational-power 1/200 (+ 1 index)) (lw-rational-power 79/100 index))
                         (* 5/4 (lw-kernel-window-radius index))))
         :hints (("Goal" :use ((:instance lw-kw-power-mixed (a 1/200) (b 79/100))
                              (:instance lw-kw-power-mixed (a 1/250) (b 79/80)))))
         :rule-classes nil))

(local (in-theory (disable lw-kernel-window-radius lw-kernel-window-radius-valid
                           lw-kernel-window-left-factor lw-kernel-window-right-factor)))

(defthm lw-mellin-kernel-window-left-bound
  (implies (and (natp address) (natp count) (natp cutoff) (<= (+ address count) cutoff) (natp index)
                (rationalp step) (< 0 step) (<= step 1/124750)
                (<= (* 600 step (+ 1 index)) 1) (<= (* cutoff step) (/ index 300))
                (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count 250 index step error)
               (* 2 (lw-kernel-window-radius index))))
  :hints (("Goal" :use ((:instance lw-mellin-grid-weight-left-tail-normalized (rate 250) (tilted-rate 300))
                        lw-kernel-window-left-factor lw-kw-left-scale lw-kernel-window-radius-valid
                        (:instance lw-rational-power-nonnegative (base 1/300) (exponent (+ 1 index)))
                        (:instance lw-kw-multiply-order
                          (a (lw-rational-power (/ (lw-kernel-grid-ratio 250 step) (lw-kernel-grid-ratio 300 step)) cutoff))
                          (b (lw-rational-power 237/200 index))
                          (factor (* 2 (lw-rational-power 1/300 (+ 1 index))))))
                  :in-theory (disable lw-rational-power-nonnegative) :nonlinearp t)))

(defthm lw-mellin-kernel-window-right-bound
  (implies (and (natp address) (natp count) (natp cutoff) (<= cutoff address) (natp index)
                (rationalp step) (< 0 step) (<= step 1/124750) (<= (* 600 step (+ 1 index)) 1)
                (rationalp lower) (<= 64 lower) (<= index (* 625/2 lower))
                (<= (- (* 3/2 lower) 1) (* cutoff step)) (rationalp error) (< 0 error))
           (<= (lw-mellin-grid-weight-sum address count 250 index step error)
               (* 5 (lw-kernel-window-radius index))))
  :hints (("Goal" :use ((:instance lw-mellin-grid-weight-right-tail-normalized (rate 250) (tilted-rate 200))
                        lw-kernel-window-right-factor lw-kw-right-scale
                        (:instance lw-rational-power-nonnegative (base 1/200) (exponent (+ 1 index)))
                        (:instance lw-kw-multiply-order
                          (a (lw-rational-power (/ (lw-kernel-grid-ratio 250 step) (lw-kernel-grid-ratio 200 step)) cutoff))
                          (b (* 2 (lw-rational-power 79/100 index)))
                          (factor (* 2 (lw-rational-power 1/200 (+ 1 index))))))
                  :in-theory (disable lw-rational-power-nonnegative) :nonlinearp t)))

(defun lw-kernel-window-left-count (upper step)
  (lw-ceiling-rational (/ upper step)))
(defun lw-kernel-window-right-address (lower step)
  (lw-ceiling-rational (/ (- (* 3/2 lower) 1) step)))

(defthm lw-kernel-window-addresses-natural
  (and (natp (lw-kernel-window-left-count upper step))
       (natp (lw-kernel-window-right-address lower step))))

(local (defthm lw-kw-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (/ divisor) coefficient) coefficient))
         :hints (("Goal" :use ((:instance inverse-of-* (x divisor)))
                         :in-theory (disable inverse-of-*)))))

(defthm lw-kernel-window-addresses-bracket
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (rationalp step) (< 0 step))
           (and (<= (* (lw-kernel-window-left-count upper step) step) (+ upper step))
                (<= (- (* 3/2 lower) 1) (* (lw-kernel-window-right-address lower step) step))))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value (/ upper step)))
                        (:instance lw-ceiling-rational-bracket (value (/ (- (* 3/2 lower) 1) step)))
                        (:instance lw-kw-multiply-order (a (lw-ceiling-rational (/ upper step))) (b (+ (/ upper step) 1)) (factor step))
                        (:instance lw-kw-multiply-order (a (/ (- (* 3/2 lower) 1) step))
                          (b (lw-ceiling-rational (/ (- (* 3/2 lower) 1) step))) (factor step)))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket) :nonlinearp t)))

(defthm lw-kernel-window-step-small
  (implies (and (natp index) (<= 208 index) (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1))
           (<= step 1/124750))
  :hints (("Goal" :use ((:instance lw-kw-multiply-order (a 124750) (b (* 600 (+ 1 index))) (factor step))))))

(local (in-theory (disable lw-kernel-window-left-count lw-kernel-window-right-address
                           lw-kernel-window-addresses-bracket lw-kernel-window-step-small
                           lw-mellin-kernel-window-left-bound lw-mellin-kernel-window-right-bound)))

; The derivative band supplies every mesh and cutoff inequality. The right
; tail is uniform in its finite length; no infinite sum enters this statement.
(defthm lw-mellin-kernel-window-concentration
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp error) (< 0 error))
           (<= (+ (lw-mellin-grid-weight-sum 0 (lw-kernel-window-left-count upper step) 250 index step error)
                  (lw-mellin-grid-weight-sum (lw-kernel-window-right-address lower step) count 250 index step error))
               (* 7 (lw-kernel-window-radius index))))
  :hints (("Goal" :use (lw-kernel-window-addresses-natural lw-kernel-window-addresses-bracket lw-kernel-window-step-small
                        (:instance lw-mellin-kernel-window-left-bound
                          (address 0) (count (lw-kernel-window-left-count upper step)) (cutoff (lw-kernel-window-left-count upper step)))
                        (:instance lw-mellin-kernel-window-right-bound
                          (address (lw-kernel-window-right-address lower step)) (cutoff (lw-kernel-window-right-address lower step)))))))

(local (in-theory (disable lw-kernel-grid-count lw-kernel-grid-step lw-kernel-grid-step-valid
                           lw-mellin-kernel-window-concentration)))

(defthm lw-mellin-computed-kernel-window-concentration
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (rationalp cap) (< 0 cap) (rationalp mesh) (< 0 mesh)
                (natp count) (rationalp error) (< 0 error))
           (let ((step (lw-kernel-grid-step cap 300 index mesh)))
             (<= (+ (lw-mellin-grid-weight-sum 0 (lw-kernel-window-left-count upper step) 250 index step error)
                    (lw-mellin-grid-weight-sum (lw-kernel-window-right-address lower step) count 250 index step error))
                 (* 7 (lw-kernel-window-radius index)))))
  :hints (("Goal" :use ((:instance lw-kernel-grid-step-valid (rate 300))
                        (:instance lw-mellin-kernel-window-concentration (step (lw-kernel-grid-step cap 300 index mesh)))))))

; Converting to the pole argument's rate 252 still leaves strict decay.
(defthm lw-kernel-window-radius-normalization
  (implies (natp index)
           (equal (lw-kernel-window-radius index)
                  (* 126/125 (lw-rational-power 4977/5000 index) (lw-rational-power 1/252 (+ 1 index)))))
  :hints (("Goal" :use ((:instance lw-kw-power-mixed (a 1/250) (b 79/80))
                        (:instance lw-kw-power-mixed (a 1/252) (b 4977/5000)))
                  :in-theory (enable lw-kernel-window-radius))))

(local (in-theory (disable lw-kernel-window-radius-normalization)))

(defthm lw-mellin-kernel-window-normalized-concentration
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp error) (< 0 error))
           (<= (+ (lw-mellin-grid-weight-sum 0 (lw-kernel-window-left-count upper step) 250 index step error)
                  (lw-mellin-grid-weight-sum (lw-kernel-window-right-address lower step) count 250 index step error))
               (* 8 (lw-rational-power 4977/5000 index) (lw-rational-power 1/252 (+ 1 index)))))
  :hints (("Goal" :use (lw-mellin-kernel-window-concentration lw-kernel-window-radius-normalization
                        (:instance lw-rational-power-nonnegative (base 4977/5000) (exponent index))
                        (:instance lw-rational-power-nonnegative (base 1/252) (exponent (+ 1 index))))
                  :in-theory (disable lw-rational-power-nonnegative) :nonlinearp t)))

(local (in-theory (disable lw-geometric-index (:executable-counterpart lw-geometric-index)
                           lw-geometric-threshold lw-rational-power-reciprocal-pair
                           lw-mellin-kernel-window-normalized-concentration)))

(defthm lw-kernel-window-geometric-budget
  (implies (and (natp index) (<= (lw-geometric-index 5000/4977 128) index))
           (<= (* 128 (lw-rational-power 4977/5000 index)) 1))
  :hints (("Goal" :use ((:instance lw-geometric-threshold (base 5000/4977) (target 128) (exponent index))
                        (:instance lw-rational-power-reciprocal-pair (value 4977/5000))
                        (:instance lw-rational-power-nonnegative (base 4977/5000) (exponent index))
                        (:instance lw-kw-multiply-order (a 128) (b (lw-rational-power 5000/4977 index))
                          (factor (lw-rational-power 4977/5000 index))))
                  :in-theory (disable lw-rational-power-nonnegative))))

(local (in-theory (disable lw-kernel-window-geometric-budget)))

(defthm lw-mellin-kernel-window-growth-budget
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (<= (lw-geometric-index 5000/4977 128) index)
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp error) (< 0 error))
           (<= (* 16 (+ (lw-mellin-grid-weight-sum 0 (lw-kernel-window-left-count upper step) 250 index step error)
                        (lw-mellin-grid-weight-sum (lw-kernel-window-right-address lower step) count 250 index step error)))
               (lw-rational-power 1/252 (+ 1 index))))
  :hints (("Goal" :use (lw-mellin-kernel-window-normalized-concentration lw-kernel-window-geometric-budget
                        (:instance lw-rational-power-nonnegative (base 1/252) (exponent (+ 1 index)))
                        (:instance lw-kw-multiply-order (a (* 128 (lw-rational-power 4977/5000 index))) (b 1)
                          (factor (lw-rational-power 1/252 (+ 1 index)))))
                  :in-theory (disable lw-rational-power-nonnegative) :nonlinearp t)))

(local (in-theory (disable lw-log-bounds (:executable-counterpart lw-log-bounds)
                           lw-window-index lw-window-index-check lw-window-index-from-log
                           lw-log-bounds-interval lw-log-bounds-dyadic-growth lw-window-index-log-band
                           lw-eventual-window-threshold lw-eventual-window-threshold-natural lw-eventual-window-index
                           lw-mellin-kernel-window-growth-budget)))

(defthm lw-eventual-kernel-window-data
  (implies (and (natp target) (<= 60 target) (rationalp start) (<= (lw-eventual-window-threshold target) start))
           (let ((lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000))))
             (and (<= 1 start) (rationalp lower) (rationalp upper) (<= lower upper) (<= 64 lower)
                  (natp (lw-window-index start)) (<= target (lw-window-index start))
                  (<= (* 6061/20 upper) (lw-window-index start)) (<= (lw-window-index start) (* 625/2 lower)))))
  :hints (("Goal" :use (lw-eventual-window-threshold-natural lw-eventual-window-index lw-window-index-log-band
                        (:instance lw-log-bounds-interval (value start) (epsilon 1/1000))
                        (:instance lw-log-bounds-dyadic-growth (value start) (epsilon 1/1000) (steps (+ (* 2 target) 8))))
                  :in-theory (union-theories '(lw-eventual-window-threshold lw-intervalp natp nfix associativity-of-+
                                              commutativity-of-* distributivity lw-kw-left-distribute
                                              (:executable-counterpart binary-+) (:executable-counterpart binary-*))
                                             (theory 'minimal-theory)) :nonlinearp nil)))

(defun lw-kernel-window-threshold ()
  (lw-eventual-window-threshold (max 64 (lw-geometric-index 5000/4977 128))))

(local (in-theory (disable lw-eventual-kernel-window-data)))

; A computed Y-threshold, derivative index and mesh, with no concentration
; or index-band estimate supplied as an input.
(defthm lw-eventual-mellin-kernel-window-growth-budget
  (implies (and (rationalp start) (<= (lw-kernel-window-threshold) start)
                (rationalp cap) (< 0 cap) (rationalp mesh) (< 0 mesh)
                (natp count) (rationalp error) (< 0 error))
           (let* ((index (lw-window-index start))
                  (step (lw-kernel-grid-step cap 300 index mesh))
                  (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000))))
             (<= (* 16 (+ (lw-mellin-grid-weight-sum 0 (lw-kernel-window-left-count upper step) 250 index step error)
                          (lw-mellin-grid-weight-sum (lw-kernel-window-right-address lower step) count 250 index step error)))
                 (lw-rational-power 1/252 (+ 1 index)))))
  :hints (("Goal" :use ((:instance lw-eventual-kernel-window-data (target (max 64 (lw-geometric-index 5000/4977 128))))
                        (:instance lw-kernel-grid-step-valid (rate 300) (index (lw-window-index start)))
                        (:instance lw-mellin-kernel-window-growth-budget
                          (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000)))
                          (index (lw-window-index start)) (step (lw-kernel-grid-step cap 300 (lw-window-index start) mesh))))
                  :in-theory (union-theories '(lw-kernel-window-threshold max natp lw-geometric-index-natural)
                                             (theory 'minimal-theory)))))
