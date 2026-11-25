(in-package "ACL2")

(include-book "signal-search")
(include-book "euler-continuity")
(include-book "rpow-continuity")

(local (defthm lw-sc-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-sc-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-sc-zero-product (equal (* 0 value) 0)))

(local (defthm lw-sc-sum-left-distribute
         (implies (and (rationalp left) (rationalp right) (rationalp factor))
                  (equal (* (+ left right) factor) (+ (* left factor) (* right factor))))
         :hints (("Goal" :use ((:instance distributivity (x factor) (y left) (z right)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-sc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-*
                                             lw-sc-multiply-left-commutes)))))

(local (defthm lw-sc-multiply-inequality
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-sc-abs-product
         (implies (and (rationalp left) (rationalp right))
                  (equal (abs (* left right)) (* (abs left) (abs right))))
         :hints (("Goal" :cases ((<= 0 left) (<= 0 right)) :nonlinearp t))))

(local (defthm lw-sc-clamp-lipschitz
         (implies (and (rationalp left) (rationalp right))
                  (<= (abs (- (max 0 left) (max 0 right))) (abs (- left right))))
         :hints (("Goal" :cases ((<= 0 left) (<= 0 right))))
         :rule-classes nil))

(defthm lw-ramp-rescale
  (implies (and (rationalp value) (<= 0 value) (posp index))
           (equal (* index (lw-ramp value index)) (max 0 (- value index))))
  :hints (("Goal" :cases ((<= value index))
                  :use ((:instance lw-positive-division-bound (numerator value) (divisor index) (bound 1))
                        (:instance lw-positive-division-lower-bound (numerator value) (divisor index) (bound 1)))
                  :nonlinearp t)))

(defthm lw-ramp-lipschitz
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right) (posp index))
           (<= (* index (abs (- (lw-ramp left index) (lw-ramp right index))))
               (abs (- left right))))
  :hints (("Goal" :use ((:instance lw-sc-clamp-lipschitz (left (- left index)) (right (- right index)))
                        (:instance lw-sc-abs-product
                          (left index) (right (- (lw-ramp left index) (lw-ramp right index))))
                        (:instance lw-ramp-rescale (value left))
                        (:instance lw-ramp-rescale (value right)))
                  :in-theory (disable lw-ramp lw-ramp-rescale lw-sc-abs-product))))

(defthm lw-mangoldt-bounds-overlap
  (implies (and (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (car (lw-mangoldt-bounds index left-error)) (cdr (lw-mangoldt-bounds index right-error))))
  :hints (("Goal" :use ((:instance lw-prime-power-data-sound (value index))
                        (:instance lw-primep-lower-bound (value (car (lw-prime-power-data index))))
                        (:instance lw-log-bounds-overlap (value (car (lw-prime-power-data index)))))
                  :in-theory (disable lw-prime-power-data lw-prime-power-data-sound
                                      lw-primep lw-primep-lower-bound lw-log-bounds lw-log-bounds-overlap))))

(defthm lw-mangoldt-lower-coarse
  (implies (and (posp index) (rationalp epsilon) (< 0 epsilon))
           (and (rationalp (car (lw-mangoldt-bounds index epsilon)))
                (<= 0 (car (lw-mangoldt-bounds index epsilon)))
                (<= (car (lw-mangoldt-bounds index epsilon)) index)))
  :hints (("Goal" :use ((:instance lw-prime-power-data-sound (value index))
                        (:instance lw-primep-lower-bound (value (car (lw-prime-power-data index))))
                        (:instance lw-log-bounds-lower-coarse (value (car (lw-prime-power-data index))))
                        (:instance lw-log-bounds-interval (value (car (lw-prime-power-data index)))))
                  :in-theory (disable lw-prime-power-data lw-prime-power-data-sound
                                      lw-primep lw-primep-lower-bound lw-log-bounds
                                      lw-log-bounds-lower-coarse lw-log-bounds-interval))))

(local
 (defthm lw-sc-weighted-term-transport
   (implies (and (rationalp left-coefficient) (rationalp right-coefficient) (<= 0 right-coefficient)
                 (rationalp lower) (rationalp upper) (<= 0 lower) (<= lower upper)
                 (rationalp cap) (<= lower cap))
            (<= (- (* left-coefficient lower) (* right-coefficient upper))
                (* cap (abs (- left-coefficient right-coefficient)))))
   :hints (("Goal" :cases ((<= right-coefficient left-coefficient))
                   :use ((:instance lw-sc-multiply-inequality (left lower) (right upper) (factor right-coefficient))
                         (:instance lw-sc-multiply-inequality
                           (left lower) (right cap) (factor (- left-coefficient right-coefficient))))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-mangoldt-ramp-transport
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right) (posp index)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (* (lw-ramp left index) (car (lw-mangoldt-bounds index left-error)))
                  (* (lw-ramp right index) (cdr (lw-mangoldt-bounds index right-error))))
               (abs (- left right))))
  :hints (("Goal" :use (lw-ramp-lipschitz lw-mangoldt-bounds-overlap
                        (:instance lw-mangoldt-lower-coarse (epsilon left-error))
                        (:instance lw-mangoldt-bounds-interval (value index) (epsilon right-error))
                        (:instance lw-sc-weighted-term-transport
                          (left-coefficient (lw-ramp left index)) (right-coefficient (lw-ramp right index))
                          (lower (car (lw-mangoldt-bounds index left-error)))
                          (upper (cdr (lw-mangoldt-bounds index right-error))) (cap index)))
                  :in-theory (disable lw-ramp lw-mangoldt-bounds lw-mangoldt-bounds-overlap
                                      lw-mangoldt-lower-coarse lw-mangoldt-bounds-interval
                                      lw-ramp-lipschitz))))

(defthm lw-smoothed-sum-bounds-transport
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right) (natp count)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-smoothed-sum-bounds left count left-error))
                  (cdr (lw-smoothed-sum-bounds right count right-error)))
               (* count (abs (- left right)))))
  :hints (("Goal" :induct (lw-smoothed-sum-bounds left count left-error)
                  :in-theory (disable lw-ramp lw-mangoldt-bounds))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mangoldt-ramp-transport (index count))
                        (:instance lw-smoothed-sum-bounds-valid (value left) (count (- count 1)) (epsilon left-error))
                        (:instance lw-smoothed-sum-bounds-valid (value right) (count (- count 1)) (epsilon right-error)))
                 :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-valid
                                     lw-ramp lw-mangoldt-bounds lw-mangoldt-ramp-transport)))))

(defthm lw-smoothed-sum-bounds-zero-tail
  (implies (and (rationalp value) (<= 0 value) (posp count) (<= value count)
                (rationalp epsilon) (< 0 epsilon))
           (equal (lw-smoothed-sum-bounds value count epsilon)
                  (lw-smoothed-sum-bounds value (- count 1) epsilon)))
  :hints (("Goal" :use ((:instance lw-positive-division-bound (numerator value) (divisor count) (bound 1))
                        (:instance lw-smoothed-sum-bounds-valid (count (- count 1))))
                  :expand ((lw-smoothed-sum-bounds value count epsilon))
                  :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-valid lw-mangoldt-bounds))))

(local
 (defun lw-sc-prefix-induction (large small)
   (declare (xargs :measure (nfix large)))
   (if (or (zp large) (<= large small)) (list large small)
     (lw-sc-prefix-induction (- large 1) small))))

(defthm lw-smoothed-sum-bounds-stable-prefix
  (implies (and (rationalp value) (<= 0 value) (natp small) (natp large)
                (<= value small) (<= small large) (rationalp epsilon) (< 0 epsilon))
           (equal (lw-smoothed-sum-bounds value large epsilon)
                  (lw-smoothed-sum-bounds value small epsilon)))
  :hints (("Goal" :induct (lw-sc-prefix-induction large small)
                  :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-zero-tail))
          (and stable-under-simplificationp
               '(:use ((:instance lw-smoothed-sum-bounds-zero-tail (count large)))
                 :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-zero-tail))))
  :rule-classes nil)

(defthm lw-smoothed-sum-bounds-stable-count
  (implies (and (rationalp value) (<= 0 value) (natp left-count) (natp right-count)
                (<= value left-count) (<= value right-count)
                (rationalp epsilon) (< 0 epsilon))
           (equal (lw-smoothed-sum-bounds value left-count epsilon)
                  (lw-smoothed-sum-bounds value right-count epsilon)))
  :hints (("Goal" :cases ((<= left-count right-count))
                  :use ((:instance lw-smoothed-sum-bounds-stable-prefix (small left-count) (large right-count))
                        (:instance lw-smoothed-sum-bounds-stable-prefix (small right-count) (large left-count)))
                  :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-zero-tail)))
  :rule-classes nil)

(defthm lw-signal-bounds-raw-normalize-count
  (implies (and (rationalp value) (<= 1 value) (natp count) (<= value count)
                (natp cap-count) (<= value cap-count) (rationalp epsilon) (< 0 epsilon))
           (equal (lw-signal-bounds-raw value count ceiling numerator denominator epsilon)
                  (lw-signal-bounds-raw value cap-count ceiling numerator denominator epsilon)))
  :hints (("Goal" :use ((:instance lw-smoothed-sum-bounds-stable-count
                          (left-count count) (right-count cap-count)))
                  :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-zero-tail
                                      lw-log-bounds lw-euler-bounds lw-rpow-bounds
                                      lw-interval-add lw-interval-sub lw-interval-scale)))
  :rule-classes nil)

(local (defthm lw-sc-abs-sub-symmetric
         (implies (and (rationalp left) (rationalp right))
                  (equal (abs (- left right)) (abs (- right left))))))

(local
 (defthm lw-sc-log-main-transport
   (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                 (rationalp cap) (<= left cap) (<= right cap)
                 (rationalp left-error) (< 0 left-error)
                 (rationalp right-error) (< 0 right-error))
            (<= (- (* right (car (lw-log-bounds right right-error)))
                   (* left (cdr (lw-log-bounds left left-error))))
                (* 2 cap (abs (- left right)))))
   :hints (("Goal" :use (lw-log-bounds-one-sided-transport
                         (:instance lw-log-bounds-lower-coarse (value right) (epsilon right-error))
                         (:instance lw-log-bounds-interval (value left) (epsilon left-error))
                         (:instance lw-log-bounds-interval (value right) (epsilon right-error))
                         (:instance lw-sc-multiply-inequality
                           (left (- (car (lw-log-bounds right right-error)) (cdr (lw-log-bounds left left-error))))
                           (right (abs (- right left))) (factor left))
                         (:instance lw-sc-multiply-inequality (right cap) (factor (abs (- left right))))
                         (:instance lw-sc-weighted-term-transport
                           (left-coefficient right) (right-coefficient left)
                           (lower (car (lw-log-bounds right right-error)))
                           (upper (car (lw-log-bounds right right-error))) (cap cap)))
                   :in-theory (disable lw-log-bounds lw-log-bounds-one-sided-transport
                                       lw-log-bounds-lower-coarse lw-log-bounds-interval)
                   :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-sc-euler-main-transport
   (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                 (rationalp left-error) (< 0 left-error) (<= left-error 1)
                 (rationalp right-error) (< 0 right-error))
            (<= (- (* left (+ 1 (car (lw-euler-bounds left-error))))
                   (* right (+ 1 (cdr (lw-euler-bounds right-error)))))
                (* 3 (abs (- left right)))))
   :hints (("Goal" :use (lw-euler-bounds-overlap
                         (:instance lw-euler-bounds-coarse (epsilon left-error))
                         (:instance lw-euler-bounds-interval (epsilon left-error))
                         (:instance lw-euler-bounds-interval (epsilon right-error))
                         (:instance lw-sc-weighted-term-transport
                           (left-coefficient left) (right-coefficient right)
                           (lower (+ 1 (car (lw-euler-bounds left-error))))
                           (upper (+ 1 (cdr (lw-euler-bounds right-error)))) (cap 3)))
                   :in-theory (disable lw-euler-bounds lw-euler-bounds-overlap
                                       lw-euler-bounds-coarse lw-euler-bounds-interval)))
   :rule-classes nil))

(defthm lw-gz-bounds-raw-transport
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                (rationalp cap) (<= left cap) (<= right cap) (natp count)
                (rationalp left-error) (< 0 left-error) (<= left-error 1)
                (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-gz-bounds-raw left count left-error))
                  (cdr (lw-gz-bounds-raw right count right-error)))
               (* (+ count (* 2 cap) 3) (abs (- left right)))))
  :hints (("Goal" :use (lw-smoothed-sum-bounds-transport
                        lw-sc-log-main-transport lw-sc-euler-main-transport
                        (:instance lw-smoothed-sum-bounds-valid (value left) (epsilon left-error))
                        (:instance lw-smoothed-sum-bounds-valid (value right) (epsilon right-error))
                        (:instance lw-log-bounds-interval (value left) (epsilon left-error))
                        (:instance lw-log-bounds-interval (value right) (epsilon right-error))
                        (:instance lw-euler-bounds-interval (epsilon left-error))
                        (:instance lw-euler-bounds-interval (epsilon right-error)))
                  :in-theory (disable lw-smoothed-sum-bounds lw-smoothed-sum-bounds-zero-tail
                                      lw-log-bounds lw-euler-bounds lw-smoothed-sum-bounds-transport
                                      lw-smoothed-sum-bounds-valid lw-log-bounds-interval
                                      lw-euler-bounds-interval))))

(defthm lw-signal-bounds-raw-transport
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                (rationalp cap) (<= left cap) (<= right cap) (natp count)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp left-error) (< 0 left-error) (<= left-error 1)
                (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-signal-bounds-raw left count ceiling numerator denominator left-error))
                  (cdr (lw-signal-bounds-raw right count ceiling numerator denominator right-error)))
               (* (+ count (* 2 cap) 3 ceiling) (abs (- left right)))))
  :hints (("Goal" :use (lw-gz-bounds-raw-transport lw-rpow-bounds-one-sided-transport
                        lw-sc-abs-sub-symmetric
                        (:instance lw-sc-multiply-inequality
                          (left (- (car (lw-rpow-bounds right numerator denominator right-error))
                                   (cdr (lw-rpow-bounds left numerator denominator left-error))))
                          (right (abs (- right left))) (factor ceiling))
                        (:instance lw-rpow-bounds-sound (value left) (epsilon left-error))
                        (:instance lw-rpow-bounds-sound (value right) (epsilon right-error))
                        (:instance lw-gz-bounds-raw-valid (value left) (epsilon left-error))
                        (:instance lw-gz-bounds-raw-valid (value right) (epsilon right-error)))
                  :in-theory (union-theories
                               (theory 'ground-zero)
                               '(lw-signal-bounds-raw lw-interval-sub lw-interval-scale lw-intervalp
                                 lw-sc-times-negation lw-sc-multiply-left-commutes)))))

(defthm lw-signal-precision-at-most-one
  (implies (and (rationalp value) (<= 1 value) (rationalp ceiling) (<= 0 ceiling)
                (rationalp error) (< 0 error) (<= error 1))
           (<= (lw-signal-precision value ceiling error) 1))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator error) (divisor (+ 1 (lw-signal-error-factor value ceiling))) (bound 1)))
                  :in-theory (disable lw-signal-count) :nonlinearp t)))

(defun lw-signal-lipschitz-factor (cap ceiling)
  (+ (lw-signal-count cap) (* 2 cap) 3 ceiling))

(defthm lw-signal-lipschitz-factor-valid
  (implies (and (rationalp cap) (<= 1 cap) (rationalp ceiling) (<= 0 ceiling))
           (and (rationalp (lw-signal-lipschitz-factor cap ceiling))
                (<= 0 (lw-signal-lipschitz-factor cap ceiling))))
  :hints (("Goal" :in-theory (disable lw-signal-count))))

(defthm lw-signal-bounds-transport
  (implies (and (rationalp left) (rationalp right) (< 1 left) (< 1 right)
                (rationalp cap) (<= left cap) (<= right cap)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp left-error) (< 0 left-error) (<= left-error 1)
                (rationalp right-error) (< 0 right-error) (<= right-error 1))
           (<= (- (car (lw-signal-bounds left ceiling numerator denominator left-error))
                  (cdr (lw-signal-bounds right ceiling numerator denominator right-error)))
               (* (lw-signal-lipschitz-factor cap ceiling) (abs (- left right)))))
  :hints (("Goal" :use ((:instance lw-signal-bounds-raw-transport
                          (count (lw-signal-count cap))
                          (left-error (lw-signal-precision left ceiling left-error))
                          (right-error (lw-signal-precision right ceiling right-error)))
                        (:instance lw-signal-bounds-raw-normalize-count
                          (value left) (count (lw-signal-count left)) (cap-count (lw-signal-count cap))
                          (epsilon (lw-signal-precision left ceiling left-error)))
                        (:instance lw-signal-bounds-raw-normalize-count
                          (value right) (count (lw-signal-count right)) (cap-count (lw-signal-count cap))
                          (epsilon (lw-signal-precision right ceiling right-error)))
                        (:instance lw-signal-count-covers (value left))
                        (:instance lw-signal-count-covers (value right))
                        (:instance lw-signal-count-covers (value cap))
                        (:instance lw-signal-precision-positive (value left) (error left-error))
                        (:instance lw-signal-precision-positive (value right) (error right-error))
                        (:instance lw-signal-precision-at-most-one (value left) (error left-error))
                        (:instance lw-signal-precision-at-most-one (value right) (error right-error)))
                  :in-theory (disable lw-signal-bounds-raw lw-signal-count lw-signal-precision
                                      lw-signal-bounds-raw-transport lw-signal-count-covers
                                      lw-signal-precision-positive lw-signal-precision-at-most-one))))

(defthm lw-signal-evaluations-upper-transport
  (implies (and (rationalp lower) (< 1 lower) (rationalp cap)
                (lw-addresses-between lower cap addresses)
                (rationalp point) (<= lower point) (<= point cap)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error) (<= error 1))
           (lw-lower-lipschitz
            point (car (lw-signal-bounds point ceiling numerator denominator error))
            (lw-signal-lipschitz-factor cap ceiling) addresses
            (lw-upper-values (lw-signal-samples addresses ceiling numerator denominator error))))
  :hints (("Goal" :induct (lw-addresses-between lower cap addresses)
                  :in-theory (disable lw-signal-bounds lw-signal-lipschitz-factor))
          (and stable-under-simplificationp
               '(:use ((:instance lw-signal-bounds-transport
                          (left point) (right (car addresses)) (left-error error) (right-error error))
                        (:instance lw-signal-bounds-valid (value point))
                        (:instance lw-signal-bounds-valid (value (car addresses)))
                        lw-signal-lipschitz-factor-valid)
                 :in-theory (disable lw-signal-bounds lw-signal-bounds-transport
                                     lw-signal-bounds-valid lw-signal-lipschitz-factor
                                     lw-signal-lipschitz-factor-valid)))))

(defthm lw-addresses-between-enlarge-upper
  (implies (and (rationalp upper) (rationalp cap) (<= upper cap)
                (lw-addresses-between lower upper addresses))
           (lw-addresses-between lower cap addresses)))

(local (defthm lw-sc-square-cap-at-least-one
         (implies (and (rationalp start) (<= 1 start)) (<= 1 (* start start)))
         :hints (("Goal" :nonlinearp t))))

(defthm lw-window-point-coarse-cap
  (implies (and (rationalp start) (<= 1 start) (rationalp point) (<= start point)
                (<= (* point point) (* start start start)))
           (<= point (* start start)))
  :hints (("Goal" :use ((:instance lw-window-bracket-sound (epsilon 1))
                        (:instance lw-window-bracket-contained (epsilon 1))
                        (:instance lw-square-bracket-bounds-point
                          (target (* start start start)) (bounds (lw-window-bracket start 1))))
                  :in-theory (disable lw-window-bracket lw-window-bracket-sound lw-window-bracket-contained
                                      lw-square-bracket-bounds-point))))

(defun lw-window-signal-lipschitz (start ceiling)
  (lw-signal-lipschitz-factor (* start start) ceiling))

; The search no longer assumes a transport predicate. Its only quantitative
; mathematical premise is a positive peak of the actual computed signal at
; a rational point in the window. Deriving that peak from zero data is the
; remaining Landau coefficient/kernel argument, not a premise hidden here.
(defthm lw-window-signal-search-from-peak
  (implies (and (rationalp start) (< 1 start) (rationalp step) (< 0 step)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error) (<= error 1)
                (rationalp point) (<= start point)
                (<= (* point point) (* start start start))
                (< (+ error (* (lw-window-signal-lipschitz start ceiling) step))
                   (car (lw-signal-bounds point ceiling numerator denominator error))))
           (lw-window-signal-search start step ceiling numerator denominator error))
  :hints (("Goal"
           :use ((:instance lw-window-signal-search-complete
                   (peak (car (lw-signal-bounds point ceiling numerator denominator error)))
                   (lipschitz (lw-signal-lipschitz-factor (* start start) ceiling)))
                 (:instance lw-signal-evaluations-upper-transport
                   (lower start) (cap (* start start)) (addresses (lw-window-mesh start step)))
                 lw-window-mesh-contained
                 (:instance lw-window-bracket-contained (epsilon step))
                 (:instance lw-window-bracket-sound (epsilon step))
                 (:instance lw-addresses-between-enlarge-upper
                   (lower start) (upper (car (lw-window-bracket start step)))
                   (cap (* start start)) (addresses (lw-window-mesh start step)))
                 lw-window-point-coarse-cap
                 (:instance lw-signal-lipschitz-factor-valid (cap (* start start)))
                 (:instance lw-signal-bounds-valid (value point)))
           :in-theory (disable lw-window-signal-search lw-signal-search lw-first-above
                               lw-window-signal-search-complete lw-signal-evaluations-upper-transport
                               lw-window-mesh lw-window-bracket lw-window-mesh-contained
                               lw-window-bracket-contained lw-window-bracket-sound
                               lw-addresses-between lw-addresses-between-enlarge-upper
                               lw-window-point-coarse-cap lw-signal-bounds lw-signal-bounds-valid
                               lw-signal-lipschitz-factor lw-signal-lipschitz-factor-valid
                               lw-lower-lipschitz lw-upper-values lw-signal-samples))))

(defun lw-landau-search-step (start ceiling)
  (/ (* 4 (+ 1 (lw-window-signal-lipschitz start ceiling)))))

(defthm lw-landau-search-parameters
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling))
           (and (rationalp (lw-landau-search-step start ceiling))
                (< 0 (lw-landau-search-step start ceiling))
                (<= (* (lw-window-signal-lipschitz start ceiling) (lw-landau-search-step start ceiling)) 1/4)))
  :hints (("Goal" :use ((:instance lw-signal-lipschitz-factor-valid (cap (* start start)))
                        (:instance lw-positive-division-bound
                          (numerator (lw-window-signal-lipschitz start ceiling))
                          (divisor (* 4 (+ 1 (lw-window-signal-lipschitz start ceiling)))) (bound 1/4)))
                  :in-theory (disable lw-signal-lipschitz-factor lw-signal-lipschitz-factor-valid)
                  :nonlinearp t)))

(defun lw-landau-window-search (start ceiling numerator denominator)
  (lw-window-signal-search start (lw-landau-search-step start ceiling) ceiling numerator denominator 1/4))

(defun lw-landau-window-address (start ceiling found)
  (lw-window-signal-address start (lw-landau-search-step start ceiling) found))

(defthm lw-landau-window-search-certificate
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (lw-landau-window-search start ceiling numerator denominator))
           (let* ((found (lw-landau-window-search start ceiling numerator denominator))
                  (address (lw-landau-window-address start ceiling found)))
             (and (rationalp address) (<= start address)
                  (<= (* address address) (* start start start))
                  (< 0 (cadr found))
                  (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal" :use ((:instance lw-window-signal-search-certificate
                          (step (lw-landau-search-step start ceiling)) (error 1/4))
                        lw-landau-search-parameters)
                  :in-theory (disable lw-landau-search-step lw-window-signal-search
                                      lw-window-signal-address lw-window-signal-search-certificate
                                      lw-landau-search-parameters lw-signal-bounds))))

; Search failure produces a uniform encoded ceiling, for every rational
; point of the window. The point is universally quantified, not supplied to
; or searched by this theorem as a pre-existing analytic peak witness.
(defthm lw-landau-search-failure-signal-ceiling
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp point) (<= start point) (<= (* point point) (* start start start)))
           (<= (cdr (lw-signal-bounds point ceiling numerator denominator 1/4)) 1))
  :hints (("Goal" :use ((:instance lw-window-signal-search-from-peak
                          (step (lw-landau-search-step start ceiling)) (error 1/4))
                        lw-landau-search-parameters
                        (:instance lw-signal-bounds-valid (value point) (error 1/4))
                        (:instance lw-signal-bounds-width (value point) (error 1/4)))
                  :in-theory (disable lw-landau-search-step lw-window-signal-search
                                      lw-window-signal-search-from-peak lw-landau-search-parameters
                                      lw-signal-bounds lw-signal-bounds-valid lw-signal-bounds-width))))

(defthm lw-landau-search-failure-gz-ceiling
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp point) (<= start point) (<= (* point point) (* start start start)))
           (let ((epsilon (lw-signal-precision point ceiling 1/4)))
             (<= (cdr (lw-gz-bounds-raw point (lw-signal-count point) epsilon))
                 (* (+ ceiling 1) (car (lw-rpow-bounds point numerator denominator epsilon))))))
  :hints (("Goal" :use (lw-landau-search-failure-signal-ceiling
                        (:instance lw-signal-precision-positive (value point) (error 1/4))
                        (:instance lw-rpow-bounds-sound
                          (value point) (epsilon (lw-signal-precision point ceiling 1/4)))
                        (:instance lw-gz-bounds-raw-valid
                          (value point) (count (lw-signal-count point))
                          (epsilon (lw-signal-precision point ceiling 1/4))))
                  :in-theory (union-theories
                               (theory 'ground-zero)
                               '(lw-signal-bounds lw-signal-bounds-raw lw-interval-sub lw-interval-scale
                                 lw-intervalp lw-sc-times-negation lw-sc-multiply-left-commutes
                                 lw-sc-sum-left-distribute)))))

(assert-event (let* ((left 3/2) (right 7/4) (cap 2) (ceiling 1) (error 1))
                (<= (- (car (lw-signal-bounds left ceiling 1 2 error))
                       (cdr (lw-signal-bounds right ceiling 1 2 error)))
                    (* (lw-signal-lipschitz-factor cap ceiling) (abs (- left right))))))
