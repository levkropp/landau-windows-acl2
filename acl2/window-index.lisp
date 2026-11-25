(in-package "ACL2")

(include-book "log-bounds")
(include-book "landau-bounds")

; A bounded rational ceiling, proved without importing a floor oracle.
(defun lw-ceiling-loop (value fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (<= value 0)) 0
    (+ 1 (lw-ceiling-loop (- value 1) (- fuel 1)))))

(defthm lw-ceiling-loop-natural
  (natp (lw-ceiling-loop value fuel))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-ceiling-loop-bracket
  (implies (and (rationalp value) (<= 0 value)
                (natp fuel) (<= value fuel))
           (and (<= value (lw-ceiling-loop value fuel))
                (< (lw-ceiling-loop value fuel) (+ value 1))))
  :hints (("Goal" :induct (lw-ceiling-loop value fuel))))

(defun lw-ceiling-rational (value)
  (lw-ceiling-loop value (+ 1 (lw-precision-fuel value 1))))

(defthm lw-ceiling-rational-natural
  (natp (lw-ceiling-rational value))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-ceiling-rational-bracket
  (implies (and (rationalp value) (<= 0 value))
           (and (<= value (lw-ceiling-rational value))
                (< (lw-ceiling-rational value) (+ value 1))))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate (width value) (epsilon 1))
                        (:instance lw-ceiling-loop-bracket
                          (fuel (+ 1 (lw-precision-fuel value 1)))))
                  :in-theory (disable lw-ceiling-loop lw-precision-fuel
                                      lw-ceiling-loop-bracket lw-precision-fuel-adequate))))

(defun lw-window-index-from-log (lower)
  (lw-ceiling-rational (* 615/2 lower)))

(defthm lw-window-index-natural
  (natp (lw-window-index-from-log lower))
  :rule-classes (:rewrite :type-prescription))

; These rational inequalities certify the band simultaneously for every
; real U in [lower,upper]. They allow all rounding and log-enclosure error.
(defthm lw-window-index-certified-band
  (implies (and (rationalp lower) (rationalp upper)
                (<= 3 lower) (<= lower upper) (<= (- upper lower) 1/1000))
           (and (<= 1 (lw-window-index-from-log lower))
                (<= (* 6061/20 upper) (lw-window-index-from-log lower))
                (<= (lw-window-index-from-log lower) (* 625/2 lower))))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value (* 615/2 lower))))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket))))

(defthm lw-window-index-threshold
  (implies (and (rationalp lower) (<= 0 lower)
                (rationalp threshold) (<= threshold (* 615/2 lower)))
           (<= threshold (lw-window-index-from-log lower)))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value (* 615/2 lower))))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket))))

(defun lw-window-index (start)
  (lw-window-index-from-log (car (lw-log-bounds start 1/1000))))

(defthm lw-window-index-log-band
  (implies (and (rationalp start) (<= 1 start)
                (<= 3 (car (lw-log-bounds start 1/1000))))
           (and (natp (lw-window-index start))
                (<= 1 (lw-window-index start))
                (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000)))
                    (lw-window-index start))
                (<= (lw-window-index start)
                    (* 625/2 (car (lw-log-bounds start 1/1000))))))
  :hints (("Goal" :use ((:instance lw-log-bounds-interval (value start) (epsilon 1/1000))
                        (:instance lw-log-bounds-width (value start) (epsilon 1/1000))
                        (:instance lw-window-index-certified-band
                          (lower (car (lw-log-bounds start 1/1000)))
                          (upper (cdr (lw-log-bounds start 1/1000)))))
                  :in-theory (disable lw-log-bounds lw-log-bounds-interval lw-log-bounds-width
                                      lw-window-index-from-log lw-window-index-certified-band))))

(defun lw-window-index-check (start index)
  (let ((bounds (lw-log-bounds start 1/1000)))
    (and (natp index) (<= 1 index) (<= 3 (car bounds))
         (<= (* 6061/20 (cdr bounds)) index)
         (<= index (* 625/2 (car bounds))))))

(defthm lw-window-index-check-computed
  (implies (and (rationalp start) (<= 1 start)
                (<= 3 (car (lw-log-bounds start 1/1000))))
           (lw-window-index-check start (lw-window-index start)))
  :hints (("Goal" :use (lw-window-index-log-band)
                  :in-theory (disable lw-log-bounds lw-window-index lw-window-index-log-band))))

(defthm lw-window-index-geometric-bounds
  (implies (and (rationalp start) (<= 1 start)
                (<= 3 (car (lw-log-bounds start 1/1000)))
                (rationalp growth) (< 1 growth)
                (rationalp pole-ratio) (< 1 pole-ratio)
                (rationalp tail-ratio) (< 1 tail-ratio)
                (rationalp pole-target) (<= 0 pole-target)
                (rationalp tail-target) (<= 0 tail-target)
                (rationalp ceiling-target) (<= 0 ceiling-target)
                (<= (lw-landau-index growth pole-ratio tail-ratio
                                     pole-target tail-target ceiling-target)
                    (* 615/2 (car (lw-log-bounds start 1/1000)))))
           (and (<= ceiling-target (lw-rational-power growth (lw-window-index start)))
                (<= pole-target (lw-rational-power pole-ratio (lw-window-index start)))
                (<= tail-target (lw-rational-power tail-ratio (lw-window-index start)))))
  :hints (("Goal" :use ((:instance lw-window-index-threshold
                          (lower (car (lw-log-bounds start 1/1000)))
                          (threshold (lw-landau-index growth pole-ratio tail-ratio
                                                       pole-target tail-target ceiling-target)))
                        (:instance lw-landau-index-sufficient (exponent (lw-window-index start)))
                        lw-window-index-log-band
                        (:instance lw-log-bounds-interval (value start) (epsilon 1/1000)))
                  :in-theory (disable lw-landau-index lw-landau-index-sufficient lw-rational-power
                                      lw-log-bounds lw-log-bounds-interval lw-window-index-from-log
                                      lw-window-index-threshold lw-window-index-log-band))))

(local
 (defthm lw-index-multiply-inequality
   (implies (and (rationalp left) (rationalp right) (<= left right)
                 (rationalp factor) (<= 0 factor))
            (<= (* left factor) (* right factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm lw-positive-division-lower-bound
  (implies (and (rationalp numerator) (rationalp divisor) (< 0 divisor)
                (rationalp bound) (<= (* bound divisor) numerator))
           (<= bound (/ numerator divisor)))
  :hints (("Goal" :use ((:instance inverse-of-* (x divisor))
                        (:instance lw-index-multiply-inequality
                          (left (* bound divisor)) (right numerator) (factor (/ divisor))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))
  :rule-classes nil)

(defthm lw-window-kernel-ratios
  (implies (and (rationalp u) (< 0 u) (posp index)
                (<= (* 6061/20 u) index) (<= index (* 625/2 u)))
           (and (<= 4/5 (/ (* 250 u) index))
                (<= (/ (* 250 u) index) 33/40)
                (<= 6/5 (/ (* 375 u) index))
                (<= (/ (* 375 u) index) 31/25)))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* 250 u)) (divisor index) (bound 33/40))
                        (:instance lw-positive-division-bound
                          (numerator (* 375 u)) (divisor index) (bound 31/25))
                        (:instance lw-positive-division-lower-bound
                          (numerator (* 250 u)) (divisor index) (bound 4/5))
                        (:instance lw-positive-division-lower-bound
                          (numerator (* 375 u)) (divisor index) (bound 6/5))))))

(assert-event (equal (lw-ceiling-rational 7/2) 4))
(assert-event (equal (lw-ceiling-rational 3) 3))
(assert-event (equal (lw-window-index-from-log 3) 923))
