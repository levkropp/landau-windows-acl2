(in-package "ACL2")

(include-book "pole-dominance")
(include-book "rpow-continuity")

(defun lw-polynomial-decay-increment (ratio degree)
  (/ (- 1 ratio) (* 2 (+ 1 degree))))

(defun lw-polynomial-decay-base (ratio degree)
  (/ (- 1 (lw-polynomial-decay-increment ratio degree))))

(defun lw-polynomial-decay-rate (ratio)
  (/ (* 2 ratio) (+ 1 ratio)))

(defun lw-polynomial-decay-scale (ratio degree offset)
  (+ 1 offset (/ (- (lw-polynomial-decay-base ratio degree) 1))))

(defun lw-polynomial-decay-index (ratio degree offset mass tolerance)
  (lw-resolvent-truncation-count
   (lw-polynomial-decay-rate ratio)
   (/ tolerance
      (+ 1 (* mass (lw-rational-power
                    (lw-polynomial-decay-scale ratio degree offset) degree))))))

(local (in-theory (disable lw-rational-power lw-reciprocal-antitone
                           lw-rational-power-at-least-one
                           lw-rational-power-nonnegative
                           lw-rational-power-monotone-base
                           lw-geometric-index lw-resolvent-truncation-count)))

(local (defthm lw-ped-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ped-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ped-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ped-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ped-times-negative (a b) (b a)))
                 :in-theory (disable lw-ped-times-negative)))))

(local (defthm lw-ped-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ped-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ped-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ped-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ped-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ped-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ped-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local
 (defthm lw-ped-times-order
   (implies (and (rationalp a) (rationalp b) (<= a b)
                 (rationalp factor) (<= 0 factor))
            (<= (* factor a) (* factor b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ped-bernoulli-step
   (implies (and (posp degree) (rationalp delta) (<= 0 delta))
            (<= (- 1 (* degree delta))
                (* (- 1 delta) (- 1 (* (- degree 1) delta)))))
   :hints (("Goal"
            :use ((:instance lw-ped-times-order (a 0) (b delta) (factor delta))
                  (:instance lw-ped-times-order (a 0) (b (- degree 1))
                    (factor (* delta delta))))
            :nonlinearp t))
   :rule-classes nil))

; Bernoulli on the reciprocal base, whose value is below one.
(local
 (defthm lw-ped-bernoulli-below-one
   (implies (and (rationalp delta) (<= 0 delta) (<= delta 1)
                 (natp degree))
            (<= (- 1 (* degree delta))
                (lw-rational-power (- 1 delta) degree)))
   :hints (("Goal" :induct (lw-rational-power (- 1 delta) degree)
                   :in-theory (enable (:induction lw-rational-power)))
           ("Subgoal *1/1" :expand ((lw-rational-power (- 1 delta) 0)))
           ("Subgoal *1/2"
            :expand ((lw-rational-power (- 1 delta) degree))
            :use (lw-ped-bernoulli-step
                  (:instance lw-ped-times-order
                   (a (- 1 (* (- degree 1) delta)))
                   (b (lw-rational-power (- 1 delta) (- degree 1)))
                   (factor (- 1 delta))))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ped-increment-budget
   (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1) (natp degree))
            (let ((delta (lw-polynomial-decay-increment ratio degree)))
              (and (rationalp delta) (< 0 delta) (< delta 1)
                   (<= (/ (+ 1 ratio) 2) (- 1 (* degree delta))))))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x (* 2 (+ 1 degree))))
                  (:instance lw-ped-times-order (a degree) (b (+ 1 degree))
                    (factor (/ (- 1 ratio) (* 2 (+ 1 degree))))))
            :in-theory (e/d (lw-polynomial-decay-increment) (inverse-of-*))
            :nonlinearp t))
   :rule-classes nil))

(local (defthm lw-ped-right-one
         (equal (* value 1) (fix value))))

(local
 (defthm lw-ped-inverse-unique
   (implies (and (rationalp value) (rationalp inverse) (< 0 value)
                 (equal (* value inverse) 1))
            (equal inverse (/ value)))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x value))
                  (:instance associativity-of-* (x (/ value)) (y value) (z inverse))
                  (:instance commutativity-of-* (x (/ value)) (y value)))
            :in-theory (disable inverse-of-* associativity-of-*
                                commutativity-of-* lw-ped-left-commutes
                                lw-ped-left-distributes distributivity)))
   :rule-classes nil))

(local
 (defthm lw-ped-rate-data
   (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1))
            (let ((rate (lw-polynomial-decay-rate ratio)))
              (and (rationalp rate) (<= 0 rate) (< rate 1)
                   (equal (* (/ (+ 1 ratio) 2) rate) ratio))))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x (+ 1 ratio)))
                  (:instance lw-ped-times-order
                    (a 0) (b (* 2 ratio)) (factor (/ (+ 1 ratio))))
                  (:instance lw-ped-times-order
                    (a (* 2 ratio)) (b (+ 1 ratio)) (factor (/ (+ 1 ratio)))))
            :in-theory (e/d (lw-polynomial-decay-rate) (inverse-of-*))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ped-inverse-factor
   (implies (and (rationalp value) (not (equal value 0)) (rationalp factor))
            (equal (* value (* (/ value) factor)) factor))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x value))
                  (:instance associativity-of-* (x value) (y (/ value)) (z factor)))
            :in-theory (disable inverse-of-* associativity-of-*
                                commutativity-of-* lw-ped-left-commutes)))
   :rule-classes nil))

(local
 (defthm lw-ped-multiply-by-reciprocal-bound
   (implies (and (rationalp lower) (< 0 lower)
                 (rationalp value) (<= lower value)
                 (rationalp inverse) (equal (* value inverse) 1)
                 (rationalp ratio) (<= 0 ratio)
                 (rationalp rate) (equal (* lower rate) ratio))
            (<= (* ratio inverse) rate))
   :hints (("Goal"
            :use (lw-ped-inverse-unique
                  (:instance lw-reciprocal-antitone (left lower) (right value))
                  (:instance lw-ped-times-order
                    (a inverse) (b (/ lower)) (factor ratio))
                  (:instance lw-ped-inverse-factor (value lower) (factor rate)))
            :in-theory (disable inverse-of-*)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ped-base-rate
   (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1) (natp degree))
            (let* ((base (lw-polynomial-decay-base ratio degree))
                   (rate (lw-polynomial-decay-rate ratio)))
              (and (rationalp base) (< 1 base)
                   (rationalp rate) (<= 0 rate) (< rate 1)
                   (<= (* ratio (lw-rational-power base degree)) rate))))
   :hints (("Goal"
            :use (lw-ped-increment-budget lw-ped-rate-data
                  (:instance lw-ped-bernoulli-below-one
                   (delta (lw-polynomial-decay-increment ratio degree)))
                  (:instance lw-rational-power-reciprocal-pair
                   (value (- 1 (lw-polynomial-decay-increment ratio degree)))
                   (index degree))
                  (:instance lw-reciprocal-antitone
                   (left (- 1 (lw-polynomial-decay-increment ratio degree))) (right 1))
                  (:instance lw-ped-multiply-by-reciprocal-bound
                   (lower (/ (+ 1 ratio) 2))
                   (value (lw-rational-power
                           (- 1 (lw-polynomial-decay-increment ratio degree)) degree))
                   (inverse (lw-rational-power (lw-polynomial-decay-base ratio degree) degree))
                   (rate (lw-polynomial-decay-rate ratio)))
                  (:instance inverse-of-* (x (- 1 (lw-polynomial-decay-increment ratio degree)))))
            :in-theory (e/d (lw-polynomial-decay-base)
                            (lw-polynomial-decay-increment lw-polynomial-decay-rate
                             inverse-of-* lw-rational-power-reciprocal-pair))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ped-linear-majorant
   (implies (and (rationalp base) (< 1 base) (rationalp offset) (<= 0 offset)
                 (natp index))
            (let ((scale (+ 1 offset (/ (- base 1)))))
              (and (rationalp scale) (< 0 scale)
                   (<= (+ offset index)
                       (* scale (lw-rational-power base index))))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-bernoulli (exponent index))
                  (:instance lw-ped-inverse-factor (value (- base 1)) (factor index))
                  (:instance lw-ped-times-order (a 0) (b (- base 1)) (factor index))
                  (:instance inverse-of-* (x (- base 1)))
                  (:instance lw-ped-times-order
                   (a (+ 1 (* index (- base 1)))) (b (lw-rational-power base index))
                   (factor (+ 1 offset (/ (- base 1))))))
            :in-theory (disable inverse-of-* lw-rational-power-bernoulli)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ped-power-swap
   (implies (and (rationalp base) (natp degree) (natp index))
            (equal (lw-rational-power (lw-rational-power base index) degree)
                   (lw-rational-power (lw-rational-power base degree) index)))
   :hints (("Goal" :induct (lw-rational-power base degree)
                   :in-theory (enable (:induction lw-rational-power)))
           ("Subgoal *1/1"
            :expand ((lw-rational-power (lw-rational-power base index) 0)
                     (lw-rational-power base 0)))
           ("Subgoal *1/2"
            :expand ((lw-rational-power (lw-rational-power base index) degree)
                     (lw-rational-power base degree))
            :use ((:instance lw-rational-power-product
                   (left base) (right (lw-rational-power base (- degree 1)))
                   (exponent index)))
            :in-theory (disable lw-rational-power-product)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ped-scale-majorant
   (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1)
                 (natp degree) (rationalp offset) (<= 0 offset) (natp index))
            (let ((scale (lw-polynomial-decay-scale ratio degree offset))
                  (rate (lw-polynomial-decay-rate ratio)))
              (and (rationalp scale) (< 0 scale)
                   (rationalp rate) (<= 0 rate) (< rate 1)
                   (<= (* (lw-rational-power (+ offset index) degree)
                          (lw-rational-power ratio index))
                       (* (lw-rational-power scale degree)
                          (lw-rational-power rate index))))))
   :hints (("Goal"
            :use (lw-ped-base-rate
                  (:instance lw-ped-power-swap (base (lw-polynomial-decay-base ratio degree)))
                  (:instance lw-ped-linear-majorant
                   (base (lw-polynomial-decay-base ratio degree)))
                  (:instance lw-rational-power-monotone-base
                   (left (+ offset index))
                   (right (* (lw-polynomial-decay-scale ratio degree offset)
                             (lw-rational-power (lw-polynomial-decay-base ratio degree) index)))
                   (exponent degree))
                  (:instance lw-rational-power-monotone-base
                   (left (* ratio (lw-rational-power (lw-polynomial-decay-base ratio degree) degree)))
                   (right (lw-polynomial-decay-rate ratio)) (exponent index))
                  (:instance lw-rational-power-nonnegative (base ratio) (exponent index))
                  (:instance lw-rational-power-nonnegative
                   (base (lw-polynomial-decay-scale ratio degree offset)) (exponent degree))
                  (:instance lw-rational-power-nonnegative
                   (base (lw-polynomial-decay-base ratio degree)) (exponent degree))
                  (:instance lw-rational-power-nonnegative
                   (base (lw-polynomial-decay-base ratio degree)) (exponent index))
                  (:instance lw-rational-power-product
                   (left (lw-polynomial-decay-scale ratio degree offset))
                   (right (lw-rational-power (lw-polynomial-decay-base ratio degree) index))
                   (exponent degree))
                  (:instance lw-rational-power-product
                   (left ratio)
                   (right (lw-rational-power (lw-polynomial-decay-base ratio degree) degree))
                   (exponent index))
                  (:instance lw-ped-times-order
                   (a (lw-rational-power (+ offset index) degree))
                   (b (* (lw-rational-power (lw-polynomial-decay-scale ratio degree offset) degree) (lw-rational-power (lw-rational-power (lw-polynomial-decay-base ratio degree) degree) index)))
                   (factor (lw-rational-power ratio index)))
                  (:instance lw-ped-times-order
                   (a (lw-rational-power (* ratio (lw-rational-power (lw-polynomial-decay-base ratio degree) degree)) index))
                   (b (lw-rational-power (lw-polynomial-decay-rate ratio) index))
                   (factor (lw-rational-power (lw-polynomial-decay-scale ratio degree offset) degree)))
                  (:instance lw-ped-times-order
                   (a 0) (b ratio) (factor (lw-rational-power (lw-polynomial-decay-base ratio degree) degree))))
            :in-theory (e/d (lw-polynomial-decay-scale)
                            (lw-polynomial-decay-base lw-polynomial-decay-rate lw-polynomial-decay-increment
                             lw-rational-power-product))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ped-cap-budget
   (implies (and (rationalp cap) (<= 0 cap)
                 (rationalp value) (rationalp tolerance) (< 0 tolerance)
                 (<= value (/ tolerance (+ 1 cap))))
            (<= (* cap value) tolerance))
   :hints (("Goal"
            :use ((:instance lw-ped-times-order
                   (a value) (b (/ tolerance (+ 1 cap))) (factor cap))
                  (:instance lw-ped-times-order
                   (a cap) (b (+ 1 cap)) (factor (/ tolerance (+ 1 cap))))
                  (:instance lw-ped-inverse-factor (value (+ 1 cap)) (factor tolerance)))
            :nonlinearp t))
   :rule-classes nil))

; This threshold works for every later integer order, including an
; order selected from a fixed-width block after the threshold is set.
(defthm lw-polynomial-exponential-computed-decay
  (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1)
                (natp degree) (rationalp offset) (<= 0 offset)
                (rationalp mass) (<= 0 mass)
                (rationalp tolerance) (< 0 tolerance)
                (natp index)
                (<= (lw-polynomial-decay-index ratio degree offset mass tolerance) index))
           (<= (* mass (lw-rational-power (+ offset index) degree)
                       (lw-rational-power ratio index))
               tolerance))
  :hints (("Goal"
           :use (lw-ped-scale-majorant
                 (:instance lw-rational-power-nonnegative
                  (base (lw-polynomial-decay-scale ratio degree offset)) (exponent degree))
                 (:instance lw-rational-power-computed-decay
                  (ratio (lw-polynomial-decay-rate ratio))
                  (error (/ tolerance
                          (+ 1 (* mass (lw-rational-power
                         (lw-polynomial-decay-scale ratio degree offset) degree))))))
                 (:instance lw-ped-times-order
                  (a 0) (b mass) (factor (lw-rational-power (lw-polynomial-decay-scale ratio degree offset) degree)))
                 (:instance lw-ped-times-order
                  (a (* (lw-rational-power (+ offset index) degree) (lw-rational-power ratio index)))
                  (b (* (lw-rational-power (lw-polynomial-decay-scale ratio degree offset) degree) (lw-rational-power (lw-polynomial-decay-rate ratio) index)))
                  (factor mass))
                 (:instance lw-ped-cap-budget (cap (* mass (lw-rational-power (lw-polynomial-decay-scale ratio degree offset) degree))) (value (lw-rational-power (lw-polynomial-decay-rate ratio) index))))
           :in-theory (e/d (lw-polynomial-decay-index)
                           (inverse-of-* lw-polynomial-decay-base
                            lw-polynomial-decay-rate lw-polynomial-decay-increment
                            lw-polynomial-decay-scale lw-rational-power-computed-decay))
           :do-not-induct t))
  :rule-classes nil)
