(in-package "ACL2")

(include-book "dirichlet-hyperbola-tail")
(include-book "zeta-series")

; Compare one shared rational precision with the actual native
; model/coefficient/node requests. All three coefficient families
; (Mangoldt, logarithm and ordinary) use the same transport argument.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
 lw-complex-mul lw-complex-diskp lw-diskp lw-complex-scale-product
 lw-complex-sub-add lw-complex-sub-add-first lw-complex-sub-add-cancel
 lw-dirichlet-sample lw-complex-log-ramp-independent-exp lw-mangoldt-bounds
 lw-zeta-dirichlet-weight lw-prime-power-data lw-log-bounds
 lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-exp-lipschitz-cap
 lw-complex-dirichlet-prime-sum lw-complex-zeta-partial-sum
 lw-complex-dirichlet-finite-value lw-complex-zeta-finite-value
 lw-complex-dirichlet-series-value lw-complex-zeta-series-value
 lw-dirichlet-finite-model-precision lw-dirichlet-finite-coefficient-precision
 lw-dirichlet-finite-node-precision lw-dirichlet-weighted-prefix
 lw-dirichlet-node-prefix lw-dirichlet-coefficient lw-dirichlet-node
 lw-mangoldt-dirichlet-weights lw-dirichlet-sample-table
 lw-complex-mangoldt-canonical-prefix lw-complex-ordinary-canonical-prefix
 lw-complex-log-dirichlet-sum)))

(local (defthm lw-cnp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cnp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cnp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cnp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cnp-times-negative (a b) (b a)))
                 :in-theory (disable lw-cnp-times-negative)))))

(local (defthm lw-cnp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cnp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cnp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cnp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cnp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cnp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cnp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cnp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cnp-left-commutes)))))

(local (defthm lw-cnp-zero-scale
 (equal (lw-complex-scale 0 point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-scale)))))

(local (defthm lw-cnp-mangoldt-one
 (equal (car (lw-mangoldt-bounds 1 error)) 0)
 :hints (("Goal" :in-theory (enable lw-mangoldt-bounds)))))

(local (defthm lw-cnp-sample-one
 (equal (lw-dirichlet-sample rate height 1 log-error node-error) (cons 1 0))
 :hints (("Goal" :in-theory (enable lw-dirichlet-sample)))))

(defun lw-common-dirichlet-coefficient (mangoldtp logp index error)
 (if mangoldtp (car (lw-mangoldt-bounds index error))
   (lw-zeta-dirichlet-weight logp index error)))

(defthm lw-common-dirichlet-coefficient-valid
 (implies (and (natp index) (< 1 index) (rationalp error) (< 0 error))
  (and (rationalp (lw-common-dirichlet-coefficient mangoldtp logp index error))
       (<= 0 (lw-common-dirichlet-coefficient mangoldtp logp index error))
       (<= (lw-common-dirichlet-coefficient mangoldtp logp index error) index)))
 :hints (("Goal"
  :use ((:instance lw-mangoldt-lower-coarse (epsilon error))
        (:instance lw-zeta-dirichlet-weight-valid (epsilon error)))
  :in-theory (disable lw-mangoldt-lower-coarse lw-zeta-dirichlet-weight-valid))))

(defthm lw-common-dirichlet-coefficient-cauchy
 (implies (and (natp index) (< 1 index)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (<= (abs (- (lw-common-dirichlet-coefficient mangoldtp logp index left-error)
              (lw-common-dirichlet-coefficient mangoldtp logp index right-error)))
      (+ left-error right-error)))
 :hints (("Goal"
  :use (lw-mangoldt-lower-cauchy lw-zeta-dirichlet-weight-cauchy)
  :in-theory (disable lw-mangoldt-lower-cauchy lw-zeta-dirichlet-weight-cauchy))))

(local (in-theory (disable lw-common-dirichlet-coefficient)))

(defun lw-complex-common-dirichlet-prefix (mangoldtp logp rate height count error)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (cons 0 0)
   (if (equal count 1)
       (if (or mangoldtp logp) (cons 0 0) (cons 1 0))
     (lw-complex-add
      (lw-complex-scale (lw-common-dirichlet-coefficient mangoldtp logp count error)
                        (lw-dirichlet-sample rate height count error error))
      (lw-complex-common-dirichlet-prefix mangoldtp logp rate height (- count 1) error)))))

(defthm lw-complex-common-dirichlet-prefix-rational
 (implies (and (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count error))))

(defthm lw-mangoldt-table-common-prefix
 (implies (and (natp total) (natp count) (<= count total)
               (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
  (equal
   (lw-dirichlet-weighted-prefix
    count (lw-mangoldt-dirichlet-weights total error)
    (lw-dirichlet-sample-table rate height total error error))
   (lw-complex-common-dirichlet-prefix t nil rate height count error)))
 :hints (("Goal" :induct (lw-complex-common-dirichlet-prefix t nil rate height count error)
                 :in-theory (enable lw-dirichlet-weighted-prefix lw-common-dirichlet-coefficient))))

(defthm lw-ordinary-table-common-prefix
 (implies (and (natp total) (natp count) (<= count total)
               (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
  (equal
   (lw-dirichlet-node-prefix count (lw-dirichlet-sample-table rate height total error error))
   (lw-complex-common-dirichlet-prefix nil nil rate height count error)))
 :hints (("Goal" :induct (lw-complex-common-dirichlet-prefix nil nil rate height count error)
                 :in-theory (enable lw-dirichlet-node-prefix lw-common-dirichlet-coefficient
                                    lw-zeta-dirichlet-weight))))

(defthm lw-mangoldt-canonical-common-prefix
 (implies (and (natp count) (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
  (equal (lw-complex-mangoldt-canonical-prefix rate height count error)
         (lw-complex-common-dirichlet-prefix t nil rate height count error)))
 :hints (("Goal" :use ((:instance lw-mangoldt-table-common-prefix (total count)))
                 :in-theory (e/d (lw-complex-mangoldt-canonical-prefix)
                                 (lw-mangoldt-table-common-prefix)))))

(defthm lw-ordinary-canonical-common-prefix
 (implies (and (natp count) (rationalp rate) (rationalp height) (rationalp error) (< 0 error))
  (equal (lw-complex-ordinary-canonical-prefix rate height count error)
         (lw-complex-common-dirichlet-prefix nil nil rate height count error)))
 :hints (("Goal" :use ((:instance lw-ordinary-table-common-prefix (total count)))
                 :in-theory (e/d (lw-complex-ordinary-canonical-prefix)
                                 (lw-ordinary-table-common-prefix)))))

(defthm lw-log-canonical-common-prefix
 (equal (lw-complex-log-dirichlet-sum rate height count error error error)
        (lw-complex-common-dirichlet-prefix nil t rate height count error))
 :hints (("Goal" :induct (lw-complex-common-dirichlet-prefix nil t rate height count error)
                 :in-theory (enable lw-complex-log-dirichlet-sum lw-common-dirichlet-coefficient
                                    lw-zeta-dirichlet-weight))))

(local (in-theory (disable lw-complex-common-dirichlet-prefix)))

(local (defthm lw-cnp-division-small
 (implies (and (rationalp divisor) (<= 1 divisor) (rationalp value) (< 0 value))
  (and (rationalp (* value (/ divisor))) (< 0 (* value (/ divisor)))
       (<= (* value (/ divisor)) value)))
 :hints (("Goal"
  :use ((:instance lw-reciprocal-antitone (left 1) (right divisor))
        (:instance lw-cnp-multiply-order (a (/ divisor)) (b 1) (factor value)))
  :in-theory (disable lw-reciprocal-antitone)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-smoothed-ramp-log-error-small
 (implies (and (natp index) (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-log-error index total model-error))
       (< 0 (lw-smoothed-ramp-log-error index total model-error))
       (<= (lw-smoothed-ramp-log-error index total model-error) model-error)))
 :hints (("Goal"
  :use ((:instance lw-smoothed-ramp-log-error-adequate (error model-error))
        (:instance lw-exp-lipschitz-cap-valid (cap index))
        (:instance lw-cnp-division-small (divisor (+ 1 total)) (value (* 1/16 model-error)))
        (:instance lw-cnp-multiply-order
         (a 1) (b (lw-exp-lipschitz-cap index))
         (factor (lw-smoothed-ramp-log-error index total model-error))))
  :in-theory (e/d (lw-smoothed-ramp-unit-error)
                  (lw-smoothed-ramp-log-error-adequate lw-exp-lipschitz-cap-valid))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-dirichlet-finite-precisions-small
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (and (<= (lw-dirichlet-finite-model-precision rate height error) error)
       (<= (lw-dirichlet-finite-coefficient-precision count error) error)
       (<= (lw-dirichlet-finite-node-precision count error) error)))
 :hints (("Goal"
  :use ((:instance lw-cnp-division-small (divisor (+ 1 (* 2 (+ rate (abs height))))) (value error))
        (:instance lw-cnp-division-small (divisor (* 8 (+ 1 count))) (value error))
        (:instance lw-cnp-division-small (divisor (* 64 (+ 1 (* count (+ 1 count))))) (value error)))
  :in-theory (enable lw-dirichlet-finite-model-precision lw-dirichlet-finite-coefficient-precision
                     lw-dirichlet-finite-node-precision)
  :nonlinearp t :do-not-induct t)))

(local (defthm lw-cnp-coefficient-change
 (implies (and (rationalp a) (rationalp b) (lw-complexp x) (lw-complexp y))
  (equal (lw-complex-sub (lw-complex-scale a x) (lw-complex-scale b y))
         (lw-complex-add (lw-complex-scale a (lw-complex-sub x y))
                         (lw-complex-scale (- a b) y))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-scale)))))

(local (defthm lw-cnp-weighted-error
 (implies (and (rationalp a) (rationalp b) (rationalp index) (<= 0 a) (<= a index)
               (rationalp coefficient-budget) (<= 0 coefficient-budget)
               (<= (abs (- a b)) coefficient-budget)
               (rationalp node-budget) (<= 0 node-budget)
               (lw-complexp x) (lw-complexp y)
               (lw-complex-diskp (lw-complex-sub x y) node-budget) (lw-complex-diskp y 2))
  (lw-complex-diskp (lw-complex-sub (lw-complex-scale a x) (lw-complex-scale b y))
                    (+ (* index node-budget) (* 2 coefficient-budget))))
 :hints (("Goal"
  :use ((:instance lw-complex-scale-disk (factor a) (point (lw-complex-sub x y)) (radius node-budget))
        (:instance lw-complex-disk-enlarge (point (lw-complex-scale a (lw-complex-sub x y)))
         (radius (* a node-budget)) (cap (* index node-budget)))
        (:instance lw-complex-scale-disk (factor (- a b)) (point y) (radius 2))
        (:instance lw-complex-disk-enlarge (point (lw-complex-scale (- a b) y))
         (radius (* 2 (abs (- a b)))) (cap (* 2 coefficient-budget)))
        (:instance lw-complex-add-disk
         (left (lw-complex-scale a (lw-complex-sub x y)))
         (right (lw-complex-scale (- a b) y))
         (radius (* index node-budget)) (other-radius (* 2 coefficient-budget))))
  :in-theory (disable lw-complex-scale-disk lw-complex-disk-enlarge lw-complex-add-disk)
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (in-theory (disable lw-cnp-coefficient-change)))

(local (defthm lw-cnp-node-budget
 (implies (and (rationalp slope) (<= 0 slope) (rationalp request) (< 0 request)
               (rationalp bound) (< 0 bound)
               (rationalp log-error) (< 0 log-error) (<= log-error bound)
               (rationalp node-error) (< 0 node-error) (<= node-error bound))
  (<= (+ (* slope (+ request log-error)) (* 32 (+ request node-error)))
      (* (+ slope 32) (+ request bound))))
 :hints (("Goal"
  :use ((:instance lw-cnp-multiply-order (a log-error) (b bound) (factor slope)))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-common-dirichlet-term-transport
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp index) (< 1 index)
               (natp total) (rationalp request) (< 0 request) (rationalp bound) (< 0 bound)
               (rationalp model-error) (< 0 model-error) (<= model-error bound)
               (rationalp primitive-error) (< 0 primitive-error) (<= primitive-error bound)
               (rationalp node-error) (< 0 node-error) (<= node-error bound) (<= node-error 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-scale (lw-common-dirichlet-coefficient mangoldtp logp index request)
                      (lw-dirichlet-sample rate height index request request))
    (lw-complex-scale (lw-common-dirichlet-coefficient mangoldtp logp index primitive-error)
     (lw-dirichlet-sample rate height index
      (lw-smoothed-ramp-log-error index total model-error) node-error)))
   (* (+ (* index (+ (* 2 (+ rate (abs height))) 32)) 2) (+ request bound))))
 :hints (("Goal"
  :use
  ((:instance lw-common-dirichlet-coefficient-valid (error request))
   (:instance lw-common-dirichlet-coefficient-valid (error primitive-error))
   (:instance lw-common-dirichlet-coefficient-cauchy (left-error request) (right-error primitive-error))
   lw-smoothed-ramp-log-error-small
   (:instance lw-cnp-node-budget
    (slope (* 2 (+ rate (abs height))))
    (log-error (lw-smoothed-ramp-log-error index total model-error)))
   (:instance lw-complex-log-ramp-exp-log-transport
    (left-log-error request) (right-log-error (lw-smoothed-ramp-log-error index total model-error))
    (left-error request) (right-error node-error))
   (:instance lw-dirichlet-sample-unit-cap
    (log-error (lw-smoothed-ramp-log-error index total model-error)))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub (lw-dirichlet-sample rate height index request request)
     (lw-dirichlet-sample rate height index (lw-smoothed-ramp-log-error index total model-error) node-error)))
    (radius (+ (* (* 2 (+ rate (abs height)))
                  (+ request (lw-smoothed-ramp-log-error index total model-error)))
               (* 32 (+ request node-error))))
    (cap (* (+ (* 2 (+ rate (abs height))) 32) (+ request bound))))
   (:instance lw-cnp-weighted-error
    (a (lw-common-dirichlet-coefficient mangoldtp logp index request))
    (b (lw-common-dirichlet-coefficient mangoldtp logp index primitive-error))
    (coefficient-budget (+ request bound))
    (node-budget (* (+ (* 2 (+ rate (abs height))) 32) (+ request bound)))
    (x (lw-dirichlet-sample rate height index request request))
    (y (lw-dirichlet-sample rate height index (lw-smoothed-ramp-log-error index total model-error) node-error))))
  :in-theory (e/d (lw-dirichlet-sample)
   (lw-common-dirichlet-coefficient-valid lw-common-dirichlet-coefficient-cauchy
    lw-smoothed-ramp-log-error-small lw-complex-log-ramp-exp-log-transport
    lw-dirichlet-sample-unit-cap lw-complex-disk-enlarge))
  :nonlinearp nil :do-not-induct t)))

(defun lw-complex-common-native-partial
 (mangoldtp logp rate height count total model-error primitive-error node-error)
 (if mangoldtp
     (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error node-error)
   (lw-complex-zeta-partial-sum logp rate height count total model-error primitive-error node-error)))

(local (defthm lw-cnp-native-partial-small
 (implies (or (zp count) (equal count 1))
  (equal (lw-complex-common-native-partial
          mangoldtp logp rate height count total model-error primitive-error node-error)
         (if (zp count) (cons 0 0)
           (if (or mangoldtp logp) (cons 0 0) (cons 1 0)))))
 :hints (("Goal" :in-theory (enable lw-complex-dirichlet-prime-sum lw-complex-zeta-partial-sum)))))

(defthm lw-complex-common-native-partial-step
 (implies (and (natp count) (< 1 count))
  (equal
   (lw-complex-common-native-partial mangoldtp logp rate height count total model-error primitive-error node-error)
   (lw-complex-add
    (lw-complex-scale (lw-common-dirichlet-coefficient mangoldtp logp count primitive-error)
     (lw-dirichlet-sample rate height count (lw-smoothed-ramp-log-error count total model-error) node-error))
    (lw-complex-common-native-partial
     mangoldtp logp rate height (- count 1) total model-error primitive-error node-error))))
 :hints (("Goal" :in-theory (enable lw-complex-common-native-partial lw-complex-dirichlet-prime-sum
                                    lw-complex-zeta-partial-sum lw-common-dirichlet-coefficient
                                    lw-dirichlet-sample))))

(local (in-theory (disable lw-complex-common-native-partial)))

(local (defun lw-cnp-countdown (count)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) count (lw-cnp-countdown (- count 1)))))

(defthm lw-complex-common-native-partial-rational
 (implies (and (rationalp rate) (rationalp height) (natp count) (natp total)
               (rationalp model-error) (< 0 model-error)
               (rationalp primitive-error) (< 0 primitive-error)
               (rationalp node-error) (< 0 node-error))
  (lw-complexp (lw-complex-common-native-partial
               mangoldtp logp rate height count total model-error primitive-error node-error)))
 :hints (("Goal" :induct (lw-cnp-countdown count))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-small (index count)))
     :in-theory (disable lw-smoothed-ramp-log-error-small)
     :do-not-induct t))))

(defun lw-complex-common-native-finite (mangoldtp logp rate height count error)
 (if mangoldtp (lw-complex-dirichlet-finite-value rate height count error)
   (lw-complex-zeta-finite-value logp rate height count error)))

(defthm lw-complex-common-native-finite-as-partial
 (equal
  (lw-complex-common-native-finite mangoldtp logp rate height count error)
  (lw-complex-common-native-partial
   mangoldtp logp rate height count count
   (lw-dirichlet-finite-model-precision rate height error)
   (lw-dirichlet-finite-coefficient-precision count error)
   (lw-dirichlet-finite-node-precision count error)))
 :hints (("Goal" :in-theory (enable lw-complex-common-native-finite lw-complex-common-native-partial
                                    lw-complex-dirichlet-finite-value lw-complex-zeta-finite-value))))

(local (in-theory (disable lw-complex-common-native-finite)))

(defthm lw-complex-common-native-finite-rational
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-common-native-finite mangoldtp logp rate height count error)))
 :hints (("Goal" :use (lw-dirichlet-finite-precisions-valid)
                 :in-theory (disable lw-dirichlet-finite-precisions-valid)
                 :do-not-induct t)))

(defun lw-common-dirichlet-transport-cost (rate height count)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) 0
   (+ (+ (* count (+ (* 2 (+ rate (abs height))) 32)) 2)
      (lw-common-dirichlet-transport-cost rate height (- count 1)))))

(defthm lw-common-dirichlet-transport-cost-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count))
  (and (rationalp (lw-common-dirichlet-transport-cost rate height count))
       (<= 0 (lw-common-dirichlet-transport-cost rate height count))))
 :hints (("Goal" :induct (lw-cnp-countdown count) :nonlinearp t)))

(local (defthm lw-cnp-add-errors
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
               (lw-complex-diskp (lw-complex-sub a b) radius)
               (lw-complex-diskp (lw-complex-sub c d) other-radius))
  (lw-complex-diskp (lw-complex-sub (lw-complex-add a c) (lw-complex-add b d))
                    (+ radius other-radius)))
 :hints (("Goal"
  :use ((:instance lw-complex-sub-add (a a) (b c) (c b) (d d))
        (:instance lw-complex-add-disk
         (left (lw-complex-sub a b)) (right (lw-complex-sub c d))))
  :in-theory (disable lw-complex-sub-add lw-complex-add-disk)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-common-native-partial-comparison
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count) (natp total)
               (rationalp request) (< 0 request) (rationalp bound) (< 0 bound)
               (rationalp model-error) (< 0 model-error) (<= model-error bound)
               (rationalp primitive-error) (< 0 primitive-error) (<= primitive-error bound)
               (rationalp node-error) (< 0 node-error) (<= node-error bound) (<= node-error 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
    (lw-complex-common-native-partial
     mangoldtp logp rate height count total model-error primitive-error node-error))
   (* (lw-common-dirichlet-transport-cost rate height count) (+ request bound))))
 :hints (("Goal"
  :induct (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
  :in-theory (enable lw-complex-common-dirichlet-prefix))
  (and stable-under-simplificationp
   '(:use ((:instance lw-complex-common-dirichlet-term-transport (index count))
           (:instance lw-cnp-add-errors
            (a (lw-complex-scale (lw-common-dirichlet-coefficient mangoldtp logp count request)
                                 (lw-dirichlet-sample rate height count request request)))
            (b (lw-complex-scale (lw-common-dirichlet-coefficient mangoldtp logp count primitive-error)
                 (lw-dirichlet-sample rate height count (lw-smoothed-ramp-log-error count total model-error)
                                      node-error)))
            (c (lw-complex-common-dirichlet-prefix mangoldtp logp rate height (- count 1) request))
            (d (lw-complex-common-native-partial
                mangoldtp logp rate height (- count 1) total model-error primitive-error node-error))
            (radius (* (+ (* count (+ (* 2 (+ rate (abs height))) 32)) 2) (+ request bound)))
            (other-radius (* (lw-common-dirichlet-transport-cost rate height (- count 1))
                             (+ request bound)))))
     :in-theory (disable lw-complex-common-dirichlet-prefix lw-complex-common-native-partial-step
                         lw-common-dirichlet-transport-cost lw-complex-common-dirichlet-term-transport)
     :nonlinearp nil :do-not-induct t))))

(local (in-theory (disable lw-common-dirichlet-transport-cost)))

(defthm lw-complex-common-native-finite-comparison
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp request) (< 0 request) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
    (lw-complex-common-native-finite mangoldtp logp rate height count error))
   (* (lw-common-dirichlet-transport-cost rate height count) (+ request error))))
 :hints (("Goal"
  :use (lw-dirichlet-finite-precisions-valid lw-dirichlet-finite-precisions-small
        (:instance lw-complex-common-native-partial-comparison
         (total count) (bound error)
         (model-error (lw-dirichlet-finite-model-precision rate height error))
         (primitive-error (lw-dirichlet-finite-coefficient-precision count error))
         (node-error (lw-dirichlet-finite-node-precision count error))))
  :in-theory (disable lw-dirichlet-finite-precisions-valid lw-dirichlet-finite-precisions-small
                      lw-complex-common-native-partial-comparison)
  :do-not-induct t)))

(local (in-theory (disable lw-complex-common-native-finite-as-partial)))

(defun lw-complex-common-native-series (mangoldtp logp rate height error)
 (if mangoldtp (lw-complex-dirichlet-series-value rate height error)
   (lw-complex-zeta-series-value logp rate height error)))

(defthm lw-complex-common-native-series-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-common-native-series mangoldtp logp rate height error))))

(defthm lw-complex-common-native-series-finite-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
               (rationalp finite-error) (< 0 finite-error))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-native-finite mangoldtp logp rate height count finite-error)
    (lw-complex-common-native-series mangoldtp logp rate height error))
   (+ (* 3/8 error) (* 4 finite-error))))
 :hints (("Goal"
  :use (lw-complex-dirichlet-series-finite-comparison lw-complex-zeta-series-finite-comparison)
  :in-theory (e/d (lw-complex-common-native-finite)
   (lw-complex-dirichlet-series-finite-comparison lw-complex-zeta-series-finite-comparison))
  :do-not-induct t)))

(local (in-theory (disable lw-complex-common-native-series)))

(defthm lw-complex-common-prefix-series-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
               (rationalp finite-error) (< 0 finite-error) (rationalp request) (< 0 request))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
    (lw-complex-common-native-series mangoldtp logp rate height error))
   (+ (* (lw-common-dirichlet-transport-cost rate height count) (+ request finite-error))
      (* 3/8 error) (* 4 finite-error))))
 :hints (("Goal"
  :use
  ((:instance lw-complex-common-native-finite-comparison (error finite-error))
   lw-complex-common-native-series-finite-comparison
   (:instance lw-complex-difference-triangle
    (left (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request))
    (middle (lw-complex-common-native-finite mangoldtp logp rate height count finite-error))
    (right (lw-complex-common-native-series mangoldtp logp rate height error))
    (radius (* (lw-common-dirichlet-transport-cost rate height count) (+ request finite-error)))
    (other-radius (+ (* 3/8 error) (* 4 finite-error)))))
  :in-theory (disable lw-complex-common-native-finite-comparison
                      lw-complex-common-native-series-finite-comparison lw-complex-difference-triangle)
  :do-not-induct t)))

(defun lw-dirichlet-native-refinement (rate height count error)
 (/ error (+ 5 (* 2 (lw-common-dirichlet-transport-cost rate height count)))))

(local (defthm lw-cnp-refinement-algebra
 (implies (and (rationalp cost) (<= 0 cost) (rationalp error) (< 0 error))
  (let ((request (/ error (+ 5 (* 2 cost)))))
   (and (rationalp request) (< 0 request) (<= request error)
        (<= (* (+ (* 2 cost) 4) request) error))))
 :hints (("Goal"
  :use ((:instance lw-cnp-division-small (divisor (+ 5 (* 2 cost))) (value error))
        (:instance lw-positive-division-bound
         (numerator (* (+ (* 2 cost) 4) error)) (divisor (+ 5 (* 2 cost))) (bound error)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-dirichlet-native-refinement-valid
 (implies (and (rationalp rate) (<= 0 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-native-refinement rate height count error)))
   (and (rationalp request) (< 0 request) (<= request error)
        (<= (* (+ (* 2 (lw-common-dirichlet-transport-cost rate height count)) 4) request) error))))
 :hints (("Goal"
  :use (lw-common-dirichlet-transport-cost-valid
        (:instance lw-cnp-refinement-algebra (cost (lw-common-dirichlet-transport-cost rate height count))))
  :in-theory (disable lw-common-dirichlet-transport-cost-valid)
  :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-native-refinement)))

(defthm lw-complex-common-prefix-series-computed-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error) (<= (lw-dirichlet-series-count error) count)
               (rationalp target-error) (< 0 target-error) (rationalp request) (< 0 request)
               (<= request (lw-dirichlet-native-refinement rate height count target-error)))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
    (lw-complex-common-native-series mangoldtp logp rate height error))
   (+ (* 3/8 error) target-error)))
 :hints (("Goal"
  :use
  ((:instance lw-dirichlet-native-refinement-valid (error target-error))
   lw-common-dirichlet-transport-cost-valid
   (:instance lw-complex-common-prefix-series-comparison
    (finite-error (lw-dirichlet-native-refinement rate height count target-error)))
   (:instance lw-cnp-multiply-order
    (a request) (b (lw-dirichlet-native-refinement rate height count target-error))
    (factor (lw-common-dirichlet-transport-cost rate height count)))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub
     (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
     (lw-complex-common-native-series mangoldtp logp rate height error)))
    (radius (+ (* (lw-common-dirichlet-transport-cost rate height count)
                  (+ request (lw-dirichlet-native-refinement rate height count target-error)))
               (* 3/8 error) (* 4 (lw-dirichlet-native-refinement rate height count target-error))))
    (cap (+ (* 3/8 error) target-error))))
  :in-theory (disable lw-dirichlet-native-refinement-valid lw-common-dirichlet-transport-cost-valid
                      lw-complex-common-prefix-series-comparison lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t)))



