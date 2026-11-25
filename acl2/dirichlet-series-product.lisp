(in-package "ACL2")

(include-book "dirichlet-common-precision")
(include-book "complex-exp-multiply")
(include-book "complex-disk-gap")

; Product identity for the actual native Cauchy series. Every auxiliary
; cutoff and precision is computed; the last slack is removed by the
; existing rational complex-disk gap lemma.

(local (in-theory (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul
 lw-complex-scale lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
 lw-complex-scale-product lw-complex-sub-add lw-complex-sub-add-first
 lw-complex-sub-add-cancel lw-complex-common-dirichlet-prefix
 lw-complex-common-native-partial lw-complex-common-native-finite
 lw-complex-common-native-finite-as-partial lw-complex-common-native-series
 lw-complex-dirichlet-series-value lw-complex-zeta-series-value
 lw-dirichlet-series-count lw-dirichlet-rectangle-count lw-dirichlet-native-refinement
 lw-dirichlet-rectangle-budget lw-dirichlet-convolution-precision
 lw-dirichlet-tail-rounding-cost lw-common-dirichlet-transport-cost
 lw-complex-mangoldt-canonical-prefix lw-complex-ordinary-canonical-prefix
 lw-complex-log-dirichlet-sum lw-disk-gap-error)))

(local (defthm lw-nsp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nsp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nsp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nsp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nsp-times-negative (a b) (b a)))
                 :in-theory (disable lw-nsp-times-negative)))))

(local (defthm lw-nsp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nsp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nsp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nsp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nsp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nsp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nsp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nsp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nsp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nsp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nsp-left-commutes)))))

(local (defthm lw-nsp-nonnegative-product
 (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nsp-difference-add
 (implies (and (lw-complexp x) (lw-complexp y))
  (equal (lw-complex-add (lw-complex-sub x y) y) x))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(local (defthm lw-nsp-nearby-cap
 (implies (and (lw-complexp x) (lw-complexp y)
               (lw-complex-diskp (lw-complex-sub x y) radius) (lw-complex-diskp y cap))
  (lw-complex-diskp x (+ cap radius)))
 :hints (("Goal"
  :use ((:instance lw-complex-add-disk (left (lw-complex-sub x y)) (right y)
         (other-radius cap)))
  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-common-native-series-cauchy
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-common-native-series mangoldtp logp rate height left-error)
                   (lw-complex-common-native-series mangoldtp logp rate height right-error))
   (+ left-error right-error)))
 :hints (("Goal"
  :use (lw-complex-dirichlet-series-value-cauchy lw-complex-zeta-series-value-cauchy)
  :in-theory (e/d (lw-complex-common-native-series)
   (lw-complex-dirichlet-series-value-cauchy lw-complex-zeta-series-value-cauchy)))))

(defthm lw-complex-common-native-series-reference-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-common-native-series mangoldtp logp rate height error)
   (+ 2 (lw-complex-l1 (lw-complex-common-native-series mangoldtp logp rate height 1)))))
 :hints (("Goal"
  :use
  ((:instance lw-complex-common-native-series-cauchy (left-error error) (right-error 1))
   (:instance lw-complex-l1-bound (point (lw-complex-common-native-series mangoldtp logp rate height 1)))
   (:instance lw-nsp-nearby-cap
    (x (lw-complex-common-native-series mangoldtp logp rate height error))
    (y (lw-complex-common-native-series mangoldtp logp rate height 1))
    (radius (+ error 1))
    (cap (lw-complex-l1 (lw-complex-common-native-series mangoldtp logp rate height 1))))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-common-native-series mangoldtp logp rate height error))
    (radius (+ (lw-complex-l1 (lw-complex-common-native-series mangoldtp logp rate height 1)) error 1))
    (cap (+ (lw-complex-l1 (lw-complex-common-native-series mangoldtp logp rate height 1)) 2))))
  :in-theory (disable lw-complex-common-native-series-cauchy lw-complex-l1-bound lw-complex-disk-enlarge)
  :do-not-induct t)))

(defun lw-dirichlet-series-product-left-cap (rate height)
 (+ 4 (lw-complex-l1 (lw-complex-common-native-series t nil rate height 1))))

(defun lw-dirichlet-series-product-right-cap (rate height)
 (+ 2 (lw-complex-l1 (lw-complex-common-native-series nil nil rate height 1))))

(defthm lw-dirichlet-series-product-caps-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height))
  (and (rationalp (lw-dirichlet-series-product-left-cap rate height))
       (<= 4 (lw-dirichlet-series-product-left-cap rate height))
       (rationalp (lw-dirichlet-series-product-right-cap rate height))
       (<= 2 (lw-dirichlet-series-product-right-cap rate height))))
 :hints (("Goal"
  :use ((:instance lw-complex-l1-bound (point (lw-complex-common-native-series t nil rate height 1)))
        (:instance lw-complex-l1-bound (point (lw-complex-common-native-series nil nil rate height 1))))
  :in-theory (disable lw-complex-l1-bound))))

(defthm lw-dirichlet-series-product-left-series-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-common-native-series t nil rate height error)
                    (- (lw-dirichlet-series-product-left-cap rate height) 2)))
 :hints (("Goal"
  :use ((:instance lw-complex-common-native-series-reference-cap (mangoldtp t) (logp nil)))
  :in-theory (disable lw-complex-common-native-series-reference-cap))))

(defthm lw-dirichlet-series-product-right-series-cap
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-common-native-series nil nil rate height error)
                    (lw-dirichlet-series-product-right-cap rate height)))
 :hints (("Goal"
  :use ((:instance lw-complex-common-native-series-reference-cap (mangoldtp nil) (logp nil)))
  :in-theory (disable lw-complex-common-native-series-reference-cap))))

(local (in-theory (disable lw-dirichlet-series-product-left-cap lw-dirichlet-series-product-right-cap)))

(defun lw-dirichlet-series-product-count (mangoldt-error ordinary-error log-error error)
 (max (lw-dirichlet-rectangle-count error)
      (max (lw-dirichlet-series-count mangoldt-error)
           (max (lw-dirichlet-series-count ordinary-error) (lw-dirichlet-series-count log-error)))))

(defthm lw-dirichlet-series-product-count-valid
 (implies (and (rationalp mangoldt-error) (< 0 mangoldt-error)
               (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp log-error) (< 0 log-error) (rationalp error) (< 0 error))
  (let ((count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error)))
   (and (posp count) (<= (lw-dirichlet-rectangle-count error) count)
        (<= (lw-dirichlet-series-count mangoldt-error) count)
        (<= (lw-dirichlet-series-count ordinary-error) count)
        (<= (lw-dirichlet-series-count log-error) count))))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-series-count-valid (error mangoldt-error))
        (:instance lw-dirichlet-series-count-valid (error ordinary-error))
        (:instance lw-dirichlet-series-count-valid (error log-error))
        lw-dirichlet-rectangle-count-valid)
  :in-theory (disable lw-dirichlet-series-count-valid lw-dirichlet-rectangle-count-valid)
  :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-series-product-count)))

(defun lw-dirichlet-series-product-budget (rate height count error)
 (lw-dirichlet-rectangle-budget rate height count (lw-dirichlet-native-refinement rate height count error)))

(defun lw-dirichlet-series-product-request (rate height count error)
 (lw-dirichlet-convolution-precision rate height count
                                    (lw-dirichlet-series-product-budget rate height count error)))

(defthm lw-dirichlet-series-product-request-valid
 (implies (and (rationalp rate) (< 3 rate) (rationalp height) (natp count)
               (rationalp error) (< 0 error))
  (let ((request (lw-dirichlet-series-product-request rate height count error))
        (budget (lw-dirichlet-series-product-budget rate height count error)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (rationalp budget) (< 0 budget)
        (<= request (lw-dirichlet-native-refinement rate height count error))
        (<= (+ budget (* (lw-dirichlet-tail-rounding-cost rate height count count count) request))
            (* 1/2 error)))))
 :hints (("Goal"
  :use
  (lw-dirichlet-native-refinement-valid
   (:instance lw-dirichlet-tail-rounding-cost-valid (left count) (bound count) (cutoff count))
   (:instance lw-dirichlet-rectangle-budget-valid
    (error (lw-dirichlet-native-refinement rate height count error)))
   (:instance lw-dirichlet-convolution-precision-small
    (error (lw-dirichlet-series-product-budget rate height count error)))
   (:instance lw-nsp-nonnegative-product
    (a (lw-dirichlet-tail-rounding-cost rate height count count count))
    (b (lw-dirichlet-series-product-request rate height count error))))
  :in-theory (disable lw-dirichlet-native-refinement-valid lw-dirichlet-tail-rounding-cost-valid
                      lw-dirichlet-rectangle-budget-valid lw-dirichlet-convolution-precision-small)
  :nonlinearp nil :do-not-induct t)))

(local (in-theory (disable lw-dirichlet-series-product-budget lw-dirichlet-series-product-request)))

(defun lw-dirichlet-series-mode-error (mangoldtp logp mangoldt-error ordinary-error log-error)
 (if mangoldtp mangoldt-error (if logp log-error ordinary-error)))

(defun lw-complex-dirichlet-series-product-error (rate height mangoldt-error ordinary-error log-error)
 (lw-complex-sub
  (lw-complex-mul (lw-complex-common-native-series t nil rate height mangoldt-error)
                  (lw-complex-common-native-series nil nil rate height ordinary-error))
  (lw-complex-common-native-series nil t rate height log-error)))

(defun lw-dirichlet-series-product-radius (rate height mangoldt-error ordinary-error log-error)
 (+ (* (lw-dirichlet-series-product-right-cap rate height) mangoldt-error)
    (* (lw-dirichlet-series-product-left-cap rate height) ordinary-error)
    log-error))

(defthm lw-complex-dirichlet-series-product-error-rational
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error)
               (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp log-error) (< 0 log-error))
  (lw-complexp (lw-complex-dirichlet-series-product-error
               rate height mangoldt-error ordinary-error log-error))))

(defthm lw-dirichlet-series-product-radius-data
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error)
               (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp log-error) (< 0 log-error))
  (and (rationalp (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error))
       (<= 0 (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error))))
 :hints (("Goal" :use (lw-dirichlet-series-product-caps-valid)
                 :in-theory (disable lw-dirichlet-series-product-caps-valid)
                 :nonlinearp t :do-not-induct t)))

(defthm lw-dirichlet-series-product-prefix-comparison
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error)
               (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp log-error) (< 0 log-error) (rationalp target-error) (< 0 target-error))
  (let* ((count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
         (request (lw-dirichlet-series-product-request rate height count target-error))
         (series-error (lw-dirichlet-series-mode-error mangoldtp logp mangoldt-error ordinary-error log-error)))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-common-dirichlet-prefix mangoldtp logp rate height count request)
     (lw-complex-common-native-series mangoldtp logp rate height series-error))
    (+ (* 3/8 series-error) target-error))))
 :hints (("Goal"
  :use
  ((:instance lw-dirichlet-series-product-count-valid (error target-error))
   (:instance lw-dirichlet-series-product-request-valid
    (count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
    (error target-error))
   (:instance lw-complex-common-prefix-series-computed-comparison
    (count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
    (request (lw-dirichlet-series-product-request rate height
              (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error))
    (error (lw-dirichlet-series-mode-error mangoldtp logp mangoldt-error ordinary-error log-error))))
  :in-theory (disable lw-dirichlet-series-product-count-valid lw-dirichlet-series-product-request-valid
                      lw-complex-common-prefix-series-computed-comparison)
  :do-not-induct t)))

(defthm lw-dirichlet-series-product-prefix-convolution
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error)
               (rationalp ordinary-error) (< 0 ordinary-error)
               (rationalp log-error) (< 0 log-error) (rationalp target-error) (< 0 target-error))
  (let* ((count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
         (request (lw-dirichlet-series-product-request rate height count target-error)))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-mul (lw-complex-common-dirichlet-prefix t nil rate height count request)
                     (lw-complex-common-dirichlet-prefix nil nil rate height count request))
     (lw-complex-common-dirichlet-prefix nil t rate height count request))
    target-error)))
 :hints (("Goal"
  :use
  ((:instance lw-dirichlet-series-product-count-valid (error target-error))
   (:instance lw-dirichlet-rectangle-count-valid (error target-error))
   (:instance lw-dirichlet-series-product-request-valid
    (count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
    (error target-error))
   (:instance lw-complex-dirichlet-rectangle-convolution-error
    (count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
    (start (lw-dirichlet-series-count (* 1/4 target-error)))
    (error (lw-dirichlet-series-product-budget rate height
            (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error)))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub
     (lw-complex-mul
      (lw-complex-common-dirichlet-prefix t nil rate height
       (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error)
       (lw-dirichlet-series-product-request rate height
        (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error))
      (lw-complex-common-dirichlet-prefix nil nil rate height
       (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error)
       (lw-dirichlet-series-product-request rate height
        (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error)))
     (lw-complex-common-dirichlet-prefix nil t rate height
      (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error)
      (lw-dirichlet-series-product-request rate height
       (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error))))
    (radius (+ (* 16 (/ (lw-dirichlet-series-count (* 1/4 target-error))))
     (* (lw-dirichlet-tail-rounding-cost rate height
          (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error)
          (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error)
          (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error))
        (lw-dirichlet-series-product-request rate height
         (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error))
     (lw-dirichlet-series-product-budget rate height
      (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error target-error) target-error)))
    (cap target-error)))
  :in-theory (e/d (lw-dirichlet-series-product-request)
   (lw-dirichlet-series-product-count-valid lw-dirichlet-rectangle-count-valid
    lw-dirichlet-series-product-request-valid lw-complex-dirichlet-rectangle-convolution-error
    lw-complex-disk-enlarge))
  :do-not-induct t)))

(local (defthm lw-nsp-loose-cap
 (implies (and (lw-complexp a) (lw-complexp x) (rationalp cap) (<= 2 cap)
               (rationalp radius) (<= 0 radius) (<= radius 2)
               (lw-complex-diskp x (- cap 2))
               (lw-complex-diskp (lw-complex-sub a x) radius))
  (lw-complex-diskp a cap))
 :hints (("Goal"
  :use ((:instance lw-nsp-nearby-cap (x a) (y x) (cap (- cap 2)))
        (:instance lw-complex-disk-enlarge (point a) (radius (+ (- cap 2) radius))))
  :in-theory (disable lw-complex-disk-enlarge)
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-nsp-product-composition
 (implies
  (and (lw-complexp x) (lw-complexp y) (lw-complexp z)
       (lw-complexp a) (lw-complexp b) (lw-complexp c)
       (rationalp left-cap) (<= 0 left-cap) (rationalp right-cap) (<= 0 right-cap)
       (rationalp mangoldt-error) (< 0 mangoldt-error)
       (rationalp ordinary-error) (< 0 ordinary-error)
       (rationalp log-error) (< 0 log-error) (rationalp error) (< 0 error)
       (lw-complex-diskp a left-cap) (lw-complex-diskp y right-cap)
       (lw-complex-diskp (lw-complex-sub a x) (+ (* 3/8 mangoldt-error) error))
       (lw-complex-diskp (lw-complex-sub b y) (+ (* 3/8 ordinary-error) error))
       (lw-complex-diskp (lw-complex-sub c z) (+ (* 3/8 log-error) error))
       (lw-complex-diskp (lw-complex-sub (lw-complex-mul a b) c) error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-mul x y) z)
   (+ (* right-cap mangoldt-error) (* left-cap ordinary-error) log-error
      (* (+ right-cap left-cap 2) error))))
 :hints (("Goal"
  :use
  ((:instance lw-complex-difference-symmetric (left a) (right x) (radius (+ (* 3/8 mangoldt-error) error)))
   (:instance lw-complex-difference-symmetric (left b) (right y) (radius (+ (* 3/8 ordinary-error) error)))
   (:instance lw-complex-mul-difference-bound
    (a x) (b y) (c a) (d b)
    (left-error (+ (* 3/8 mangoldt-error) error)) (right-error (+ (* 3/8 ordinary-error) error)))
   (:instance lw-complex-difference-triangle
    (left (lw-complex-mul x y)) (middle (lw-complex-mul a b)) (right c)
    (radius (+ (* right-cap (+ (* 3/8 mangoldt-error) error))
               (* left-cap (+ (* 3/8 ordinary-error) error)))) (other-radius error))
   (:instance lw-complex-difference-triangle
    (left (lw-complex-mul x y)) (middle c) (right z)
    (radius (+ (* right-cap (+ (* 3/8 mangoldt-error) error))
               (* left-cap (+ (* 3/8 ordinary-error) error)) error))
    (other-radius (+ (* 3/8 log-error) error)))
   (:instance lw-nsp-multiply-order (a (* 3/8 mangoldt-error)) (b mangoldt-error) (factor right-cap))
   (:instance lw-nsp-multiply-order (a (* 3/8 ordinary-error)) (b ordinary-error) (factor left-cap))
   (:instance lw-complex-disk-enlarge
    (point (lw-complex-sub (lw-complex-mul x y) z))
    (radius (+ (* right-cap (+ (* 3/8 mangoldt-error) error))
               (* left-cap (+ (* 3/8 ordinary-error) error)) error (* 3/8 log-error) error))
    (cap (+ (* right-cap mangoldt-error) (* left-cap ordinary-error) log-error
            (* (+ right-cap left-cap 2) error)))))
  :in-theory (disable lw-complex-mul-difference-bound
                      lw-complex-difference-triangle lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-dirichlet-series-product-slack
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error) (<= mangoldt-error 1)
               (rationalp ordinary-error) (< 0 ordinary-error) (<= ordinary-error 1)
               (rationalp log-error) (< 0 log-error) (<= log-error 1)
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-dirichlet-series-product-error rate height mangoldt-error ordinary-error log-error) (+ (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error) (* (+ (lw-dirichlet-series-product-left-cap rate height) (lw-dirichlet-series-product-right-cap rate height) 2) error))))
 :hints (("Goal"
  :use
  (lw-dirichlet-series-product-count-valid
   (:instance lw-dirichlet-series-product-request-valid (count (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error)))
   lw-dirichlet-series-product-caps-valid
   (:instance lw-dirichlet-series-product-left-series-cap (error mangoldt-error))
   (:instance lw-dirichlet-series-product-right-series-cap (error ordinary-error))
   (:instance lw-dirichlet-series-product-prefix-comparison (mangoldtp t) (logp nil) (target-error error))
   (:instance lw-dirichlet-series-product-prefix-comparison (mangoldtp nil) (logp nil) (target-error error))
   (:instance lw-dirichlet-series-product-prefix-comparison (mangoldtp nil) (logp t) (target-error error))
   (:instance lw-dirichlet-series-product-prefix-convolution (target-error error))
   (:instance lw-nsp-loose-cap
    (a (lw-complex-common-dirichlet-prefix t nil rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) (lw-dirichlet-series-product-request rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) error))) (x (lw-complex-common-native-series t nil rate height mangoldt-error))
    (cap (lw-dirichlet-series-product-left-cap rate height)) (radius (+ (* 3/8 mangoldt-error) error)))
   (:instance lw-nsp-product-composition
    (x (lw-complex-common-native-series t nil rate height mangoldt-error))
    (y (lw-complex-common-native-series nil nil rate height ordinary-error))
    (z (lw-complex-common-native-series nil t rate height log-error))
    (a (lw-complex-common-dirichlet-prefix t nil rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) (lw-dirichlet-series-product-request rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) error))) (b (lw-complex-common-dirichlet-prefix nil nil rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) (lw-dirichlet-series-product-request rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) error))) (c (lw-complex-common-dirichlet-prefix nil t rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) (lw-dirichlet-series-product-request rate height (lw-dirichlet-series-product-count mangoldt-error ordinary-error log-error error) error)))
    (left-cap (lw-dirichlet-series-product-left-cap rate height)) (right-cap (lw-dirichlet-series-product-right-cap rate height))))
  :in-theory (e/d (lw-complex-dirichlet-series-product-error lw-dirichlet-series-product-radius)
   (lw-dirichlet-series-product-count-valid lw-dirichlet-series-product-request-valid
    lw-dirichlet-series-product-caps-valid lw-dirichlet-series-product-left-series-cap
    lw-dirichlet-series-product-right-series-cap lw-dirichlet-series-product-prefix-comparison
    lw-dirichlet-series-product-prefix-convolution))
  :nonlinearp nil :do-not-induct t)))

(defun lw-disk-gap-refinement (point radius cost)
 (min 1 (/ (lw-disk-gap-error (lw-complex-norm-square point) radius) (+ 1 cost))))

(local (defthm lw-nsp-gap-request-data
 (implies (and (rationalp cost) (<= 0 cost) (rationalp value) (< 0 value))
  (let ((request (min 1 (/ value (+ 1 cost)))))
   (and (rationalp request) (< 0 request) (<= request 1) (<= (* cost request) value))))
 :hints (("Goal"
  :use ((:instance lw-positive-division-bound (numerator (* cost value)) (divisor (+ 1 cost)) (bound value))
        (:instance lw-nsp-multiply-order
         (a (min 1 (/ value (+ 1 cost)))) (b (/ value (+ 1 cost))) (factor cost)))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-disk-gap-refinement-excludes
 (implies (and (lw-complexp point) (rationalp radius) (<= 0 radius)
               (not (lw-complex-diskp point radius)) (rationalp cost) (<= 0 cost))
  (let ((request (lw-disk-gap-refinement point radius cost)))
   (and (rationalp request) (< 0 request) (<= request 1)
        (not (lw-complex-diskp point (+ radius (* cost request)))))))
 :hints (("Goal"
  :use (lw-complex-disk-gap-excludes
        (:instance lw-nsp-gap-request-data
         (value (lw-disk-gap-error (lw-complex-norm-square point) radius)))
        (:instance lw-complex-disk-enlarge
         (radius (+ radius (* cost (lw-disk-gap-refinement point radius cost))))
         (cap (+ radius (lw-disk-gap-error (lw-complex-norm-square point) radius)))))
  :in-theory (disable lw-complex-disk-gap-excludes lw-complex-disk-enlarge)
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil)

(local (in-theory (disable lw-disk-gap-refinement lw-complex-dirichlet-series-product-error
                          lw-dirichlet-series-product-radius)))

(defthm lw-complex-common-dirichlet-series-product
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error) (<= mangoldt-error 1)
               (rationalp ordinary-error) (< 0 ordinary-error) (<= ordinary-error 1)
               (rationalp log-error) (< 0 log-error) (<= log-error 1))
  (lw-complex-diskp (lw-complex-dirichlet-series-product-error rate height mangoldt-error ordinary-error log-error) (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error)))
 :hints (("Goal"
  :cases ((lw-complex-diskp (lw-complex-dirichlet-series-product-error rate height mangoldt-error ordinary-error log-error) (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error)))
  :use
  (lw-dirichlet-series-product-caps-valid
   lw-dirichlet-series-product-radius-data
   lw-complex-dirichlet-series-product-error-rational
   (:instance lw-complex-disk-gap-refinement-excludes
    (point (lw-complex-dirichlet-series-product-error rate height mangoldt-error ordinary-error log-error)) (radius (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error)) (cost (+ (lw-dirichlet-series-product-left-cap rate height) (lw-dirichlet-series-product-right-cap rate height) 2)))
   (:instance lw-complex-dirichlet-series-product-slack
    (error (lw-disk-gap-refinement (lw-complex-dirichlet-series-product-error rate height mangoldt-error ordinary-error log-error) (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error) (+ (lw-dirichlet-series-product-left-cap rate height) (lw-dirichlet-series-product-right-cap rate height) 2)))))
  :in-theory (disable lw-dirichlet-series-product-caps-valid lw-dirichlet-series-product-radius-data
                      lw-complex-dirichlet-series-product-error-rational lw-complex-dirichlet-series-product-slack)
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-dirichlet-series-product
 (implies (and (rationalp rate) (< 3 rate) (rationalp height)
               (rationalp mangoldt-error) (< 0 mangoldt-error) (<= mangoldt-error 1)
               (rationalp ordinary-error) (< 0 ordinary-error) (<= ordinary-error 1)
               (rationalp log-error) (< 0 log-error) (<= log-error 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-mul (lw-complex-dirichlet-series-value rate height mangoldt-error)
                    (lw-complex-zeta-series-value nil rate height ordinary-error))
    (lw-complex-zeta-series-value t rate height log-error))
   (lw-dirichlet-series-product-radius rate height mangoldt-error ordinary-error log-error)))
 :hints (("Goal"
  :use (lw-complex-common-dirichlet-series-product)
  :in-theory (e/d (lw-complex-dirichlet-series-product-error lw-complex-common-native-series)
                  (lw-complex-common-dirichlet-series-product))
  :do-not-induct t)))



