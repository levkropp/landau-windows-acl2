(in-package "ACL2")

(include-book "rpow-bounds")

(local (defthm lw-rpc-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rpc-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity
                                (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rpc-zero-product (equal (* 0 value) 0)))

(local (defthm lw-rpc-multiply-inequality
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-rpc-positive-product
         (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right))
                  (< 0 (* left right)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(local (defthm lw-rpc-cancel-positive-product
         (implies (and (rationalp left) (rationalp right) (rationalp factor) (< 0 factor)
                       (<= (* left factor) (* right factor)))
                  (<= left right))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

(defthm lw-rational-power-positive
  (implies (and (rationalp base) (< 0 base)) (< 0 (lw-rational-power base exponent)))
  :hints (("Goal" :induct (lw-rational-power base exponent) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-rpc-positive-product
                          (left base) (right (lw-rational-power base (- exponent 1)))))
                 :in-theory (disable lw-rational-power) :nonlinearp t))))

(defthm lw-rational-power-strict-base
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (< left right) (posp exponent))
           (< (lw-rational-power left exponent) (lw-rational-power right exponent)))
  :hints (("Goal" :induct (lw-rational-power left exponent) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-rational-power-monotone-base (exponent (- exponent 1)))
                        (:instance lw-rational-power-positive (base right) (exponent (- exponent 1))))
                 :in-theory (disable lw-rational-power lw-rational-power-monotone-base
                                     lw-rational-power-positive)
                 :nonlinearp t)))
  :rule-classes nil)

(defthm lw-rational-power-reflects-order
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= 0 right) (posp exponent)
                (<= (lw-rational-power left exponent) (lw-rational-power right exponent)))
           (<= left right))
  :hints (("Goal" :cases ((<= left right))
                  :use ((:instance lw-rational-power-strict-base (left right) (right left)))
                  :in-theory (disable lw-rational-power)))
  :rule-classes nil)

(defthm lw-rational-power-product
  (implies (and (rationalp left) (rationalp right) (natp exponent))
           (equal (lw-rational-power (* left right) exponent)
                  (* (lw-rational-power left exponent) (lw-rational-power right exponent))))
  :hints (("Goal" :induct (lw-rational-power left exponent))))

(defthm lw-rational-power-add-exponents
  (implies (and (rationalp base) (natp left) (natp right))
           (equal (lw-rational-power base (+ left right))
                  (* (lw-rational-power base left) (lw-rational-power base right))))
  :hints (("Goal" :induct (lw-rational-power base left))))

(defthm lw-mixed-power-order
  (implies (and (rationalp large) (rationalp small) (<= 1 small) (<= small large)
                (natp numerator) (natp denominator) (<= numerator denominator))
           (<= (* (lw-rational-power large numerator) (lw-rational-power small denominator))
               (* (lw-rational-power large denominator) (lw-rational-power small numerator))))
  :hints (("Goal" :use ((:instance lw-rational-power-add-exponents
                          (base large) (left numerator) (right (- denominator numerator)))
                        (:instance lw-rational-power-add-exponents
                          (base small) (left numerator) (right (- denominator numerator)))
                        (:instance lw-rational-power-monotone-base
                          (left small) (right large) (exponent (- denominator numerator)))
                        (:instance lw-rational-power-at-least-one (base large) (exponent numerator))
                        (:instance lw-rational-power-at-least-one (base small) (exponent numerator))
                        (:instance lw-rpc-multiply-inequality
                          (left (lw-rational-power small (- denominator numerator)))
                          (right (lw-rational-power large (- denominator numerator)))
                          (factor (* (lw-rational-power large numerator)
                                     (lw-rational-power small numerator)))))
                  :in-theory (disable lw-rational-power lw-rational-power-add-exponents
                                      lw-rational-power-monotone-base lw-rational-power-at-least-one)
                  :nonlinearp t)))

(local
 (defthm lw-rpc-cross-product-transport
   (implies (and (rationalp large) (rationalp small) (< 0 small) (<= small large)
                 (rationalp left) (rationalp right) (<= right small)
                 (<= (* left small) (* large right)))
            (<= (- left right) (- large small)))
   :hints (("Goal" :use ((:instance lw-rpc-multiply-inequality
                          (left right) (right small) (factor (- large small)))
                        (:instance lw-rpc-cancel-positive-product
                          (left (- left right)) (right (- large small)) (factor small)))
                   :nonlinearp t))
   :rule-classes nil))

; Lower root at x versus upper root at y. The proof uses only polynomial
; brackets and integer powers: no real rpow derivative is assumed.
(defthm lw-rpow-bracket-transport
  (implies (and (rationalp large) (rationalp small) (<= 1 small) (<= small large)
                (rationalp lower-root) (<= 1 lower-root)
                (rationalp upper-root) (<= 1 upper-root) (<= upper-root small)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (<= (lw-rational-power lower-root denominator) (lw-rational-power large numerator))
                (<= (lw-rational-power small numerator) (lw-rational-power upper-root denominator)))
           (<= (- lower-root upper-root) (- large small)))
  :hints (("Goal" :use (lw-mixed-power-order
                        (:instance lw-rpc-multiply-inequality
                          (left (lw-rational-power lower-root denominator))
                          (right (lw-rational-power large numerator))
                          (factor (lw-rational-power small denominator)))
                        (:instance lw-rpc-multiply-inequality
                          (left (lw-rational-power small numerator))
                          (right (lw-rational-power upper-root denominator))
                          (factor (lw-rational-power large denominator)))
                        (:instance lw-rational-power-reflects-order
                          (left (* lower-root small)) (right (* large upper-root)) (exponent denominator))
                        (:instance lw-rpc-cross-product-transport (left lower-root) (right upper-root)))
                  :in-theory (disable lw-rational-power lw-mixed-power-order)
                  :nonlinearp t)))

(defthm lw-rpow-bounds-growth-transport
  (implies (and (rationalp large) (rationalp small) (<= 1 small) (<= small large)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp large-error) (< 0 large-error)
                (rationalp small-error) (< 0 small-error))
           (<= (- (car (lw-rpow-bounds large numerator denominator large-error))
                  (cdr (lw-rpow-bounds small numerator denominator small-error)))
               (- large small)))
  :hints (("Goal" :use ((:instance lw-rpow-bounds-sound (value large) (epsilon large-error))
                        (:instance lw-rpow-bounds-sound (value small) (epsilon small-error))
                        (:instance lw-rpow-bracket-transport
                          (lower-root (car (lw-rpow-bounds large numerator denominator large-error)))
                          (upper-root (cdr (lw-rpow-bounds small numerator denominator small-error)))))
                  :in-theory (disable lw-rpow-bounds lw-rpow-bounds-sound lw-rpow-bracket-transport
                                      lw-rational-power))))

(defthm lw-rpow-bounds-monotone-overlap
  (implies (and (rationalp small) (rationalp large) (<= 1 small) (<= small large)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp small-error) (< 0 small-error)
                (rationalp large-error) (< 0 large-error))
           (<= (car (lw-rpow-bounds small numerator denominator small-error))
               (cdr (lw-rpow-bounds large numerator denominator large-error))))
  :hints (("Goal" :use ((:instance lw-rpow-bounds-sound (value large) (epsilon large-error))
                        (:instance lw-rpow-bounds-sound (value small) (epsilon small-error))
                        (:instance lw-rational-power-monotone-base (left small) (right large) (exponent numerator))
                        (:instance lw-rational-power-reflects-order
                          (left (car (lw-rpow-bounds small numerator denominator small-error)))
                          (right (cdr (lw-rpow-bounds large numerator denominator large-error))) (exponent denominator)))
                  :in-theory (disable lw-rpow-bounds lw-rpow-bounds-sound lw-rational-power
                                      lw-rational-power-monotone-base lw-rational-power-positive
                                      lw-rational-power-product
                                      lw-rational-power-add-exponents lw-mixed-power-order
                                      lw-rpow-bracket-transport lw-rpow-bounds-growth-transport))))

(defthm lw-rpow-bounds-lipschitz-budget
  (implies (and (rationalp small) (rationalp large) (<= 1 small) (<= small large)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp small-error) (< 0 small-error)
                (rationalp large-error) (< 0 large-error))
           (<= (- (cdr (lw-rpow-bounds large numerator denominator large-error))
                  (car (lw-rpow-bounds small numerator denominator small-error)))
               (+ (- large small) small-error large-error)))
  :hints (("Goal" :use (lw-rpow-bounds-growth-transport
                        (:instance lw-rpow-bounds-width (value large) (epsilon large-error))
                        (:instance lw-rpow-bounds-width (value small) (epsilon small-error))
                        (:instance lw-rpow-bounds-sound (value large) (epsilon large-error))
                        (:instance lw-rpow-bounds-sound (value small) (epsilon small-error)))
                  :in-theory (disable lw-rpow-bounds lw-rpow-bounds-width lw-rpow-bounds-sound
                                      lw-rpow-bounds-growth-transport lw-rational-power))))

(defthm lw-rpow-bounds-cross-budget
  (implies (and (rationalp left) (rationalp right) (<= 1 left) (<= 1 right)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (cdr (lw-rpow-bounds right numerator denominator right-error))
                  (car (lw-rpow-bounds left numerator denominator left-error)))
               (+ (abs (- right left)) left-error right-error)))
  :hints (("Goal" :cases ((<= left right))
                  :use ((:instance lw-rpow-bounds-lipschitz-budget
                          (small left) (large right) (small-error left-error) (large-error right-error))
                        (:instance lw-rpow-bounds-monotone-overlap
                          (small right) (large left) (small-error right-error) (large-error left-error))
                        (:instance lw-rpow-bounds-width (value left) (epsilon left-error))
                        (:instance lw-rpow-bounds-width (value right) (epsilon right-error))
                        (:instance lw-rpow-bounds-sound (value left) (epsilon left-error))
                        (:instance lw-rpow-bounds-sound (value right) (epsilon right-error)))
                  :in-theory (disable lw-rpow-bounds lw-rpow-bounds-width lw-rpow-bounds-sound
                                      lw-rpow-bounds-lipschitz-budget lw-rpow-bounds-monotone-overlap
                                      lw-rational-power))))

(defthm lw-rpow-enclosed-values-lipschitz
  (implies (and (rationalp left) (rationalp right) (<= 1 left) (<= 1 right)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error)
                (lw-contains (lw-rpow-bounds left numerator denominator left-error) left-value)
                (lw-contains (lw-rpow-bounds right numerator denominator right-error) right-value))
           (<= (abs (- right-value left-value))
               (+ (abs (- right left)) left-error right-error)))
  :hints (("Goal" :use (lw-rpow-bounds-cross-budget
                        (:instance lw-rpow-bounds-cross-budget
                          (left right) (right left) (left-error right-error) (right-error left-error)))
                  :in-theory (disable lw-rpow-bounds lw-rpow-bounds-cross-budget))))

(defthm lw-rpow-lower-cauchy
  (implies (and (rationalp value) (<= 1 value)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (abs (- (car (lw-rpow-bounds value numerator denominator left-error))
                       (car (lw-rpow-bounds value numerator denominator right-error))))
               (+ left-error right-error)))
  :hints (("Goal" :use ((:instance lw-rpow-enclosed-values-lipschitz
                          (left value) (right value)
                          (left-value (car (lw-rpow-bounds value numerator denominator right-error)))
                          (right-value (car (lw-rpow-bounds value numerator denominator left-error)))
                          (left-error right-error) (right-error left-error))
                        (:instance lw-rpow-bounds-sound (epsilon left-error))
                        (:instance lw-rpow-bounds-sound (epsilon right-error)))
                  :in-theory (disable lw-rpow-bounds lw-rpow-enclosed-values-lipschitz
                                      lw-rpow-bounds-sound lw-rational-power))))

(defthm lw-rpow-bounds-one-sided-transport
  (implies (and (rationalp left) (rationalp right) (<= 1 left) (<= 1 right)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp left-error) (< 0 left-error)
                (rationalp right-error) (< 0 right-error))
           (<= (- (car (lw-rpow-bounds right numerator denominator right-error))
                  (cdr (lw-rpow-bounds left numerator denominator left-error)))
               (abs (- right left))))
  :hints (("Goal" :cases ((<= left right))
                  :use ((:instance lw-rpow-bounds-growth-transport
                          (small left) (large right) (small-error left-error) (large-error right-error))
                        (:instance lw-rpow-bounds-monotone-overlap
                          (small right) (large left) (small-error right-error) (large-error left-error))
                        (:instance lw-rpow-bounds-sound (value left) (epsilon left-error))
                        (:instance lw-rpow-bounds-sound (value right) (epsilon right-error)))
                  :in-theory (disable lw-rpow-bounds lw-rpow-bounds-growth-transport
                                      lw-rpow-bounds-monotone-overlap lw-rpow-bounds-sound
                                      lw-rational-power))))

(assert-event (<= (- (cdr (lw-rpow-bounds 3 1 2 1/100))
                     (car (lw-rpow-bounds 2 1 2 1/20)))
                  (+ 1 1/100 1/20)))
(assert-event (<= (abs (- (car (lw-rpow-bounds 2 2 3 1/100))
                          (car (lw-rpow-bounds 2 2 3 1/20))))
                  (+ 1/100 1/20)))
