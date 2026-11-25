(in-package "ACL2")

(include-book "signal-growth")

(local (defthm lw-ms-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ms-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

; Rational complex geometry. No square roots or analytic norm are needed.
(defun lw-diskp (real imag radius)
  (and (rationalp real) (rationalp imag) (rationalp radius) (<= 0 radius)
       (<= (+ (* real real) (* imag imag)) (* radius radius))))

(local
 (defthm lw-ms-square-order
   (implies (and (rationalp left) (rationalp right) (<= 0 right)
                 (<= (* left left) (* right right)))
            (<= left right))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ms-lagrange-identity
   (implies (and (rationalp x) (rationalp y) (rationalp u) (rationalp v))
            (equal (+ (* (+ (* x u) (* y v)) (+ (* x u) (* y v)))
                      (* (- (* x v) (* y u)) (- (* x v) (* y u))))
                   (* (+ (* x x) (* y y)) (+ (* u u) (* v v)))))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ms-square-nonnegative
   (implies (rationalp value) (<= 0 (* value value)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ms-multiply-order
   (implies (and (rationalp left) (rationalp right) (<= left right)
                 (rationalp factor) (<= 0 factor))
            (<= (* left factor) (* right factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ms-norm-product-bound
   (implies (and (lw-diskp x y radius) (lw-diskp u v other-radius))
            (<= (* (+ (* x x) (* y y)) (+ (* u u) (* v v)))
                (* radius radius other-radius other-radius)))
   :hints (("Goal"
            :use ((:instance lw-ms-square-nonnegative (value u))
                  (:instance lw-ms-square-nonnegative (value v))
                  (:instance lw-ms-multiply-order
                    (left (+ (* x x) (* y y))) (right (* radius radius))
                    (factor (+ (* u u) (* v v))))
                  (:instance lw-ms-multiply-order
                    (left (+ (* u u) (* v v))) (right (* other-radius other-radius))
                    (factor (* radius radius))))))
   :rule-classes nil))

(local
 (defthm lw-ms-dot-square-bound
   (implies (and (lw-diskp x y radius) (lw-diskp u v other-radius))
            (<= (* (+ (* x u) (* y v)) (+ (* x u) (* y v)))
                (* radius radius other-radius other-radius)))
   :hints (("Goal" :use (lw-ms-lagrange-identity lw-ms-norm-product-bound
                          (:instance lw-ms-square-nonnegative (value (- (* x v) (* y u)))))
                   :nonlinearp t))
   :rule-classes nil))

(defthm lw-disk-dot-bound
  (implies (and (lw-diskp x y radius) (lw-diskp u v other-radius))
           (<= (+ (* x u) (* y v)) (* radius other-radius)))
  :hints (("Goal" :use (lw-ms-dot-square-bound
                        (:instance lw-ms-square-order
                          (left (+ (* x u) (* y v))) (right (* radius other-radius))))
                  :nonlinearp t))
  :rule-classes nil)

(defthm lw-disk-add
  (implies (and (lw-diskp x y radius) (lw-diskp u v other-radius))
           (lw-diskp (+ x u) (+ y v) (+ radius other-radius)))
  :hints (("Goal" :use (lw-disk-dot-bound) :nonlinearp t)))

(defthm lw-disk-enlarge
  (implies (and (lw-diskp real imag radius) (rationalp cap) (<= radius cap))
           (lw-diskp real imag cap))
  :hints (("Goal" :nonlinearp t)))

; A row is (value weight phase-real phase-imag cap). Its phase lies in
; the unit disk, its weight is nonnegative and value <= cap, cap >= 0.
; Inside the window cap will be computed from search failure. Outside it
; may be a growth envelope; the theorem keeps its contribution explicit.
(defun lw-mellin-rowp (row)
  (and (true-listp row) (equal (len row) 5)
       (rationalp (nth 0 row))
       (rationalp (nth 1 row)) (<= 0 (nth 1 row))
       (lw-diskp (nth 2 row) (nth 3 row) 1)
       (rationalp (nth 4 row)) (<= 0 (nth 4 row))
       (<= (nth 0 row) (nth 4 row))))

(defun lw-mellin-rowsp (rows)
  (if (consp rows)
      (and (lw-mellin-rowp (car rows)) (lw-mellin-rowsp (cdr rows)))
    (equal rows nil)))

(defun lw-mellin-real (rows)
  (if (consp rows)
      (+ (* (nth 0 (car rows)) (nth 1 (car rows)) (nth 2 (car rows)))
         (lw-mellin-real (cdr rows)))
    0))

(defun lw-mellin-imag (rows)
  (if (consp rows)
      (+ (* (nth 0 (car rows)) (nth 1 (car rows)) (nth 3 (car rows)))
         (lw-mellin-imag (cdr rows)))
    0))

(defun lw-mellin-plain (rows)
  (if (consp rows)
      (+ (* (nth 0 (car rows)) (nth 1 (car rows)))
         (lw-mellin-plain (cdr rows)))
    0))

(defun lw-mellin-mass (rows)
  (if (consp rows)
      (+ (* (abs (nth 0 (car rows))) (nth 1 (car rows)))
         (lw-mellin-mass (cdr rows)))
    0))

(defun lw-mellin-budget (rows)
  (if (consp rows)
      (+ (* (nth 4 (car rows)) (nth 1 (car rows)))
         (lw-mellin-budget (cdr rows)))
    0))

(defthm lw-mellin-sums-rational
  (implies (lw-mellin-rowsp rows)
           (and (rationalp (lw-mellin-real rows))
                (rationalp (lw-mellin-imag rows))
                (rationalp (lw-mellin-plain rows))
                (rationalp (lw-mellin-mass rows))
                (rationalp (lw-mellin-budget rows)))))

(local
 (defthm lw-ms-row-disk
   (implies (lw-mellin-rowp row)
            (lw-diskp (* (nth 0 row) (nth 1 row) (nth 2 row))
                      (* (nth 0 row) (nth 1 row) (nth 3 row))
                      (* (abs (nth 0 row)) (nth 1 row))))
   :hints (("Goal" :nonlinearp t))))

(defthm lw-mellin-triangle
  (implies (lw-mellin-rowsp rows)
           (lw-diskp (lw-mellin-real rows) (lw-mellin-imag rows) (lw-mellin-mass rows)))
  :hints (("Goal" :induct (lw-mellin-rowsp rows)
                  :in-theory (disable lw-diskp lw-mellin-rowp))
          ("Subgoal *1/1" :use ((:instance lw-ms-row-disk (row (car rows)))
                                (:instance lw-disk-add
                                  (x (* (nth 0 (car rows)) (nth 1 (car rows)) (nth 2 (car rows))))
                                  (y (* (nth 0 (car rows)) (nth 1 (car rows)) (nth 3 (car rows))))
                                  (radius (* (abs (nth 0 (car rows))) (nth 1 (car rows))))
                                  (u (lw-mellin-real (cdr rows)))
                                  (v (lw-mellin-imag (cdr rows)))
                                  (other-radius (lw-mellin-mass (cdr rows))))))))

; This is the one-sided cancellation: large negative values disappear
; from |sum| + the unmodulated sum. No lower bound on value is assumed.
(local
 (defthm lw-ms-row-positive-part
   (implies (lw-mellin-rowp row)
            (<= (+ (* (abs (nth 0 row)) (nth 1 row))
                   (* (nth 0 row) (nth 1 row)))
                (* 2 (nth 4 row) (nth 1 row))))
   :hints (("Goal" :nonlinearp t))))

(defthm lw-mellin-positive-part
  (implies (lw-mellin-rowsp rows)
           (<= (+ (lw-mellin-mass rows) (lw-mellin-plain rows))
               (* 2 (lw-mellin-budget rows))))
  :hints (("Goal" :induct (lw-mellin-rowsp rows)
                  :in-theory (disable lw-mellin-rowp))
          ("Subgoal *1/1" :use ((:instance lw-ms-row-positive-part (row (car rows)))))))

(defthm lw-mellin-one-sided-bound
  (implies (lw-mellin-rowsp rows)
           (lw-diskp (lw-mellin-real rows) (lw-mellin-imag rows)
                     (- (* 2 (lw-mellin-budget rows)) (lw-mellin-plain rows))))
  :hints (("Goal" :use (lw-mellin-triangle lw-mellin-positive-part
                        (:instance lw-disk-enlarge
                          (real (lw-mellin-real rows)) (imag (lw-mellin-imag rows))
                          (radius (lw-mellin-mass rows))
                          (cap (- (* 2 (lw-mellin-budget rows)) (lw-mellin-plain rows)))))
                  :in-theory (disable lw-mellin-real lw-mellin-imag lw-mellin-plain
                                      lw-mellin-mass lw-mellin-budget lw-mellin-rowsp
                                      lw-mellin-triangle lw-mellin-positive-part
                                      lw-diskp lw-disk-enlarge))))

; The failure ceiling persists for every finer lower approximation. This
; supplies arbitrarily precise quadrature values, rather than freezing the
; integral to the original search precision.
(defthm lw-failed-search-refined-gz-ceiling
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp point) (<= start point) (<= (* point point) (* start start start))
                (rationalp epsilon) (< 0 epsilon) (<= epsilon 1))
           (<= (car (lw-gz-bounds-raw point (lw-signal-count point) epsilon))
               (* (+ ceiling 1)
                  (car (lw-rpow-bounds point numerator denominator
                                      (lw-signal-precision point ceiling 1/4))))))
  :hints (("Goal"
           :use (lw-landau-search-failure-gz-ceiling
                 (:instance lw-signal-precision-positive (value point) (error 1/4))
                 (:instance lw-gz-bounds-raw-transport
                   (left point) (right point) (cap point) (count (lw-signal-count point))
                   (left-error epsilon) (right-error (lw-signal-precision point ceiling 1/4))))
           :in-theory (disable lw-landau-window-search lw-landau-search-failure-gz-ceiling
                               lw-signal-precision lw-signal-precision-positive lw-signal-count
                               lw-gz-bounds-raw lw-gz-bounds-raw-transport lw-rpow-bounds))))

; Input datum: (point primitive-error weight phase-real phase-imag).
(defun lw-mellin-window-datump (datum start)
  (and (true-listp datum) (equal (len datum) 5)
       (rationalp (nth 0 datum)) (<= start (nth 0 datum))
       (<= (* (nth 0 datum) (nth 0 datum)) (* start start start))
       (rationalp (nth 1 datum)) (< 0 (nth 1 datum)) (<= (nth 1 datum) 1)
       (rationalp (nth 2 datum)) (<= 0 (nth 2 datum))
       (lw-diskp (nth 3 datum) (nth 4 datum) 1)))

(defun lw-mellin-window-datap (data start)
  (if (consp data)
      (and (lw-mellin-window-datump (car data) start) (lw-mellin-window-datap (cdr data) start))
    (equal data nil)))

(defun lw-mellin-window-row (datum ceiling numerator denominator)
  (let* ((point (nth 0 datum))
         (epsilon (nth 1 datum))
         (value (car (lw-gz-bounds-raw point (lw-signal-count point) epsilon)))
         (cap (* (+ ceiling 1)
                 (car (lw-rpow-bounds point numerator denominator
                                     (lw-signal-precision point ceiling 1/4))))))
    (list value (nth 2 datum) (nth 3 datum) (nth 4 datum) cap)))

(defun lw-mellin-window-rows (data ceiling numerator denominator)
  (if (consp data)
      (cons (lw-mellin-window-row (car data) ceiling numerator denominator)
            (lw-mellin-window-rows (cdr data) ceiling numerator denominator))
    nil))

(defthm lw-failed-search-mellin-row-valid
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (lw-mellin-window-datump datum start))
           (lw-mellin-rowp (lw-mellin-window-row datum ceiling numerator denominator)))
  :hints (("Goal"
           :use ((:instance lw-failed-search-refined-gz-ceiling
                   (point (nth 0 datum)) (epsilon (nth 1 datum)))
                 (:instance lw-signal-precision-positive (value (nth 0 datum)) (error 1/4))
                 (:instance lw-gz-bounds-raw-valid
                   (value (nth 0 datum)) (count (lw-signal-count (nth 0 datum))) (epsilon (nth 1 datum)))
                 (:instance lw-rpow-bounds-sound
                   (value (nth 0 datum)) (epsilon (lw-signal-precision (nth 0 datum) ceiling 1/4))))
           :in-theory (disable lw-landau-window-search lw-failed-search-refined-gz-ceiling
                               lw-signal-precision lw-signal-precision-positive lw-signal-count
                               lw-gz-bounds-raw lw-gz-bounds-raw-valid lw-rpow-bounds lw-rpow-bounds-sound
                               lw-diskp lw-rational-power)
           :nonlinearp t)))

(defthm lw-failed-search-mellin-rows-valid
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (lw-mellin-window-datap data start))
           (lw-mellin-rowsp (lw-mellin-window-rows data ceiling numerator denominator)))
  :hints (("Goal" :induct (lw-mellin-window-datap data start)
                  :in-theory (disable lw-mellin-window-datump lw-mellin-rowp
                                      lw-mellin-window-row lw-landau-window-search))))

(defthm lw-failed-search-finite-mellin-bound
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (lw-mellin-window-datap data start))
           (let ((rows (lw-mellin-window-rows data ceiling numerator denominator)))
             (lw-diskp (lw-mellin-real rows) (lw-mellin-imag rows)
                       (- (* 2 (lw-mellin-budget rows)) (lw-mellin-plain rows)))))
  :hints (("Goal" :use ((:instance lw-mellin-one-sided-bound
                          (rows (lw-mellin-window-rows data ceiling numerator denominator))))
                  :in-theory (disable lw-diskp lw-mellin-real lw-mellin-imag lw-mellin-budget
                                      lw-mellin-plain lw-mellin-rowsp lw-mellin-one-sided-bound
                                      lw-mellin-window-rows lw-mellin-window-datap lw-landau-window-search))))

; Samples outside the window use the proved global growth envelope.
; The data format agrees with window data, but no window test is needed.
(defun lw-mellin-growth-datump (datum)
  (and (true-listp datum) (equal (len datum) 5)
       (rationalp (nth 0 datum)) (< 1 (nth 0 datum))
       (rationalp (nth 1 datum)) (< 0 (nth 1 datum)) (<= (nth 1 datum) 1)
       (rationalp (nth 2 datum)) (<= 0 (nth 2 datum))
       (lw-diskp (nth 3 datum) (nth 4 datum) 1)))

(defun lw-mellin-growth-datap (data)
  (if (consp data)
      (and (lw-mellin-growth-datump (car data)) (lw-mellin-growth-datap (cdr data)))
    (equal data nil)))

(defun lw-mellin-growth-row (datum)
  (let* ((point (nth 0 datum))
         (value (car (lw-gz-bounds-raw point (lw-signal-count point) (nth 1 datum)))))
    (list value (nth 2 datum) (nth 3 datum) (nth 4 datum) (* 4 point point))))

(defun lw-mellin-growth-rows (data)
  (if (consp data)
      (cons (lw-mellin-growth-row (car data)) (lw-mellin-growth-rows (cdr data)))
    nil))

(defthm lw-mellin-growth-row-valid
  (implies (lw-mellin-growth-datump datum)
           (lw-mellin-rowp (lw-mellin-growth-row datum)))
  :hints (("Goal"
           :use ((:instance lw-gz-lower-quadratic-growth
                   (value (nth 0 datum)) (count (lw-signal-count (nth 0 datum))) (epsilon (nth 1 datum)))
                 (:instance lw-gz-bounds-raw-valid
                   (value (nth 0 datum)) (count (lw-signal-count (nth 0 datum))) (epsilon (nth 1 datum))))
           :in-theory (disable lw-gz-bounds-raw lw-gz-lower-quadratic-growth
                               lw-gz-bounds-raw-valid lw-signal-count lw-diskp)
           :nonlinearp t)))

(defthm lw-mellin-growth-rows-valid
  (implies (lw-mellin-growth-datap data)
           (lw-mellin-rowsp (lw-mellin-growth-rows data)))
  :hints (("Goal" :induct (lw-mellin-growth-datap data)
                  :in-theory (disable lw-mellin-growth-datump lw-mellin-growth-row lw-mellin-rowp))))

(defthm lw-mellin-rows-append
  (implies (and (lw-mellin-rowsp left) (lw-mellin-rowsp right))
           (lw-mellin-rowsp (append left right))))

(defthm lw-mellin-sums-append
  (and (equal (lw-mellin-real (append left right)) (+ (lw-mellin-real left) (lw-mellin-real right)))
       (equal (lw-mellin-imag (append left right)) (+ (lw-mellin-imag left) (lw-mellin-imag right)))
       (equal (lw-mellin-plain (append left right)) (+ (lw-mellin-plain left) (lw-mellin-plain right)))
       (equal (lw-mellin-mass (append left right)) (+ (lw-mellin-mass left) (lw-mellin-mass right)))
       (equal (lw-mellin-budget (append left right)) (+ (lw-mellin-budget left) (lw-mellin-budget right)))))

(defthm lw-failed-search-finite-mellin-bound-with-tail
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (lw-mellin-window-datap window-data start) (lw-mellin-growth-datap tail-data))
           (let* ((window-rows (lw-mellin-window-rows window-data ceiling numerator denominator))
                  (tail-rows (lw-mellin-growth-rows tail-data))
                  (rows (append window-rows tail-rows)))
             (lw-diskp (lw-mellin-real rows) (lw-mellin-imag rows)
                       (+ (* 2 (lw-mellin-budget window-rows))
                          (* 2 (lw-mellin-budget tail-rows)) (- (lw-mellin-plain rows))))))
  :hints (("Goal"
           :use ((:instance lw-mellin-one-sided-bound
                   (rows (append (lw-mellin-window-rows window-data ceiling numerator denominator)
                                 (lw-mellin-growth-rows tail-data)))))
           :in-theory (disable lw-diskp lw-mellin-real lw-mellin-imag lw-mellin-budget lw-mellin-plain
                               lw-mellin-rowsp lw-mellin-one-sided-bound lw-mellin-window-rows
                               lw-mellin-growth-rows lw-mellin-window-datap lw-mellin-growth-datap
                               lw-landau-window-search))))

; Finite approximation errors are retained explicitly. An analytic
; application must still compute and prove these errors tend to zero.
(defthm lw-mellin-bound-with-remainders
  (implies (and (lw-mellin-rowsp rows)
                (rationalp coefficient-real) (rationalp coefficient-imag)
                (rationalp plain-coefficient) (rationalp plain-error) (<= 0 plain-error)
                (<= (- plain-coefficient (lw-mellin-plain rows)) plain-error)
                (lw-diskp (- coefficient-real (lw-mellin-real rows))
                          (- coefficient-imag (lw-mellin-imag rows)) coefficient-error))
           (lw-diskp coefficient-real coefficient-imag
                     (+ (* 2 (lw-mellin-budget rows)) (- plain-coefficient)
                        coefficient-error plain-error)))
  :hints (("Goal"
           :use (lw-mellin-one-sided-bound
                 (:instance lw-disk-add
                   (x (lw-mellin-real rows)) (y (lw-mellin-imag rows))
                   (radius (- (* 2 (lw-mellin-budget rows)) (lw-mellin-plain rows)))
                   (u (- coefficient-real (lw-mellin-real rows)))
                   (v (- coefficient-imag (lw-mellin-imag rows))) (other-radius coefficient-error))
                 (:instance lw-disk-enlarge
                   (real coefficient-real) (imag coefficient-imag)
                   (radius (+ (* 2 (lw-mellin-budget rows)) (- (lw-mellin-plain rows)) coefficient-error))
                   (cap (+ (* 2 (lw-mellin-budget rows)) (- plain-coefficient) coefficient-error plain-error))))
           :in-theory (disable lw-mellin-real lw-mellin-imag lw-mellin-budget lw-mellin-plain
                               lw-mellin-rowsp lw-mellin-one-sided-bound lw-disk-add lw-disk-enlarge))))

(assert-event
 (let ((rows '((-100 1 0 1 2) (1 1 1 0 2))))
   (and (lw-mellin-rowsp rows)
        (lw-diskp (lw-mellin-real rows) (lw-mellin-imag rows)
                  (- (* 2 (lw-mellin-budget rows)) (lw-mellin-plain rows))))))

(assert-event
 (and (not (lw-mellin-rowp '(3 1 1 0 2)))
      (not (lw-mellin-rowp '(1 1 1 1 2)))
      (lw-mellin-growth-datap '((3/2 1/2 1/10 3/5 4/5)))
      (lw-mellin-rowsp (lw-mellin-growth-rows '((3/2 1/2 1/10 3/5 4/5))))))
