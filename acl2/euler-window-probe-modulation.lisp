(in-package "ACL2")

(include-book "euler-window-real-bands")
(include-book "euler-window-modulated-covers")

; A positive real count supplies an interior probe. Round its height
; to one of the prepared modulated covers, using the certified gap.

(local (defthm lw-ewpm-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewpm-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewpm-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewpm-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewpm-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewpm-times-negative)))))

(local (defthm lw-ewpm-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewpm-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewpm-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewpm-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewpm-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewpm-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewpm-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewpm-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewpm-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewpm-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewpm-left-commutes)))))

(local (deftheory lw-ewpm-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewpm-left-commutes lw-ewpm-left-distributes lw-ewpm-fold-constants
              lw-ewpm-times-negative lw-ewpm-negative-times lw-ewpm-zero-times
              lw-ewpm-minus-one lw-ewpm-double-negative lw-ewpm-add-cancel lw-ewpm-double lw-ewpm-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-real-probe-tolerance (cap gap real-radius)
  (min (lw-euler-real-circle-probe-request (lw-euler-window-real-outer cap) gap) (lw-euler-window-height-request cap gap real-radius (lw-euler-window-height-count cap gap))))

(defun lw-euler-window-real-probe-offset (cap gap real-radius positive)
  (lw-euler-circle-interior-probe-offset
   (cons 252 0) (car positive) (cadr positive) (caddr positive) (lw-euler-window-real-probe-tolerance cap gap real-radius)))

(defun lw-euler-window-probe-modulation-height (cap gap real-radius positive)
  (lw-euler-window-grid-height cap gap
    (lw-euler-window-height-index cap gap (cdr (lw-euler-window-real-probe-offset cap gap real-radius positive)))))

(local
 (defthm lw-ewpm-tolerance
   (implies (and (rationalp cap) (< 251 cap) (< cap 252) (rationalp gap) (< 0 gap))
            (and (rationalp (lw-euler-window-real-probe-tolerance cap gap real-radius)) (< 0 (lw-euler-window-real-probe-tolerance cap gap real-radius)) (<= (lw-euler-window-real-probe-tolerance cap gap real-radius) (lw-euler-real-circle-probe-request (lw-euler-window-real-outer cap) gap)) (<= (lw-euler-window-real-probe-tolerance cap gap real-radius) (lw-euler-window-height-request cap gap real-radius (lw-euler-window-height-count cap gap)))))
   :hints (("Goal"
            :use ((:instance lw-euler-real-circle-probe-request-data (outer-radius (lw-euler-window-real-outer cap)))
                  (:instance lw-euler-window-height-request-positive (last (lw-euler-window-height-count cap gap))))
            :in-theory (union-theories '(lw-euler-window-real-outer
                                         lw-euler-window-real-probe-tolerance min)
                                       (theory 'lw-ewpm-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewpm-offset-geometry
   (implies (and (lw-complexp offset) (rationalp height) (<= (cdr offset) height)
                 (< height (+ (cdr offset) gap))
                 (rationalp gap) (< 0 gap) (< 0 (- (car offset)))
                 (rationalp real-radius) (< (+ (- (car offset)) (* 8 gap)) (+ real-radius gap)))
            (lw-complex-diskp (cons (car offset) (- (cdr offset) height)) (- real-radius gap)))
   :hints (("Goal"
            :use ((:instance lw-complex-l1-bound (point (cons (car offset) (- (cdr offset) height))))
                  (:instance lw-complex-disk-enlarge (point (cons (car offset) (- (cdr offset) height)))
                     (radius (lw-complex-l1 (cons (car offset) (- (cdr offset) height)))) (cap (- real-radius gap))))
            :in-theory (union-theories '(lw-complexp lw-complex-l1 abs) (theory 'lw-ewpm-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewpm-checked-real-probe
   (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                 (rationalp gap) (< 0 gap) (<= gap 1/4) (<= (* 8192 gap) (* (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap) (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap)))
                 (rationalp real-radius) (< (+ 251 (* 2 gap)) real-radius) (< real-radius cap)
                 (rationalp (car positive)) (< (car positive) cap)
                 (< (car positive) (+ real-radius gap))
                 (lw-euler-circle-coverp (cons 252 0) (car positive) (cadr positive) (caddr positive))
                 (< 0 (lw-euler-circle-interior-count (cons 252 0) (car positive) (cadr positive) (caddr positive))))
            (and (lw-complexp (lw-euler-window-real-probe-offset cap gap real-radius positive))
                 (<= (- cap) (cdr (lw-euler-window-real-probe-offset cap gap real-radius positive))) (<= (cdr (lw-euler-window-real-probe-offset cap gap real-radius positive)) cap)
                 (< 0 (- (car (lw-euler-window-real-probe-offset cap gap real-radius positive))))
                 (< (+ (- (car (lw-euler-window-real-probe-offset cap gap real-radius positive))) (* 8 gap)) (+ real-radius gap))
                 (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car (lw-euler-window-real-probe-offset cap gap real-radius positive))) (cdr (lw-euler-window-real-probe-offset cap gap real-radius positive)) (lw-euler-window-real-probe-tolerance cap gap real-radius)) (lw-euler-window-real-probe-tolerance cap gap real-radius))))
   :hints (("Goal"
            :use (lw-ewpm-tolerance
                  (:instance lw-euler-real-circle-checked-probe-geometry
                    (outer-radius (lw-euler-window-real-outer cap)) (radius (car positive))
                    (plus-arcs (cadr positive)) (minus-arcs (caddr positive))
                    (tolerance (lw-euler-window-real-probe-tolerance cap gap real-radius)) (error (lw-euler-window-real-probe-tolerance cap gap real-radius)))
                  (:instance lw-complex-disk-data (point (lw-euler-window-real-probe-offset cap gap real-radius positive)) (radius (car positive)))
                  (:instance lw-complex-disk-coordinates (point (lw-euler-window-real-probe-offset cap gap real-radius positive)) (radius (car positive))))
            :in-theory (union-theories '(lw-euler-window-real-outer lw-euler-window-real-probe-offset
                                        lw-complexp abs)
                                       (theory 'lw-ewpm-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewpm-grid-request
   (implies (and (rationalp cap) (< 251 cap) (< cap 252) (rationalp gap) (< 0 gap)
                 (lw-complexp offset) (<= (- cap) (cdr offset)) (<= (cdr offset) cap)
                 (rationalp real-radius))
            (let* ((index (lw-euler-window-height-index cap gap (cdr offset)))
                   (height (lw-euler-window-grid-height cap gap index)))
              (and (rationalp height) (<= (cdr offset) height) (< height (+ (cdr offset) gap))
                   (rationalp (lw-euler-window-modulated-request height real-radius gap))
                   (<= (lw-euler-window-real-probe-tolerance cap gap real-radius) (lw-euler-window-modulated-request height real-radius gap)))))
   :hints (("Goal"
            :use (lw-ewpm-tolerance
                  (:instance lw-euler-window-height-count-natural (step gap))
                  (:instance lw-euler-window-height-index-data (step gap) (height (cdr offset)))
                  (:instance lw-euler-window-grid-height-rational (step gap)
                    (index (lw-euler-window-height-index cap gap (cdr offset))))
                  (:instance lw-euler-window-height-request-positive (last (lw-euler-window-height-count cap gap)))
                  (:instance lw-euler-window-height-request-valid (last (lw-euler-window-height-count cap gap))
                    (index (lw-euler-window-height-index cap gap (cdr offset))))
                  (:instance lw-euler-window-modulated-request-positive
                    (height (lw-euler-window-grid-height cap gap (lw-euler-window-height-index cap gap (cdr offset))))))
            :in-theory (union-theories '(lw-complexp) (theory 'lw-ewpm-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-probe-modulation-valid
  (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                (rationalp gap) (< 0 gap) (<= gap 1/4) (<= (* 8192 gap) (* (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap) (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap)))
                (rationalp real-radius) (< (+ 251 (* 2 gap)) real-radius) (< real-radius cap)
                (rationalp (car positive)) (< (car positive) cap)
                (< (car positive) (+ real-radius gap))
                (lw-euler-circle-coverp (cons 252 0) (car positive) (cadr positive) (caddr positive))
                (< 0 (lw-euler-circle-interior-count (cons 252 0) (car positive) (cadr positive) (caddr positive))))
           (let* ((height (lw-euler-window-probe-modulation-height cap gap real-radius positive))
                  (data (lw-euler-window-modulated-cover height real-radius gap)))
             (and (rationalp height)
                  (< 0 (lw-euler-circle-interior-count (cons 252 height) (car data) (cadr data) (caddr data))))))
  :hints (("Goal"
           :use (lw-ewpm-tolerance lw-ewpm-checked-real-probe
                 (:instance lw-ewpm-grid-request (offset (lw-euler-window-real-probe-offset cap gap real-radius positive)))
                 (:instance lw-ewpm-offset-geometry (offset (lw-euler-window-real-probe-offset cap gap real-radius positive)) (height (lw-euler-window-probe-modulation-height cap gap real-radius positive)))
                 (:instance lw-euler-window-modulated-cover-valid (height (lw-euler-window-probe-modulation-height cap gap real-radius positive)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-euler-continuation-value (+ 252 (car (lw-euler-window-real-probe-offset cap gap real-radius positive))) (cdr (lw-euler-window-real-probe-offset cap gap real-radius positive)) (lw-euler-window-real-probe-tolerance cap gap real-radius)))
                   (radius (lw-euler-window-real-probe-tolerance cap gap real-radius)) (cap (lw-euler-window-modulated-request (lw-euler-window-probe-modulation-height cap gap real-radius positive) real-radius gap)))
                 (:instance lw-euler-window-positive-count-from-interior-sample
                   (height (lw-euler-window-probe-modulation-height cap gap real-radius positive)) (radius (car (lw-euler-window-modulated-cover (lw-euler-window-probe-modulation-height cap gap real-radius positive) real-radius gap))) (inner-radius (- real-radius gap))
                   (plus-arcs (cadr (lw-euler-window-modulated-cover (lw-euler-window-probe-modulation-height cap gap real-radius positive) real-radius gap))) (minus-arcs (caddr (lw-euler-window-modulated-cover (lw-euler-window-probe-modulation-height cap gap real-radius positive) real-radius gap)))
                   (offset (cons (car (lw-euler-window-real-probe-offset cap gap real-radius positive)) (- (cdr (lw-euler-window-real-probe-offset cap gap real-radius positive)) (lw-euler-window-probe-modulation-height cap gap real-radius positive)))) (error (lw-euler-window-real-probe-tolerance cap gap real-radius))))
           :in-theory (union-theories '(lw-euler-window-probe-modulation-height lw-euler-window-modulated-request
                                        lw-complexp)
                                       (theory 'lw-ewpm-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
