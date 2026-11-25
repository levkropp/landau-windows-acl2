(in-package "ACL2")

(include-book "euler-window-real-scan")
(include-book "euler-window-probe-modulation")

; Compute the two contours and the zero-sample tolerance before
; inspecting the supplied rational offset.

(local (defthm lw-ewcp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewcp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewcp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewcp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewcp-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewcp-times-negative)))))

(local (defthm lw-ewcp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewcp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewcp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewcp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewcp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewcp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewcp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewcp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewcp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewcp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewcp-left-commutes)))))

(local (deftheory lw-ewcp-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewcp-left-commutes lw-ewcp-left-distributes lw-ewcp-fold-constants
              lw-ewcp-times-negative lw-ewcp-negative-times lw-ewcp-zero-times
              lw-ewcp-minus-one lw-ewcp-double-negative lw-ewcp-add-cancel lw-ewcp-double lw-ewcp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-prepare-circles (cap slack seed-height)
  (let* ((real-data (lw-euler-window-real-covers cap slack))
         (empty (car real-data))
         (positive (cadr real-data))
         (real-radius (car empty))
         (gap (lw-euler-window-real-gap cap slack))
         (height (if positive
                     (lw-euler-window-probe-modulation-height cap gap real-radius positive)
                   seed-height))
         (modulated (lw-euler-window-modulated-cover height real-radius gap))
         (request (if positive 1 (lw-euler-window-modulated-request height real-radius gap))))
    (list height modulated empty (- real-radius (* 1/4 gap)) request)))

(defun lw-euler-window-zero-sample-request (cap slack seed-height)
  (nth 4 (lw-euler-window-prepare-circles cap slack seed-height)))

(defun lw-euler-window-small-samplep (cap slack seed-height offset)
  (let ((request (lw-euler-window-zero-sample-request cap slack seed-height)))
    (and (lw-complex-diskp offset (- cap slack))
         (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ seed-height (cdr offset)) (* 1/4 request)) request))))

(local
 (defthm lw-ewcp-band-probe
   (implies (and (rationalp cap) (< 251 cap) (< cap 252) (rationalp slack) (< 0 slack) (cadr (lw-euler-window-real-covers cap slack)))
            (and (rationalp (lw-euler-window-probe-modulation-height cap (lw-euler-window-real-gap cap slack) (car (car (lw-euler-window-real-covers cap slack))) (cadr (lw-euler-window-real-covers cap slack))))
                 (< 0 (lw-euler-circle-interior-count (cons 252 (lw-euler-window-probe-modulation-height cap (lw-euler-window-real-gap cap slack) (car (car (lw-euler-window-real-covers cap slack))) (cadr (lw-euler-window-real-covers cap slack)))) (car (lw-euler-window-modulated-cover (lw-euler-window-probe-modulation-height cap (lw-euler-window-real-gap cap slack) (car (car (lw-euler-window-real-covers cap slack))) (cadr (lw-euler-window-real-covers cap slack))) (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))) (cadr (lw-euler-window-modulated-cover (lw-euler-window-probe-modulation-height cap (lw-euler-window-real-gap cap slack) (car (car (lw-euler-window-real-covers cap slack))) (cadr (lw-euler-window-real-covers cap slack))) (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))) (caddr (lw-euler-window-modulated-cover (lw-euler-window-probe-modulation-height cap (lw-euler-window-real-gap cap slack) (car (car (lw-euler-window-real-covers cap slack))) (cadr (lw-euler-window-real-covers cap slack))) (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack)))))))
   :hints (("Goal"
            :use (lw-euler-window-real-covers-valid lw-euler-window-real-gap-data
                  (:instance lw-euler-window-real-band-step-data (gap (lw-euler-window-real-gap cap slack)))
                  (:instance lw-euler-window-probe-modulation-valid
                    (gap (lw-euler-window-real-gap cap slack)) (real-radius (car (car (lw-euler-window-real-covers cap slack)))) (positive (cadr (lw-euler-window-real-covers cap slack)))))
            :in-theory (theory 'lw-ewcp-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-prepared-circles-valid
  (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                (rationalp slack) (< 0 slack) (rationalp seed-height))
           (let* ((data (lw-euler-window-prepare-circles cap slack seed-height))
                  (height (car data))
                  (modulated (cadr data))
                  (empty (caddr data))
                  (real-radius (cadddr data)))
             (and (rationalp height) (rationalp (car modulated)) (rationalp (car empty))
                  (rationalp real-radius) (< 251 real-radius) (< real-radius (car empty)) (< (car empty) cap)
                  (< (car modulated) real-radius)
                  (lw-euler-circle-coverp (cons 252 height) (car modulated) (cadr modulated) (caddr modulated)) (lw-euler-circle-coverp (cons 252 0) (car empty) (cadr empty) (caddr empty))
                  (lw-euler-value-clearance-check 252 height (lw-euler-zeta-clearance-request 252 height)) (lw-euler-value-clearance-check 252 0 (lw-euler-zeta-clearance-request 252 0))
                  (equal (lw-euler-circle-interior-count (cons 252 0) (car empty) (cadr empty) (caddr empty)) 0)
                  (rationalp (lw-euler-window-zero-sample-request cap slack seed-height)) (< 0 (lw-euler-window-zero-sample-request cap slack seed-height)))))
  :hints (("Goal"
           :use (lw-euler-window-real-covers-valid lw-euler-window-real-gap-data lw-ewcp-band-probe
                 (:instance lw-euler-window-modulated-cover-valid (height seed-height) (gap (lw-euler-window-real-gap cap slack)) (real-radius (car (car (lw-euler-window-real-covers cap slack)))))
                 (:instance lw-euler-window-modulated-cover-valid (height (lw-euler-window-probe-modulation-height cap (lw-euler-window-real-gap cap slack) (car (car (lw-euler-window-real-covers cap slack))) (cadr (lw-euler-window-real-covers cap slack)))) (gap (lw-euler-window-real-gap cap slack)) (real-radius (car (car (lw-euler-window-real-covers cap slack)))))
                 (:instance lw-euler-window-modulated-request-positive (height seed-height) (gap (lw-euler-window-real-gap cap slack)) (real-radius (car (car (lw-euler-window-real-covers cap slack)))))
                 (:instance lw-euler-zeta-clearance-check (rate 252) (height 0)))
           :in-theory (union-theories '(lw-euler-window-prepare-circles lw-euler-window-zero-sample-request nth
                                       (:executable-counterpart binary-+) (:executable-counterpart unary--))
                                       (theory 'lw-ewcp-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ewcp-seed-modulation-count
   (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                (rationalp slack) (< 0 slack) (rationalp seed-height)
                 (not (cadr (lw-euler-window-real-covers cap slack))) (lw-euler-window-small-samplep cap slack seed-height offset))
            (< 0 (lw-euler-circle-interior-count (cons 252 seed-height) (car (lw-euler-window-modulated-cover seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))) (cadr (lw-euler-window-modulated-cover seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))) (caddr (lw-euler-window-modulated-cover seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))))))
   :hints (("Goal"
            :use (lw-euler-window-real-covers-valid lw-euler-window-real-gap-data
                  (:instance lw-euler-window-real-band-step-data (gap (lw-euler-window-real-gap cap slack)))
                  (:instance lw-euler-window-modulated-cover-valid (height seed-height) (gap (lw-euler-window-real-gap cap slack)) (real-radius (car (car (lw-euler-window-real-covers cap slack)))))
                  (:instance lw-euler-window-modulated-request-positive (height seed-height) (gap (lw-euler-window-real-gap cap slack)) (real-radius (car (car (lw-euler-window-real-covers cap slack)))))
                  (:instance lw-complex-disk-enlarge (point offset) (radius (- cap slack)) (cap (- (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))))
                  (:instance lw-euler-window-positive-count-from-interior-sample
                    (height seed-height) (radius (car (lw-euler-window-modulated-cover seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))))
                    (plus-arcs (cadr (lw-euler-window-modulated-cover seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack)))) (minus-arcs (caddr (lw-euler-window-modulated-cover seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))))
                    (inner-radius (- (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))) (error (* 1/4 (lw-euler-window-modulated-request seed-height (car (car (lw-euler-window-real-covers cap slack))) (lw-euler-window-real-gap cap slack))))))
            :in-theory (union-theories '(lw-euler-window-small-samplep lw-euler-window-zero-sample-request
                                         lw-euler-window-prepare-circles lw-euler-window-modulated-request nth
                                         (:executable-counterpart binary-+) (:executable-counterpart unary--))
                                        (theory 'lw-ewcp-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-prepared-circles-positive-count
  (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                (rationalp slack) (< 0 slack) (rationalp seed-height)
                (lw-euler-window-small-samplep cap slack seed-height offset))
           (let* ((data (lw-euler-window-prepare-circles cap slack seed-height))
                  (height (car data))
                  (modulated (cadr data)))
             (< 0 (lw-euler-circle-interior-count (cons 252 height) (car modulated) (cadr modulated) (caddr modulated)))))
  :hints (("Goal"
           :use (lw-ewcp-band-probe lw-ewcp-seed-modulation-count)
           :in-theory (union-theories '(lw-euler-window-prepare-circles) (theory 'lw-ewcp-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
