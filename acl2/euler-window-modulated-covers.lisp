(in-package "ACL2")

(include-book "euler-window-circle-cover")
(include-book "euler-window-interior-sample")
(include-book "euler-window-height-grid")

; A modulated band lies strictly below the real normalization radius.
; Prepare one request small enough for every possible rounded height.

(local (defthm lw-ewmc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewmc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewmc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewmc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewmc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewmc-times-negative)))))

(local (defthm lw-ewmc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewmc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewmc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewmc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewmc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewmc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewmc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewmc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewmc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewmc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewmc-left-commutes)))))

(local (deftheory lw-ewmc-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewmc-left-commutes lw-ewmc-left-distributes lw-ewmc-fold-constants
              lw-ewmc-times-negative lw-ewmc-negative-times lw-ewmc-zero-times
              lw-ewmc-minus-one lw-ewmc-double-negative lw-ewmc-add-cancel lw-ewmc-double lw-ewmc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-modulated-cover (height real-radius gap)
  (lw-euler-window-circle-cover height (- real-radius (* 3/4 gap)) (- real-radius (* 1/2 gap))))

(defun lw-euler-window-modulated-request (height real-radius gap)
  (lw-euler-window-interior-sample-request height (car (lw-euler-window-modulated-cover height real-radius gap)) (- real-radius gap)))

(defun lw-euler-window-height-request (cap gap real-radius last)
  (declare (xargs :measure (nfix last)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp last) (lw-euler-window-modulated-request (lw-euler-window-grid-height cap gap 0) real-radius gap)
    (min (lw-euler-window-modulated-request (lw-euler-window-grid-height cap gap last) real-radius gap)
         (lw-euler-window-height-request cap gap real-radius (- last 1)))))

(defthm lw-euler-window-modulated-cover-valid
  (implies (and (rationalp height) (rationalp gap) (< 0 gap)
                (rationalp real-radius) (< (+ 251 (* 2 gap)) real-radius) (< real-radius 252))
           (let ((data (lw-euler-window-modulated-cover height real-radius gap)))
             (and (rationalp (car data))
                  (< 251 (- real-radius (* 1/4 gap))) (< (- real-radius (* 1/4 gap)) real-radius)
                  (< 0 (- real-radius gap)) (< (- real-radius gap) (car data))
                  (< (car data) (- real-radius (* 1/4 gap))) (< (car data) 252)
                  (lw-euler-circle-coverp (cons 252 height) (car data) (cadr data) (caddr data))
                  (lw-euler-value-clearance-check 252 height (lw-euler-zeta-clearance-request 252 height)))))
  :hints (("Goal"
           :use ((:instance lw-euler-window-circle-cover-valid
                   (lower (- real-radius (* 3/4 gap))) (upper (- real-radius (* 1/2 gap)))))
           :in-theory (union-theories '(lw-euler-window-modulated-cover) (theory 'lw-ewmc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-window-modulated-request-positive
  (and (rationalp (lw-euler-window-modulated-request height real-radius gap)) (< 0 (lw-euler-window-modulated-request height real-radius gap)))
  :hints (("Goal"
           :use ((:instance lw-euler-window-interior-sample-request-positive
                            (radius (car (lw-euler-window-modulated-cover height real-radius gap))) (inner-radius (- real-radius gap))))
           :in-theory (union-theories '(lw-euler-window-modulated-request) (theory 'lw-ewmc-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-window-height-request-positive
  (and (rationalp (lw-euler-window-height-request cap gap real-radius last)) (< 0 (lw-euler-window-height-request cap gap real-radius last)))
  :hints (("Goal"
           :induct (lw-euler-window-height-request cap gap real-radius last)
           :in-theory (union-theories '(lw-euler-window-height-request min) (theory 'lw-ewmc-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-euler-window-modulated-request-positive (height (lw-euler-window-grid-height cap gap 0)))
                       (:instance lw-euler-window-modulated-request-positive (height (lw-euler-window-grid-height cap gap last))))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-euler-window-height-request-valid
  (implies (and (natp index) (natp last) (<= index last))
           (<= (lw-euler-window-height-request cap gap real-radius last) (lw-euler-window-modulated-request (lw-euler-window-grid-height cap gap index) real-radius gap)))
  :hints (("Goal"
           :induct (lw-euler-window-height-request cap gap real-radius last)
           :in-theory (union-theories '(lw-euler-window-height-request min) (theory 'lw-ewmc-arithmetic))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-euler-window-height-request-positive (last (- last 1)))
                       (:instance lw-euler-window-modulated-request-positive (height (lw-euler-window-grid-height cap gap index)))
                       (:instance lw-euler-window-modulated-request-positive (height (lw-euler-window-grid-height cap gap last)))
                       (:instance lw-euler-window-modulated-request-positive (height (lw-euler-window-grid-height cap gap 0))))
                 :do-not-induct t)))
  :rule-classes nil)
