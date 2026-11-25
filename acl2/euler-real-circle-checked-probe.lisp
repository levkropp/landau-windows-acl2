(in-package "ACL2")

(include-book "euler-real-circle-probe-geometry")
(include-book "euler-circle-interior-probe")

; Apply the probe geometry at a request chosen before extracting a
; witness. It also certifies an empty initial real-centered contour.

(local (defthm lw-ercp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ercp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ercp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ercp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ercp-times-negative (a b) (b a)))
                 :in-theory (disable lw-ercp-times-negative)))))

(local (defthm lw-ercp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ercp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ercp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ercp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ercp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ercp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ercp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ercp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ercp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ercp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ercp-left-commutes)))))

(local (deftheory lw-ercp-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ercp-left-commutes lw-ercp-left-distributes lw-ercp-fold-constants
              lw-ercp-times-negative lw-ercp-negative-times lw-ercp-zero-times
              lw-ercp-minus-one lw-ercp-double-negative lw-ercp-add-cancel lw-ercp-double lw-ercp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-euler-circle-interior-count-natural
  (natp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
  :hints (("Goal" :in-theory (union-theories '(lw-euler-circle-interior-count (:type-prescription len))
                                             (theory 'lw-ercp-arithmetic)))))

(defthm lw-euler-real-circle-checked-probe-geometry
  (implies (and (and (rationalp outer-radius) (< outer-radius 252)
                 (rationalp cap) (<= 0 cap) (< cap outer-radius)
                 (rationalp radius) (<= radius cap) (rationalp gap)
                 (< 0 gap) (<= gap 1/4)
                 (<= (* 8192 gap) (* (lw-euler-near-real-radius 252 outer-radius cap) (lw-euler-near-real-radius 252 outer-radius cap))))
                (lw-euler-circle-coverp (cons 252 0) radius plus-arcs minus-arcs) (< 0 (lw-euler-circle-interior-count (cons 252 0) radius plus-arcs minus-arcs))
                (rationalp tolerance) (< 0 tolerance) (<= tolerance (lw-euler-real-circle-probe-request outer-radius gap))
                (rationalp error) (< 0 error) (<= error tolerance))
           (let ((offset (lw-euler-circle-interior-probe-offset (cons 252 0) radius plus-arcs minus-arcs tolerance)))
             (and (lw-complex-diskp offset radius)
                  (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car offset)) (cdr offset) error) tolerance)
                  (< (lw-euler-near-real-radius 252 outer-radius cap) (abs (cdr offset)))
                  (< (- 251 gap) (- (car offset)))
                  (< (+ (- (car offset)) (* 8 gap)) radius)
                  (< (+ 251 (* 7 gap)) radius))))
  :hints (("Goal"
           :use (lw-euler-real-circle-probe-request-data
                 (:instance lw-euler-circle-interior-probe-small-value (center (cons 252 0)) (value-error error))
                 (:instance lw-complex-disk-data
                   (point (lw-euler-circle-interior-probe-offset (cons 252 0) radius plus-arcs minus-arcs tolerance)))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (+ 252 (car (lw-euler-circle-interior-probe-offset (cons 252 0) radius plus-arcs minus-arcs tolerance))) (cdr (lw-euler-circle-interior-probe-offset (cons 252 0) radius plus-arcs minus-arcs tolerance)) error))
                            (radius tolerance) (cap (lw-euler-real-circle-probe-request outer-radius gap)))
                 (:instance lw-euler-real-circle-small-probe-geometry (offset (lw-euler-circle-interior-probe-offset (cons 252 0) radius plus-arcs minus-arcs tolerance))))
           :in-theory (union-theories '(lw-complexp) (theory 'lw-ercp-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-real-circle-initial-count-empty
  (implies (and (and (rationalp outer-radius) (< outer-radius 252)
                 (rationalp cap) (<= 0 cap) (< cap outer-radius)
                 (rationalp radius) (<= radius cap) (rationalp gap)
                 (< 0 gap) (<= gap 1/4)
                 (<= (* 8192 gap) (* (lw-euler-near-real-radius 252 outer-radius cap) (lw-euler-near-real-radius 252 outer-radius cap))))
                (lw-euler-circle-coverp (cons 252 0) radius plus-arcs minus-arcs)
                (<= radius (+ 251 (* 7 gap))))
           (equal (lw-euler-circle-interior-count (cons 252 0) radius plus-arcs minus-arcs) 0))
  :hints (("Goal"
           :use (lw-euler-real-circle-probe-request-data
                 (:instance lw-euler-circle-interior-count-natural (center (cons 252 0)))
                 (:instance lw-euler-real-circle-checked-probe-geometry
                   (tolerance (lw-euler-real-circle-probe-request outer-radius gap)) (error (lw-euler-real-circle-probe-request outer-radius gap))))
           :in-theory (theory 'lw-ercp-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
