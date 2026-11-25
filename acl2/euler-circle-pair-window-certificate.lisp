(in-package "ACL2")

(include-book "euler-circle-window-budget")
(include-book "euler-circle-real-native-bound")

(defun lw-euler-circle-pair-window-threshold (center radius plus-arcs minus-arcs ceiling numerator denominator real-circle-radius real-radius real-plus-arcs real-minus-arcs)
  (lw-euler-circle-computed-window-threshold center radius plus-arcs minus-arcs
    ceiling numerator denominator real-radius (lw-euler-circle-real-normalized-cap 252 real-circle-radius real-radius real-plus-arcs real-minus-arcs)))

(local (defthm lw-ecpw-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecpw-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecpw-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecpw-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecpw-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecpw-times-negative)))))

(local (defthm lw-ecpw-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecpw-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecpw-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecpw-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecpw-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecpw-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecpw-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecpw-right-one (equal (* value 1) (fix value))))

(local
 (defthm lw-ecpw-inverse-unique
   (implies (and (rationalp scale) (rationalp bound) (< 0 scale)
                 (equal (* scale bound) 1))
            (equal bound (/ scale)))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x scale))
                  (:instance associativity-of-* (x (/ scale)) (y scale) (z bound))
                  (:instance commutativity-of-* (x (/ scale)) (y scale)))
            :in-theory (disable inverse-of-* associativity-of-*
                                commutativity-of-* lw-ecpw-left-commutes
                                lw-ecpw-left-distributes distributivity)))
   :rule-classes nil))

(local
 (defthm lw-ecpw-reciprocal-power
   (implies (and (rationalp radius) (< 0 radius) (natp index))
            (equal (lw-rational-power (/ radius) index)
                   (/ (lw-rational-power radius index))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-reciprocal-pair (value radius))
                  (:instance lw-rational-power-positive (base radius) (exponent index))
                  (:instance lw-ecpw-inverse-unique
                    (scale (lw-rational-power radius index))
                    (bound (lw-rational-power (/ radius) index))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power-rational lw-reciprocal-positive
              lw-ecpw-left-commutes lw-ecpw-left-distributes lw-ecpw-fold-constants
              lw-ecpw-times-negative lw-ecpw-negative-times lw-ecpw-zero-times
              lw-ecpw-minus-one lw-ecpw-double-negative lw-ecpw-add-cancel lw-ecpw-double lw-ecpw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))


(local
 (defthm lw-ecpw-pair-real-check
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                (lw-euler-circle-coverp (cons 252 0) real-circle-radius real-plus-arcs real-minus-arcs)
                (lw-euler-value-clearance-check 252 0 real-anchor-error)
                (equal (lw-euler-circle-interior-count (cons 252 0) real-circle-radius real-plus-arcs real-minus-arcs) 0)
                (rationalp real-radius) (< 251 real-radius) (< real-radius real-circle-radius)
                (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) real-radius)
                (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- 252 (/ numerator denominator)))
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
            (lw-euler-window-real-coefficient-check real-radius (lw-euler-circle-real-normalized-cap 252 real-circle-radius real-radius real-plus-arcs real-minus-arcs) (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
   :hints (("Goal"
            :use (lw-euler-circle-window-budget-request-data
                  (:instance lw-euler-circle-window-coefficient-index-data (request (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))
                  (:instance lw-euler-circle-joint-request-adequate (target 0) (request (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))
                  (:instance lw-euler-circle-real-native-negative-part-bound
                    (rate 252) (radius real-circle-radius) (inner real-radius)
                    (plus-arcs real-plus-arcs) (minus-arcs real-minus-arcs) (anchor-error real-anchor-error)
                    (index (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))) (coefficient-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
                  (:instance lw-ecpw-reciprocal-power (radius real-radius) (index (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
                  (:instance lw-euler-circle-real-native-negative-part-bound
                    (rate 252) (radius real-circle-radius) (inner real-radius)
                    (plus-arcs real-plus-arcs) (minus-arcs real-minus-arcs) (anchor-error real-anchor-error)
                    (index (+ 1 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))) (coefficient-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
                  (:instance lw-ecpw-reciprocal-power (radius real-radius) (index (+ 1 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))))
                  (:instance lw-euler-circle-real-native-negative-part-bound
                    (rate 252) (radius real-circle-radius) (inner real-radius)
                    (plus-arcs real-plus-arcs) (minus-arcs real-minus-arcs) (anchor-error real-anchor-error)
                    (index (+ 2 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))) (coefficient-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
                  (:instance lw-ecpw-reciprocal-power (radius real-radius) (index (+ 2 (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-window-real-coefficient-check
              lw-ecpw-left-commutes lw-ecpw-left-distributes lw-ecpw-fold-constants
              lw-ecpw-times-negative lw-ecpw-negative-times lw-ecpw-zero-times
              lw-ecpw-minus-one lw-ecpw-double-negative lw-ecpw-add-cancel lw-ecpw-double lw-ecpw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; The modulated circle has positive count. The real circle has count
; zero and admits a larger normalization radius still inside its contour.
(defthm lw-euler-circle-pair-window-certificate
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                (lw-euler-circle-coverp (cons 252 0) real-circle-radius real-plus-arcs real-minus-arcs)
                (lw-euler-value-clearance-check 252 0 real-anchor-error)
                (equal (lw-euler-circle-interior-count (cons 252 0) real-circle-radius real-plus-arcs real-minus-arcs) 0)
                (rationalp real-radius) (< 251 real-radius) (< real-radius real-circle-radius)
                (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) real-radius)
                (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- 252 (/ numerator denominator)))
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (<= (lw-euler-circle-pair-window-threshold center radius plus-arcs minus-arcs ceiling numerator denominator real-circle-radius real-radius real-plus-arcs real-minus-arcs) start))
           (let* ((found (lw-landau-window-search start ceiling numerator denominator))
                  (address (lw-landau-window-address start ceiling found)))
             (and found (rationalp address)
                  (<= start address)
                  (<= (* address address) (* start start start))
                  (< 0 (cadr found))
                  (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal"
           :use (lw-ecpw-pair-real-check
                 (:instance lw-euler-circle-real-native-cap-data
                   (rate 252) (radius real-circle-radius) (inner real-radius)
                   (plus-arcs real-plus-arcs) (minus-arcs real-minus-arcs) (anchor-error real-anchor-error))
                 (:instance lw-euler-circle-computed-window-certificate (real-mass (lw-euler-circle-real-normalized-cap 252 real-circle-radius real-radius real-plus-arcs real-minus-arcs))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-pair-window-threshold
              lw-ecpw-left-commutes lw-ecpw-left-distributes lw-ecpw-fold-constants
              lw-ecpw-times-negative lw-ecpw-negative-times lw-ecpw-zero-times
              lw-ecpw-minus-one lw-ecpw-double-negative lw-ecpw-add-cancel lw-ecpw-double lw-ecpw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
