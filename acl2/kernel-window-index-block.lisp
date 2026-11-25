(in-package "ACL2")

(include-book "kernel-window")

(defun lw-kernel-window-block-threshold (minimum-index width)
  (lw-eventual-window-threshold
   (max 64 (max (lw-geometric-index 5000/4977 128)
                (max (nfix minimum-index) (nfix width))))))

(local
 (defthm lw-window-index-block-upper
   (implies (and (rationalp lower) (natp width)
                 (<= (+ 1 width) lower)
                 (<= index (+ (lw-window-index-from-log lower) width)))
            (<= index (* 625/2 lower)))
   :hints (("Goal"
            :use ((:instance lw-ceiling-rational-bracket (value (* 615/2 lower))))
            :in-theory
            (union-theories '(lw-window-index-from-log natp commutativity-of-+ associativity-of-+)
                            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-window-block-power-two-strict
   (implies (natp exponent)
            (< 1 (lw-rational-power 2 (+ 1 exponent))))
   :hints (("Goal"
            :expand ((lw-rational-power 2 (+ 1 exponent)))
            :use ((:instance lw-rational-power-at-least-one (base 2)))
            :in-theory
            (union-theories '(natp zp fix fold-consts-in-+ unicity-of-0 commutativity-of-+ associativity-of-+
                              (:executable-counterpart binary-+)
                              (:executable-counterpart binary-*))
                            (theory 'minimal-theory))))
   :rule-classes nil))

; The bounded shift fits in the unused upper margin of the kernel band.
; All indices in the block use the same window endpoints.
(defthm lw-kernel-window-index-block-data
  (implies (and (rationalp start) (natp minimum-index) (natp width)
                (<= (lw-kernel-window-block-threshold minimum-index width) start)
                (natp index)
                (<= (lw-window-index start) index)
                (<= index (+ (lw-window-index start) width)))
           (let* ((bounds (lw-log-bounds start 1/1000))
                  (lower (car bounds))
                  (upper (cdr bounds)))
             (and (< 1 start)
                  (rationalp lower) (rationalp upper) (<= lower upper)
                  (<= 64 lower)
                  (<= minimum-index index)
                  (<= (lw-geometric-index 5000/4977 128) index)
                  (<= (* 6061/20 upper) index)
                  (<= index (* 625/2 lower)))))
  :hints (("Goal"
           :use ((:instance lw-eventual-kernel-window-data
                    (target (max 64 (max (lw-geometric-index 5000/4977 128)
                                         (max minimum-index width)))))
                 (:instance lw-log-bounds-dyadic-growth
                    (value start) (epsilon 1/1000)
                    (steps (+ (* 2 (max 64 (max (lw-geometric-index 5000/4977 128)
                                                  (max minimum-index width)))) 8)))
                 (:instance lw-window-index-block-upper
                    (lower (car (lw-log-bounds start 1/1000))))
                 (:instance lw-window-block-power-two-strict
                    (exponent (+ (* 2 (max 64 (max (lw-geometric-index 5000/4977 128)
                                                     (max minimum-index width)))) 8))))
           :in-theory
           (union-theories
            '(lw-kernel-window-block-threshold lw-eventual-window-threshold
              lw-window-index max natp nfix lw-geometric-index-natural
              fold-consts-in-+ associativity-of-+ commutativity-of-+ commutativity-2-of-+
              associativity-of-* commutativity-of-* distributivity
              (:executable-counterpart binary-+) (:executable-counterpart binary-*))
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
