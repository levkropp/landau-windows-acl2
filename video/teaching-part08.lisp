; Part Eight: illustrative finite geometry and pole coefficients.
(in-package "ACL2")
(include-book "../acl2/box-circles")
(include-book "../acl2/mellin-window-budget")

(defun video-eight-geometric-prefix (ratio count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ 1 (* ratio (video-eight-geometric-prefix ratio (- count 1))))))

(defun video-eight-toy-coefficient (index)
  (lw-complex-add (lw-pole-coefficient '(1 . 0) '(2 . 0) index)
                  (lw-pole-coefficient '(-3 . 0) '(3 . 0) index)))

(defthm video-eight-geometric-example
  (and (equal (video-eight-geometric-prefix 1/2 3) 7/4)
       (equal (+ (video-eight-geometric-prefix 1/2 3) 1/4) 2))
  :rule-classes nil)

(defthm video-eight-complex-reciprocal
  (equal (lw-complex-reciprocal '(2 . 1)) '(2/5 . -1/5))
  :rule-classes nil)

(defthm video-eight-pole-coefficients
  (and (equal (lw-pole-coefficient '(1 . 0) '(2 . 0) 0) '(1/2 . 0))
       (equal (lw-pole-coefficient '(1 . 0) '(2 . 0) 1) '(1/4 . 0))
       (equal (lw-pole-coefficient '(1 . 0) '(2 . 0) 5) '(1/64 . 0)))
  :rule-classes nil)

(defthm video-eight-tie-heights
  (and (equal (lw-tie-height 2 '(1 . 1) '(1 . -1)) 0)
       (equal (lw-tie-height 2 '(1 . 1) '(0 . 0)) -1)
       (equal (lw-tie-height 2 '(1 . -1) '(0 . 0)) 1))
  :rule-classes nil)

(defthm video-eight-avoiding-heights
  (and (equal (lw-avoid-height-interval -1 1 '(-1 0 1)) '(1/2 . 3/4))
       (equal (lw-chosen-height -1 1 '(-1 0 1)) 5/8))
  :rule-classes nil)

(defthm video-eight-nearest-point
  (and (equal (lw-distance-squared 2 5/8 '(1 . 1)) 73/64)
       (equal (lw-distance-squared 2 5/8 '(1 . -1)) 233/64)
       (equal (lw-distance-squared 2 5/8 '(0 . 0)) 281/64)
       (equal (lw-nearest-point 2 5/8 '((1 . 1) (1 . -1) (0 . 0))) '(1 . 1)))
  :rule-classes nil)

(defthm video-eight-isolation
  (and (equal (lw-other-points '(1 . 1) '((1 . 1) (1 . 1) (1 . -1) (0 . 0)))
              '((1 . -1) (0 . 0)))
       (equal (lw-isolating-radius-squared 2 5/8 '(1 . 1)
                '((1 . 1) (1 . -1) (0 . 0)) 4) 153/64)
       (< 73/64 153/64) (< 153/64 233/64))
  :rule-classes nil)

(defthm video-eight-box-distances
  (and (equal (lw-square-interval '(-2 . 3)) '(0 . 9))
       (equal (lw-distance-box 2 1 '(59/100 61/100 99/100 101/100))
              '(19321/10000 . 9941/5000))
       (equal (lw-distance-box 2 1 '(59/100 61/100 -101/100 -99/100))
              '(29461/5000 . 30141/5000))
       (< 9941/5000 2) (< 5 29461/5000))
  :rule-classes nil)

(defthm video-eight-box-circle
  (and (lw-circle-check 2 1 3 '(59/100 61/100 99/100 101/100)
                         '((59/100 61/100 -101/100 -99/100)))
       (not (lw-circle-check 2 1 2 '(0 1 0 1) '((0 1 0 1)))))
  :rule-classes nil)

(defthm video-eight-residue-example
  (and (equal (lw-zeta-residue-denominator '(1/2 . 1)) '(-5/4 . 0))
       (equal (lw-zeta-pole-residue '(1/2 . 1) 1) '(4/5 . 0))
       (equal (lw-zeta-pole-residue '(1/2 . 1) 2) '(8/5 . 0)))
  :rule-classes nil)

(defthm video-eight-relative-dominance
  (and (equal (video-eight-toy-coefficient 0) '(-1/2 . 0))
       (equal (video-eight-toy-coefficient 5) '(179/15552 . 0))
       (equal (* 64 179/15552) 179/243)
       (< (* 3 (lw-rational-power 2/3 6)) 1/2)
       (< 1/128 179/15552))
  :rule-classes nil)

(defthm video-eight-separated-bounds
  (implies (and (rationalp pole) (rationalp remainder) (rationalp upper)
                (< (+ remainder upper) pole))
           (not (and (rationalp value) (<= (- pole remainder) value)
                     (<= value upper))))
  :rule-classes nil)
