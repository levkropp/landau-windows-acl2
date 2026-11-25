; Part Three: isolated snapshots of the finite search and grid-witness books.
; Original definitions, theorem statements and proof hints are retained.
(in-package "ACL2")

(defun lw-intervalp (bounds)
  (and (consp bounds)
       (rationalp (car bounds))
       (rationalp (cdr bounds))
       (<= (car bounds) (cdr bounds))))

(defun lw-contains (bounds value)
  (and (lw-intervalp bounds)
       (rationalp value)
       (<= (car bounds) value)
       (<= value (cdr bounds))))

(defun lw-interval-add (left right)
  (cons (+ (car left) (car right))
        (+ (cdr left) (cdr right))))

(defun lw-interval-sub (left right)
  (cons (- (car left) (cdr right))
        (- (cdr left) (car right))))

(defun lw-interval-scale (coefficient bounds)
  (if (<= 0 coefficient)
      (cons (* coefficient (car bounds)) (* coefficient (cdr bounds)))
    (cons (* coefficient (cdr bounds)) (* coefficient (car bounds)))))

(defthm lw-contains-add
  (implies (and (lw-contains left left-value)
                (lw-contains right right-value))
           (lw-contains (lw-interval-add left right) (+ left-value right-value))))

(defthm lw-contains-sub
  (implies (and (lw-contains left left-value)
                (lw-contains right right-value))
           (lw-contains (lw-interval-sub left right) (- left-value right-value))))

(defthm lw-contains-scale
  (implies (and (rationalp coefficient) (lw-contains bounds value))
           (lw-contains (lw-interval-scale coefficient bounds) (* coefficient value)))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-lower-gt-of-margin
  (implies (and (lw-contains bounds value)
                (rationalp threshold)
                (rationalp error)
                (<= (- (cdr bounds) (car bounds)) error)
                (< (+ threshold error) value))
           (< threshold (car bounds))))

(defun lw-first-above (threshold samples)
  (if (endp samples)
      nil
    (if (< threshold (caar samples))
        (cons 0 (car samples))
      (let ((found (lw-first-above threshold (cdr samples))))
        (if found (cons (+ 1 (car found)) (cdr found)) nil)))))

(defun lw-some-lower-above (threshold samples)
  (if (endp samples)
      nil
    (or (< threshold (caar samples))
        (lw-some-lower-above threshold (cdr samples)))))

(defthm lw-first-above-complete
  (iff (lw-first-above threshold samples)
       (lw-some-lower-above threshold samples)))

(defthm lw-first-above-lower-gt
  (implies (lw-first-above threshold samples)
           (< threshold (cadr (lw-first-above threshold samples)))))

(defthm lw-first-above-index-natural
  (implies (lw-first-above threshold samples)
           (natp (car (lw-first-above threshold samples))))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-first-above-index-bound
  (implies (lw-first-above threshold samples)
           (< (car (lw-first-above threshold samples)) (len samples))))

(defthm lw-first-above-nth
  (implies (lw-first-above threshold samples)
           (equal (cdr (lw-first-above threshold samples))
                  (nth (car (lw-first-above threshold samples)) samples)))
  :hints (("Goal" :induct (lw-first-above threshold samples)
                  :in-theory (disable lw-first-above-complete))))

(defun lw-encloses-values (samples values)
  (if (endp samples)
      (endp values)
    (and (consp values)
         (lw-contains (car samples) (car values))
         (lw-encloses-values (cdr samples) (cdr values)))))

(defun lw-widths-at-most (error samples)
  (if (endp samples)
      t
    (and (<= (- (cdar samples) (caar samples)) error)
         (lw-widths-at-most error (cdr samples)))))

(defun lw-some-value-above (threshold values)
  (if (endp values)
      nil
    (or (< threshold (car values))
        (lw-some-value-above threshold (cdr values)))))

(defthm lw-first-above-value-gt
  (implies (and (rationalp threshold)
                (lw-encloses-values samples values)
                (lw-first-above threshold samples))
           (< threshold (nth (car (lw-first-above threshold samples)) values)))
  :hints (("Goal" :induct (lw-encloses-values samples values)
                  :in-theory (disable lw-first-above-complete))))

(defthm lw-search-complete-of-margin
  (implies (and (rationalp threshold)
                (rationalp error)
                (lw-encloses-values samples values)
                (lw-widths-at-most error samples)
                (lw-some-value-above (+ threshold error) values))
           (lw-first-above threshold samples)))

(assert-event (equal (lw-first-above 0 '((-1 . 0) (1/4 . 1/2)))
                     '(1 1/4 . 1/2)))

(assert-event (not (lw-first-above 0 '((-1 . 0) (-2 . -1)))))





(defun lw-last-address (addresses)
  (if (consp (cdr addresses))
      (lw-last-address (cdr addresses))
    (car addresses)))

(defun lw-meshp (addresses mesh)
  (and (consp addresses)
       (rationalp (car addresses))
       (if (consp (cdr addresses))
           (and (<= (car addresses) (cadr addresses))
                (<= (- (cadr addresses) (car addresses)) mesh)
                (lw-meshp (cdr addresses) mesh))
         (equal (cdr addresses) nil))))

(defun lw-some-nearby (point mesh addresses)
  (if (endp addresses)
      nil
    (or (<= (abs (- (car addresses) point)) mesh)
        (lw-some-nearby point mesh (cdr addresses)))))

(defthm lw-mesh-covers-point
  (implies (and (rationalp point)
                (rationalp mesh)
                (<= 0 mesh)
                (lw-meshp addresses mesh)
                (<= (car addresses) point)
                (<= point (lw-last-address addresses)))
           (lw-some-nearby point mesh addresses))
  :hints (("Goal" :induct (lw-meshp addresses mesh))))

(defun lw-lower-lipschitz (point peak lipschitz addresses values)
  (if (endp addresses)
      (endp values)
    (and (consp values)
         (rationalp (car addresses))
         (rationalp (car values))
         (<= (- peak (* lipschitz (abs (- (car addresses) point))))
             (car values))
         (lw-lower-lipschitz point peak lipschitz (cdr addresses) (cdr values)))))

(defthm lw-margin-survives-transport
  (implies (and (rationalp point)
                (rationalp address)
                (rationalp peak)
                (rationalp lipschitz)
                (rationalp mesh)
                (rationalp threshold)
                (rationalp error)
                (rationalp value)
                (<= 0 lipschitz)
                (<= (abs (- address point)) mesh)
                (< (+ threshold error (* lipschitz mesh)) peak)
                (<= (- peak (* lipschitz (abs (- address point)))) value))
           (< (+ threshold error) value))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm lw-nearby-forces-large-value
  (implies (and (rationalp point)
                (rationalp peak)
                (rationalp lipschitz)
                (rationalp mesh)
                (rationalp threshold)
                (rationalp error)
                (<= 0 lipschitz)
                (< (+ threshold error (* lipschitz mesh)) peak)
                (lw-some-nearby point mesh addresses)
                (lw-lower-lipschitz point peak lipschitz addresses values))
           (lw-some-value-above (+ threshold error) values))
  :hints (("Goal" :induct (lw-lower-lipschitz point peak lipschitz addresses values))
          (and stable-under-simplificationp
               '(:use ((:instance lw-margin-survives-transport
                                  (address (car addresses))
                                  (value (car values))))))))

(defthm lw-grid-search-complete
  (implies (and (rationalp point)
                (rationalp peak)
                (rationalp lipschitz)
                (rationalp mesh)
                (rationalp threshold)
                (rationalp error)
                (<= 0 lipschitz)
                (<= 0 mesh)
                (lw-meshp addresses mesh)
                (<= (car addresses) point)
                (<= point (lw-last-address addresses))
                (< (+ threshold error (* lipschitz mesh)) peak)
                (lw-lower-lipschitz point peak lipschitz addresses values)
                (lw-encloses-values samples values)
                (lw-widths-at-most error samples))
           (lw-first-above threshold samples))
  :hints (("Goal" :use (lw-mesh-covers-point
                        lw-nearby-forces-large-value
                        lw-search-complete-of-margin)
                  :in-theory (disable lw-meshp lw-some-nearby lw-lower-lipschitz
                                      lw-encloses-values lw-widths-at-most
                                      lw-some-value-above lw-first-above
                                      lw-first-above-complete))))

(assert-event
 (and (lw-meshp '(0 1 2) 1)
      (lw-lower-lipschitz 3/4 3 1 '(0 1 2) '(9/4 11/4 7/4))
      (lw-encloses-values '((2 . 5/2) (5/2 . 3) (3/2 . 2)) '(9/4 11/4 7/4))
      (lw-widths-at-most 1/2 '((2 . 5/2) (5/2 . 3) (3/2 . 2)))
      (equal (lw-first-above 1 '((2 . 5/2) (5/2 . 3) (3/2 . 2))) '(0 2 . 5/2))))

; A teaching constructor for a simple uniform grid; the project later uses
; a rounded rational window grid with its own endpoint and coverage proofs.
(defun video-uniform-grid (count start step)
  (if (zp count)
      nil
    (cons start
          (video-uniform-grid (1- count) (+ start step) step))))

(defthm video-uniform-grid-length
  (implies (natp count)
           (equal (len (video-uniform-grid count start step)) count)))

(defthm video-uniform-grid-first
  (implies (consp (video-uniform-grid count start step))
           (equal (car (video-uniform-grid count start step)) start)))

(defthm video-uniform-grid-is-mesh
  (implies (and (posp count) (rationalp start)
                (rationalp step) (<= 0 step))
           (lw-meshp (video-uniform-grid count start step) step))
  :hints (("Goal" :induct (video-uniform-grid count start step))))

(assert-event
 (equal (video-uniform-grid 9 0 1/8)
        '(0 1/8 1/4 3/8 1/2 5/8 3/4 7/8 1)))

(assert-event
 (equal (lw-first-above 0 '((-7/8 . -5/8) (-3/8 . -1/8)
                           (1/8 . 3/8) (5/8 . 7/8)))
        '(2 1/8 . 3/8)))
(assert-event (equal (nth 2 (video-uniform-grid 9 0 1/8)) 1/4))
(assert-event (not (lw-first-above 0 '((-7/8 . -5/8) (-11/8 . -9/8)))))
(assert-event (not (lw-first-above 0 '((-1/8 . 3/8)))))
(assert-event (lw-contains '(-1/8 . 3/8) 1/8))
(assert-event
 (let ((addresses '(0 1/8 1/4 3/8 1/2 5/8 3/4 7/8 1))
       (values '(-3/4 -1/4 1/4 3/4 3/4 1/4 -1/4 -3/4 -5/4))
       (samples '((-7/8 . -5/8) (-3/8 . -1/8) (1/8 . 3/8)
                  (5/8 . 7/8) (5/8 . 7/8) (1/8 . 3/8)
                  (-3/8 . -1/8) (-7/8 . -5/8) (-11/8 . -9/8))))
   (and (lw-meshp addresses 1/8)
        (equal (lw-last-address addresses) 1)
        (lw-some-nearby 7/16 1/8 addresses)
        (< (+ 0 1/4 (* 4 1/8)) 1)
        (lw-lower-lipschitz 7/16 1 4 addresses values)
        (lw-encloses-values samples values)
        (lw-widths-at-most 1/4 samples)
        (equal (lw-first-above 0 samples) '(2 1/8 . 3/8)))))

; Independently check each displayed value of 1 - 4*abs(x - 7/16).
(assert-event
 (equal (list (- 1 (* 4 (abs (- 0 7/16))))
              (- 1 (* 4 (abs (- 1/8 7/16))))
              (- 1 (* 4 (abs (- 1/4 7/16))))
              (- 1 (* 4 (abs (- 3/8 7/16))))
              (- 1 (* 4 (abs (- 1/2 7/16))))
              (- 1 (* 4 (abs (- 5/8 7/16))))
              (- 1 (* 4 (abs (- 3/4 7/16))))
              (- 1 (* 4 (abs (- 7/8 7/16))))
              (- 1 (* 4 (abs (- 1 7/16)))))
        '(-3/4 -1/4 1/4 3/4 3/4 1/4 -1/4 -3/4 -5/4)))
