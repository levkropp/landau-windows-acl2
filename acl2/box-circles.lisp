(in-package "ACL2")

(include-book "pole-geometry")

(defthm lw-contains-point
  (implies (rationalp value) (lw-contains (cons value value) value)))

(defun lw-square-interval (bounds)
  (let ((left (* (car bounds) (car bounds)))
        (right (* (cdr bounds) (cdr bounds))))
    (cons (if (and (<= (car bounds) 0) (<= 0 (cdr bounds))) 0 (min left right))
          (max left right))))

(defthm lw-square-interval-sound
  (implies (lw-contains bounds value)
           (lw-contains (lw-square-interval bounds) (* value value)))
  :hints (("Goal" :cases ((<= 0 value)) :nonlinearp t)))

(defun lw-boxp (box)
  (and (consp box)
       (consp (cdr box))
       (consp (cddr box))
       (consp (cdddr box))
       (equal (cddddr box) nil)
       (lw-intervalp (cons (car box) (cadr box)))
       (lw-intervalp (cons (caddr box) (cadddr box)))))

(defun lw-box-contains (box point)
  (and (lw-boxp box)
       (lw-plane-pointp point)
       (lw-contains (cons (car box) (cadr box)) (car point))
       (lw-contains (cons (caddr box) (cadddr box)) (cdr point))))

(defun lw-distance-box (sigma height box)
  (lw-interval-add
   (lw-square-interval (lw-interval-sub (cons sigma sigma) (cons (car box) (cadr box))))
   (lw-square-interval (lw-interval-sub (cons height height) (cons (caddr box) (cadddr box))))))

(defthm lw-distance-box-sound
  (implies (and (rationalp sigma) (rationalp height) (lw-box-contains box point))
           (lw-contains (lw-distance-box sigma height box)
                        (lw-distance-squared sigma height point)))
  :hints (("Goal" :use ((:instance lw-contains-sub
                                   (left (cons sigma sigma))
                                   (right (cons (car box) (cadr box)))
                                   (left-value sigma) (right-value (car point)))
                        (:instance lw-contains-sub
                                   (left (cons height height))
                                   (right (cons (caddr box) (cadddr box)))
                                   (left-value height) (right-value (cdr point)))
                        (:instance lw-square-interval-sound
                                   (bounds (lw-interval-sub (cons sigma sigma)
                                                            (cons (car box) (cadr box))))
                                   (value (- sigma (car point))))
                        (:instance lw-square-interval-sound
                                   (bounds (lw-interval-sub (cons height height)
                                                            (cons (caddr box) (cadddr box))))
                                   (value (- height (cdr point))))
                        (:instance lw-contains-add
                                   (left (lw-square-interval
                                          (lw-interval-sub (cons sigma sigma)
                                                           (cons (car box) (cadr box)))))
                                   (right (lw-square-interval
                                           (lw-interval-sub (cons height height)
                                                            (cons (caddr box) (cadddr box)))))
                                   (left-value (* (- sigma (car point)) (- sigma (car point))))
                                   (right-value (* (- height (cdr point)) (- height (cdr point))))))
                  :in-theory (disable lw-interval-add lw-interval-sub lw-square-interval
                                      lw-contains lw-contains-add lw-contains-sub
                                      lw-square-interval-sound distributivity))))

(defun lw-boxes-outside-circle (sigma height radius boxes)
  (if (endp boxes)
      t
    (and (lw-boxp (car boxes))
         (< radius (car (lw-distance-box sigma height (car boxes))))
         (lw-boxes-outside-circle sigma height radius (cdr boxes)))))

(defun lw-point-in-boxes (point boxes)
  (if (endp boxes)
      nil
    (or (lw-box-contains (car boxes) point)
        (lw-point-in-boxes point (cdr boxes)))))

(defun lw-circle-check (sigma height radius selected others)
  (and (rationalp sigma)
       (rationalp height)
       (rationalp radius)
       (< 0 radius)
       (lw-boxp selected)
       (< (cdr (lw-distance-box sigma height selected)) radius)
       (lw-boxes-outside-circle sigma height radius others)))

(defthm lw-circle-check-contains-selected
  (implies (and (lw-circle-check sigma height radius selected others)
                (lw-box-contains selected point))
           (< (lw-distance-squared sigma height point) radius))
  :hints (("Goal" :use ((:instance lw-distance-box-sound (box selected)))
                  :in-theory (disable lw-distance-box-sound lw-distance-box lw-distance-squared
                                      lw-box-contains lw-boxp lw-boxes-outside-circle))))

(defthm lw-boxes-outside-circle-sound
  (implies (and (rationalp sigma)
                (rationalp height)
                (rationalp radius)
                (lw-boxes-outside-circle sigma height radius boxes)
                (lw-point-in-boxes point boxes))
           (< radius (lw-distance-squared sigma height point)))
  :hints (("Goal" :induct (lw-boxes-outside-circle sigma height radius boxes)
                  :in-theory (disable lw-box-contains lw-boxp lw-distance-box lw-distance-squared))
          (and stable-under-simplificationp
               '(:use ((:instance lw-distance-box-sound (box (car boxes))))
                 :in-theory (disable lw-distance-box-sound lw-distance-box lw-distance-squared
                                     lw-box-contains lw-boxp)))))

(defthm lw-circle-check-excludes-others
  (implies (and (lw-circle-check sigma height radius selected others)
                (lw-point-in-boxes point others))
           (< radius (lw-distance-squared sigma height point)))
  :hints (("Goal" :in-theory (disable lw-point-in-boxes lw-boxes-outside-circle
                                      lw-distance-squared lw-distance-box lw-boxp))))

(assert-event
 (and (lw-contains (lw-square-interval '(-2 . 3)) 0)
      (lw-contains (lw-square-interval '(-2 . 3)) 9)
      (lw-circle-check 2 1 3 '(59/100 61/100 99/100 101/100)
                       '((59/100 61/100 -101/100 -99/100)))
      (not (lw-circle-check 2 1 2 '(0 1 0 1) '((0 1 0 1))))))
