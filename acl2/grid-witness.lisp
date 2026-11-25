(in-package "ACL2")

(include-book "interval-search")

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
