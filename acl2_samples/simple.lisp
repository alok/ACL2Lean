(in-package "ACL2")

(defun len (x)
  (if (consp x)
      (+ 1 (len (cdr x)))
    0))

(defun append (x y)
  (if (consp x)
      (cons (car x) (append (cdr x) y))
    y))

(defthm len-append
  (equal (len (append x y))
         (+ (len x) (len y))))
