;;; XL-1: Ferry, 8 cars all crossing from left to right
;;; Ferry holds 1 car. Optimal plan: 7×(board,sail,debark,sail-back) + board,sail,debark = 31 steps
;;; Inherently sequential — empty-ferry is a single shared resource.
(define (problem ferry-8cars)
  (:domain ferry)
  (:objects left right c1 c2 c3 c4 c5 c6 c7 c8)
  (:init
    (at-ferry left) (empty)
    (at c1 left) (at c2 left) (at c3 left) (at c4 left)
    (at c5 left) (at c6 left) (at c7 left) (at c8 left))
  (:goal
    (and
      (at c1 right) (at c2 right) (at c3 right) (at c4 right)
      (at c5 right) (at c6 right) (at c7 right) (at c8 right))))
