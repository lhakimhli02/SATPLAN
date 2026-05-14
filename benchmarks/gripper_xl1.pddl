;;; XL-1: Gripper, 16 balls, move all from rooma to roomb
;;; Optimal parallel plan: 31 steps (8 trips × 4 steps, last trip 3 steps)
;;; Each trip: [pick b2k-1 lg, pick b2k rg] → move → [drop b2k-1, drop b2k] → move back
(define (problem gripper-xl1)
  (:domain gripper-strips)
  (:objects
    rooma roomb
    ball1 ball2 ball3 ball4 ball5 ball6 ball7 ball8
    ball9 ball10 ball11 ball12 ball13 ball14 ball15 ball16
    lgripper rgripper)
  (:init
    (room rooma) (room roomb)
    (ball ball1) (ball ball2) (ball ball3) (ball ball4)
    (ball ball5) (ball ball6) (ball ball7) (ball ball8)
    (ball ball9) (ball ball10) (ball ball11) (ball ball12)
    (ball ball13) (ball ball14) (ball ball15) (ball ball16)
    (gripper lgripper) (gripper rgripper)
    (at-robby rooma)
    (free lgripper) (free rgripper)
    (at ball1 rooma) (at ball2 rooma) (at ball3 rooma) (at ball4 rooma)
    (at ball5 rooma) (at ball6 rooma) (at ball7 rooma) (at ball8 rooma)
    (at ball9 rooma) (at ball10 rooma) (at ball11 rooma) (at ball12 rooma)
    (at ball13 rooma) (at ball14 rooma) (at ball15 rooma) (at ball16 rooma))
  (:goal
    (and
      (at ball1 roomb) (at ball2 roomb) (at ball3 roomb) (at ball4 roomb)
      (at ball5 roomb) (at ball6 roomb) (at ball7 roomb) (at ball8 roomb)
      (at ball9 roomb) (at ball10 roomb) (at ball11 roomb) (at ball12 roomb)
      (at ball13 roomb) (at ball14 roomb) (at ball15 roomb) (at ball16 roomb))))
