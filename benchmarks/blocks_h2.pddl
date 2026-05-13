;;; HARD-2: 6 blocks in reverse tower, reverse it
;;; Init: A on B on C on D on E on F (A on top), all on table chain
;;; Goal: F on E on D on C on B on A (F on top) — reverse the tower
(define (problem BLOCKS-H2)
  (:domain BLOCKS)
  (:objects A B C D E F)
  (:init (CLEAR A) (ON A B) (ON B C) (ON C D) (ON D E) (ON E F) (ONTABLE F)
         (HANDEMPTY))
  (:goal (and (ON B A) (ON C B) (ON D C) (ON E D) (ON F E))))
