;;; MEDIUM-2: 5 blocks in two towers → merge into one
;;; Init: A on B on table, C on D on E on table
;;; Goal: A on B on C on D on E
(define (problem BLOCKS-M2)
  (:domain BLOCKS)
  (:objects A B C D E)
  (:init (CLEAR A) (ON A B) (ONTABLE B)
         (CLEAR C) (ON C D) (ON D E) (ONTABLE E)
         (HANDEMPTY))
  (:goal (and (ON A B) (ON B C) (ON C D) (ON D E))))
