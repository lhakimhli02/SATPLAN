;;; SMALL-2: 4 blocks, A on B on table, C on D on table → swap towers
(define (problem BLOCKS-S2)
  (:domain BLOCKS)
  (:objects A B C D)
  (:init (CLEAR A) (ON A B) (ONTABLE B)
         (CLEAR C) (ON C D) (ONTABLE D)
         (HANDEMPTY))
  (:goal (and (ON A C) (ON C D) (ON D B))))
