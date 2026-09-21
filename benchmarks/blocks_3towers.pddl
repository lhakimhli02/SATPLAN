;;; 3-TOWERS: 6 blocks start as three separate 2-block towers
;;; (A/B, C/D, E/F), goal rotates the tops across towers so you
;;; end up with three different 2-block towers (A/D, C/F, E/B).
(define (problem BLOCKS-3TOWERS)
  (:domain BLOCKS)
  (:objects A B C D E F)
  (:init (ON A B) (ONTABLE B) (CLEAR A)
         (ON C D) (ONTABLE D) (CLEAR C)
         (ON E F) (ONTABLE F) (CLEAR E)
         (HANDEMPTY))
  (:goal (and (ON A D) (ON C F) (ON E B))))
