;;; Towers of Hanoi domain
;;; Discs sit on pegs or on top of larger discs.
;;; smaller(?d, ?x) is a static predicate encoding disc size order.
(define (domain hanoi)
  (:requirements :strips)
  (:predicates
    (on ?disc ?peg-or-disc)
    (clear ?peg-or-disc)
    (smaller ?disc ?peg-or-disc))

  (:action move
    :parameters (?disc ?from ?to)
    :precondition (and (clear ?disc) (on ?disc ?from)
                       (clear ?to) (smaller ?disc ?to))
    :effect (and (on ?disc ?to) (clear ?from)
                 (not (on ?disc ?from)) (not (clear ?to)))))
