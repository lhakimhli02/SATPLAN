;;; Ferry domain: transport cars one at a time across a body of water
(define (domain ferry)
  (:requirements :strips)
  (:predicates
    (at-ferry ?loc)
    (at ?car ?loc)
    (on ?car)
    (empty))

  (:action sail
    :parameters (?from ?to)
    :precondition (at-ferry ?from)
    :effect (and (at-ferry ?to) (not (at-ferry ?from))))

  (:action board
    :parameters (?car ?loc)
    :precondition (and (at ?car ?loc) (at-ferry ?loc) (empty))
    :effect (and (on ?car) (not (at ?car ?loc)) (not (empty))))

  (:action debark
    :parameters (?car ?loc)
    :precondition (and (on ?car) (at-ferry ?loc))
    :effect (and (at ?car ?loc) (empty) (not (on ?car)))))
