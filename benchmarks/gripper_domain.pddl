;;; Gripper domain: robot with two grippers moves balls between rooms
(define (domain gripper-strips)
  (:requirements :strips)
  (:predicates
    (room ?r)
    (ball ?b)
    (gripper ?g)
    (at-robby ?r)
    (at ?b ?r)
    (free ?g)
    (carry ?b ?g))

  (:action move
    :parameters (?from ?to)
    :precondition (and (room ?from) (room ?to) (at-robby ?from))
    :effect (and (at-robby ?to) (not (at-robby ?from))))

  (:action pick
    :parameters (?ball ?room ?gripper)
    :precondition (and (ball ?ball) (room ?room) (gripper ?gripper)
                       (at ?ball ?room) (at-robby ?room) (free ?gripper))
    :effect (and (carry ?ball ?gripper)
                 (not (at ?ball ?room))
                 (not (free ?gripper))))

  (:action drop
    :parameters (?ball ?room ?gripper)
    :precondition (and (ball ?ball) (room ?room) (gripper ?gripper)
                       (carry ?ball ?gripper) (at-robby ?room))
    :effect (and (at ?ball ?room)
                 (free ?gripper)
                 (not (carry ?ball ?gripper)))))
