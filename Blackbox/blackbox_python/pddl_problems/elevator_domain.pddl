(define (domain elevators-strips)
  (:requirements :typing)
  (:types elevator passenger floor)

  (:predicates
    (lift-at ?lift - elevator ?f - floor)
    (passenger-at ?p - passenger ?f - floor)
    (boarded ?p - passenger ?lift - elevator)
    (above ?f1 - floor ?f2 - floor)
  )

  (:action move-up
    :parameters (?lift - elevator ?f1 - floor ?f2 - floor)
    :precondition (and (lift-at ?lift ?f1) (above ?f1 ?f2))
    :effect (and (lift-at ?lift ?f2) (not (lift-at ?lift ?f1)))
  )

  (:action move-down
    :parameters (?lift - elevator ?f1 - floor ?f2 - floor)
    :precondition (and (lift-at ?lift ?f1) (above ?f2 ?f1))
    :effect (and (lift-at ?lift ?f2) (not (lift-at ?lift ?f1)))
  )

  (:action board
    :parameters (?p - passenger ?lift - elevator ?f - floor)
    :precondition (and (lift-at ?lift ?f) (passenger-at ?p ?f))
    :effect (and (boarded ?p ?lift) (not (passenger-at ?p ?f)))
  )

  (:action leave
    :parameters (?p - passenger ?lift - elevator ?f - floor)
    :precondition (and (lift-at ?lift ?f) (boarded ?p ?lift))
    :effect (and (passenger-at ?p ?f) (not (boarded ?p ?lift)))
  )
)
