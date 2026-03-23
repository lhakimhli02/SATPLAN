(define (domain library)
  (:requirements :strips :typing)
  
  (:types
    shelf book
  )
  (:predicates
    (personat ?s - shelf)
    (bookat ?b - book ?s - shelf)
    (holding ?b - book)
    (handempty)
    (adj ?from - shelf ?to - shelf)
  )
  (:action move
    :parameters (?from - shelf ?to - shelf)
    :precondition (and
      (personat ?from)
      (adj ?from ?to)
    )
    :effect (and
      (not (personat ?from))
      (personat ?to)
    )
  )
  (:action pickup
    :parameters (?b - book ?s - shelf)
    :precondition (and
      (personat ?s)
      (bookat ?b ?s)
      (handempty)
    )
    :effect (and
      (holding ?b)
      (not (bookat ?b ?s))
      (not (handempty))
    )
  )
  (:action shelve
    :parameters (?b - book ?s - shelf)
    :precondition (and
      (personat ?s)
      (holding ?b)
    )
    :effect (and
      (bookat ?b ?s)
      (handempty)
      (not (holding ?b))
    )
  )
)