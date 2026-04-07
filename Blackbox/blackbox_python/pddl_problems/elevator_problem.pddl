(define (problem elevators-strips-small)
  (:domain elevators-strips)

  (:objects
    f0 f1 f2 f3 - floor
    e0 - elevator
    p0 p1 - passenger
  )

  (:init
    ; floor ordering
    (above f0 f1) (above f1 f2) (above f2 f3)

    ; elevator starts at f0
    (lift-at e0 f0)

    ; passengers
    (passenger-at p0 f0)
    (passenger-at p1 f2)
  )

  (:goal
    (and
      (passenger-at p0 f3)
      (passenger-at p1 f1)
    )
  )
)
