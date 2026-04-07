(define (problem elevators-strips-medium)
  (:domain elevators-strips)

  (:objects
    f0 f1 f2 f3 f4 f5 - floor
    e0 e1 - elevator
    p0 p1 p2 - passenger
  )

  (:init
    ; floor ordering
    (above f0 f1) (above f1 f2) (above f2 f3) (above f3 f4) (above f4 f5)

    ; elevators start at opposite ends of the building
    (lift-at e0 f0)
    (lift-at e1 f5)

    ; passengers scattered across middle floors
    (passenger-at p0 f1)
    (passenger-at p1 f3)
    (passenger-at p2 f4)
  )

  (:goal
    (and
      (passenger-at p0 f5)
      (passenger-at p1 f0)
      (passenger-at p2 f2)
    )
  )
)
