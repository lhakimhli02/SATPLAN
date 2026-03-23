(define (problem library-reorder)
  (:domain library)
  (:objects
    s1 s2 s3 - shelf
    a b c - book
  )
  (:init
    ;; person start location
    (personat s1)
    ;; initial book locations
    (bookat a s3)
    (bookat b s2)
    (bookat c s1)
    ;; hand state
    (handempty)
    ;; adjacency
    (adj s1 s2)
    (adj s2 s1)
    (adj s2 s3)
    (adj s3 s2)
  )
  (:goal
    (and
      (bookat a s1)
      (bookat b s2)
      (bookat c s3)
    )
  )
)