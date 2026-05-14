;;; Depot domain — untyped STRIPS version
;;; Types are encoded as unary predicates in :init (place, truck, hoist, etc.)
(define (domain Depot)
  (:requirements :strips)
  (:predicates
    (place ?p)
    (locatable ?x)
    (depot ?d)
    (distributor ?d)
    (truck ?t)
    (hoist ?h)
    (surface ?s)
    (pallet ?p)
    (crate ?c)
    (at ?x ?p)
    (on ?x ?y)
    (in ?c ?t)
    (clear ?s)
    (available ?h)
    (lifting ?h ?c))

  (:action drive
    :parameters (?t ?from ?to)
    :precondition (and (truck ?t) (place ?from) (place ?to) (at ?t ?from))
    :effect (and (at ?t ?to) (not (at ?t ?from))))

  (:action lift
    :parameters (?h ?c ?s ?p)
    :precondition (and (hoist ?h) (crate ?c) (surface ?s) (place ?p)
                       (at ?h ?p) (available ?h) (at ?c ?p)
                       (on ?c ?s) (clear ?c))
    :effect (and (lifting ?h ?c) (clear ?s)
                 (not (available ?h)) (not (at ?c ?p))
                 (not (clear ?c)) (not (on ?c ?s))))

  (:action drop
    :parameters (?h ?c ?s ?p)
    :precondition (and (hoist ?h) (crate ?c) (surface ?s) (place ?p)
                       (at ?h ?p) (lifting ?h ?c) (at ?s ?p) (clear ?s))
    :effect (and (available ?h) (at ?c ?p) (on ?c ?s) (clear ?c)
                 (not (lifting ?h ?c)) (not (clear ?s))))

  (:action load
    :parameters (?h ?c ?t ?p)
    :precondition (and (hoist ?h) (crate ?c) (truck ?t) (place ?p)
                       (at ?h ?p) (at ?t ?p) (lifting ?h ?c))
    :effect (and (in ?c ?t) (available ?h) (not (lifting ?h ?c))))

  (:action unload
    :parameters (?h ?c ?t ?p)
    :precondition (and (hoist ?h) (crate ?c) (truck ?t) (place ?p)
                       (at ?h ?p) (at ?t ?p) (available ?h) (in ?c ?t))
    :effect (and (lifting ?h ?c) (not (in ?c ?t)) (not (available ?h)))))
