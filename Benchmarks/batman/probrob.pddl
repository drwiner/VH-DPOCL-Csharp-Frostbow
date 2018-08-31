(define (problem rob)
(:domain batman)
(:objects batman joker harvey rachel henchman1 henchman2 - character
 52ndst avex gothampd car1 car2 - location
)
(:init (player batman)
 (alive harvey)
 (alive rachel)
 (at batman gothampd)
 (at joker gothampd)
 (apprehended joker)
 (at henchman1 car1)
 (henchman henchman1)
 (has henchman1 harvey)
 (at henchman2 car2)
 (henchman henchman2)
 (has henchman2 rachel)
 (connected 52ndst car1)
 (connected 52ndst car2)
 (connected 52ndst gothampd)
 (connected avex car1)
 (connected avex car2)
 (connected avex gothampd)
)
(:goal (AND (saved harvey batman)
 (not (alive rachel))
)))