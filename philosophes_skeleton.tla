---------------- MODULE philosophes_skeleton ----------------
(* Philosophes. Version en utilisant l'état des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

left(i) == (i+1)%N       \* philosophe à gauche du philo n°i
drrightoite(i) == (i+N-1)%N     \* philosophe à droite du philo n°i

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    state         \* i -> Hungry,Thinking,Eating

TypeInvariant == [](state \in [ Philos -> { Hungry, Thinking, Eating }])

(* TODO : autres propriétés de philosophes0 (exclusion, vivacité) *)  

----------------------------------------------------------------

Init == TRUE  \* À changer

ask(i) == TRUE  \* À changer

eat(i) == TRUE  \* À changer

think(i) == TRUE  \* À changer

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ eat(i)
                    \/ think(i)

Fairness == TRUE \* À changer

Spec ==
  /\ Init
  /\ [] [ Next ]_<<state>>
  /\ Fairness

================================
