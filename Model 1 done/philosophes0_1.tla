---------------- MODULE philosophes0_1 ----------------
(* Philosophes. Version en utilisant l'état des voisins. *)

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

left(i) == (i+1)%N       \* philosophe à gauche du philo n°i
right(i) == (i+N-1)%N     \* philosophe à droite du philo n°i

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    state         \* i -> Hungry,Thinking,Eating

TypeInvariant == [](state \in [ Philos -> { Hungry, Thinking, Eating }])

MutualExclusion ==
  []( \A i \in Philos : state[i] = Eating => state[left(i)] # Eating /\ state[right(i)] # Eating)

Liveness ==
  \A i \in Philos : (state[i] = Hungry) ~> (state[i] = Eating)
----------------------------------------------------------------

Init ==
    /\ state = [i \in Philos |-> Thinking]

ask(i) ==
    /\ state[i] = Thinking
    /\ state' = [state EXCEPT ![i] = Hungry]

eat(i) ==
    /\ state[i] = Hungry
    /\ state[left(i)] # Eating
    /\ state[right(i)] # Eating
    /\ state' = [state EXCEPT ![i] = Eating]

think(i) ==
    /\ state[i] = Eating
    /\ state' = [state EXCEPT ![i] = Thinking]

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ eat(i)
                    \/ think(i)

Fairness ==
    \A i \in Philos : 
        /\ SF_state(ask(i))
        /\ SF_state(eat(i))
        /\ SF_state(think(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<state>>
  /\ Fairness

================================
