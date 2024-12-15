---------------- MODULE philosophes1 ----------------
EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

left(i) == (i+1) % N
right(i) == (i+N-1) % N

Hungry == "H"
Thinking == "T"
Eating == "E"

VARIABLES
    state         \* i -> Hungry, Thinking, Eating

TypeInvariant == 
  state \in [ Philos -> { Hungry, Thinking, Eating } ]

(* Propriétés *)
MutualExclusion ==
  []( \A i \in Philos : state[i] = Eating => state[left(i)] # Eating /\ state[right(i)] # Eating)

Liveness ==
  \A i \in Philos : (state[i] = Hungry) ~> (state[i] = Eating)

----------------------------------------------------------------

(* Initialisation *)
Init ==
  state = [i \in Philos |-> Thinking]

(* Transitions *)
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

(* Contraintes d'équité *)
Fairness ==
  \A i \in Philos : 
    /\ WF_state(ask(i))
    /\ WF_state(eat(i))
    /\ WF_state(think(i))

Spec ==
  /\ Init
  /\ [] [Next]_<<state>>
  /\ Fairness

================================