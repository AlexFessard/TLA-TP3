---------------- MODULE philosophes1 ----------------
EXTENDS Naturals

CONSTANT N  \* Number of philosophers

Philos == 0..N-1  \* Set of philosophers indexed from 0 to N-1

left(i) == (i+1) % N  \* Function to get the philosopher to the left
right(i) == (i+N-1) % N  \* Function to get the philosopher to the right

Hungry == "H"  \* State representing a hungry philosopher
Thinking == "T"  \* State representing a thinking philosopher
Eating == "E"  \* State representing an eating philosopher

VARIABLES
    state  \* State variable mapping each philosopher to their current state

TypeInvariant == 
  state \in [ Philos -> { Hungry, Thinking, Eating } ]  \* Invariant ensuring state is valid

(* Propriétés *)
MutualExclusion ==
  []( \A i \in Philos : state[i] = Eating => state[left(i)] # Eating /\ state[right(i)] # Eating)  \* Ensures no two adjacent philosophers are eating simultaneously

Liveness ==
  \A i \in Philos : (state[i] = Hungry) ~> (state[i] = Eating)  \* Ensures that every hungry philosopher eventually gets to eat

----------------------------------------------------------------

(* Initialisation *)
Init ==
  state = [i \in Philos |-> Thinking]  \* Initial state where all philosophers are thinking

(* Transitions *)
ask(i) ==
  /\ state[i] = Thinking  \* Transition from thinking to hungry
  /\ state' = [state EXCEPT ![i] = Hungry]

eat(i) ==
  /\ state[i] = Hungry  \* Transition from hungry to eating
  /\ state[left(i)] # Eating  \* Ensures left neighbor is not eating
  /\ state[right(i)] # Eating  \* Ensures right neighbor is not eating
  /\ state' = [state EXCEPT ![i] = Eating]

think(i) ==
  /\ state[i] = Eating  \* Transition from eating to thinking
  /\ state' = [state EXCEPT ![i] = Thinking]

Next ==
  \E i \in Philos : \/ ask(i)  \* Non-deterministic choice of transitions
                    \/ eat(i)
                    \/ think(i)

(* Contraintes d'équité *)
Fairness ==
  \A i \in Philos : 
    /\ SF_state(ask(i))  \* Strong fairness for ask transition
    /\ WF_state(eat(i))  \* Weak fairness for eat transition
    /\ WF_state(think(i))  \* Weak fairness for think transition

Spec ==
  /\ Init  \* Specification includes the initial state
  /\ [] [Next]_<<state>>  \* Specification includes the next-state relation
  /\ Fairness  \* Specification includes fairness constraints

================================