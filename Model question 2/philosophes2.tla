---------------- MODULE philosophes2 ----------------
EXTENDS Naturals

CONSTANT N

Philos == 0..N-1
Forks == 0..N-1

left(i) == (i+1) % N
right(i) == (i+N-1) % N

Hungry == "H"
Thinking == "Th"
Eating == "E"
Free == "F"
Taken == "Ta"

VARIABLES
    state, forks         \* state[i] -> Hungry, Thinking, Eating ; forks[i] -> Free, Taken

TypeInvariant == 
    /\ state \in [ Philos -> { Hungry, Thinking, Eating } ]
    /\ forks \in [ Forks -> { Free, Taken } ]

(* Propriétés *)
MutualExclusion ==
  []( \A i \in Philos : state[i] = Eating => state[left(i)] # Eating /\ state[right(i)] # Eating)

Liveness ==
  \A i \in Philos : (state[i] = Hungry) ~> (state[i] = Eating)

----------------------------------------------------------------

(* Initialisation *)
Init ==
    /\ state = [i \in Philos |-> Thinking]
    /\ forks = [i \in Forks |-> Free]

(* Transitions *)
ask(i) ==
  /\ state[i] = Thinking
  /\ state' = [state EXCEPT ![i] = Hungry]
  /\ UNCHANGED forks

takeForks(i) ==
    /\ state[i] = Hungry
    /\ forks[i] = Free
    /\ forks[right(i)] = Free
    /\ state' = [state EXCEPT ![i] = Eating]
    /\ forks' = [forks EXCEPT ![i] = Taken, ![right(i)] = Taken]

releaseForks(i) ==
    /\ state[i] = Eating
    /\ forks' = [forks EXCEPT ![i] = Free, ![right(i)] = Free]
    /\ state' = [state EXCEPT ![i] = Thinking]

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ takeForks(i)
                    \/ releaseForks(i)

(* Contraintes d'équité *)
Fairness ==
  \A i \in Philos : 
    /\ WF_state(ask(i))
    /\ WF_state(takeForks(i))
    /\ WF_state(releaseForks(i))

Spec ==
  /\ Init
  /\ [] [Next]_<<state>>
  /\ Fairness

================================