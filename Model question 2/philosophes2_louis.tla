---------------- MODULE philosophes2 ----------------
EXTENDS Naturals

CONSTANT N

Philos == 0..N-1

left(i) == (i+1) % N
right(i) == (i+N-1) % N

Hungry == "H"
Thinking == "T"
Eating == "E"
Free == "F"
Taken == "T"

VARIABLES
    state, forks        \* state[i] -> Hungry, Thinking, Eating ; forks[i] -> Free, Taken

TypeInvariant == 
  /\ state \in [Philos -> { Hungry, Thinking, Eating }]
  /\ forks \in [Philos -> { Free, Taken }]

(* Properties *)
MutualExclusion ==
  []( \A i \in Philos : state[i] = Eating => (state[left(i)] # Eating /\ state[right(i)] # Eating))

Liveness ==
  \A i \in Philos : (state[i] = Hungry) ~> (state[i] = Eating)

DeadlockFreedom ==
  \A i \in Philos : state[i] /= Hungry

----------------------------------------------------------------

(* Initialization *)
Init ==
  /\ state = [i \in Philos |-> Thinking]
  /\ forks = [i \in Philos |-> Free]

(* Transitions *)

ask(i) ==
  /\ state[i] = Thinking
  /\ state' = [state EXCEPT ![i] = Hungry]
  /\ UNCHANGED forks

takeLeftFork(i) ==
    /\ state[i] = Hungry
    /\ forks[i] = Free
    /\ state' = [state EXCEPT ![i] = Eating]
    /\ forks' = [forks EXCEPT ![i] = Taken]

takeRightFork(i) ==
    /\ state[i] = Eating
    /\ forks[right(i)] = Free
    /\ state' = [state EXCEPT ![i] = Eating]
    /\ forks' = [forks EXCEPT ![right(i)] = Taken]

releaseLeftFork(i) ==
    /\ state[i] = Eating
    /\ forks[i] = Taken
    /\ forks' = [forks EXCEPT ![i] = Free]
    /\ state' = [state EXCEPT ![i] = Thinking]

releaseRightFork(i) ==
    /\ state[i] = Eating
    /\ forks[right(i)] = Taken
    /\ forks' = [forks EXCEPT ![right(i)] = Free]
    /\ state' = [state EXCEPT ![i] = Thinking]

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ takeLeftFork(i)
                    \/ takeRightFork(i)
                    \/ releaseLeftFork(i)
                    \/ releaseRightFork(i)

(* Fairness Constraints *)
Fairness ==
  \A i \in Philos : 
    /\ SF_state(ask(i))
    /\ SF_state(takeLeftFork(i))
    /\ SF_state(releaseLeftFork(i))
    /\ SF_state(takeRightFork(i))
    /\ SF_state(releaseRightFork(i))

Spec ==
  /\ Init
  /\ [] [Next]_<<state, forks>>
  /\ Fairness

================================