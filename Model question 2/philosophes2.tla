---------------- MODULE philosophes2 ----------------

EXTENDS Naturals

CONSTANT N  \* Number of philosophers

Philos == 0..N-1  \* Set of philosophers indexed from 0 to N-1
Forks == 0..N-1  \* Set of forks indexed from 0 to N-1

left(i) == (i+1)%N  \* Function to get the philosopher or fork at the left of i
right(i) == (i+N-1)%N  \* Function to get the philosopher or fork at the right of i

Hungry == "H"  \* State representing a hungry philosopher
Thinking == "T"  \* State representing a thinking philosopher
Eating == "E"  \* State representing an eating philosopher
Unhold == N  \* State representing an unheld fork

VARIABLES
    state,  \* State variable mapping each philosopher to their current state
    forks_state  \* State variable mapping each fork to its current holder

TypeInvariant ==
    [](/\ state \in [ Philos -> { Hungry, Thinking, Eating }]
        /\ forks_state \in [ Forks -> 0..N])  \* Invariant ensuring state and forks_state are valid

MutualExclusion == []( \A i \in Philos : state[i] = Eating => state[left(i)] # Eating /\ state[right(i)] # Eating)  \* Ensures no two adjacent philosophers are eating simultaneously

Liveness == [](\A i \in Philos : state[i] = Hungry => <>(state[i] = Eating))  \* Ensures that every hungry philosopher eventually gets to eat

GlobalLiveness == []((\E i \in Philos: state[i] = Hungry) => <>(\E j \in Philos: state[j] = Eating))  \* Ensures that if any philosopher is hungry, eventually some philosopher will eat

----------------------------------------------------------------

Init ==
    /\ state = [ i \in Philos |-> Thinking ]  \* Initial state where all philosophers are thinking
    /\ forks_state = [ i \in Forks |-> Unhold ]  \* Initial state where all forks are unheld

ask(i) ==
    /\ state[i] = Thinking  \* Transition from thinking to hungry
    /\ state' = [ state EXCEPT ![i] = Hungry ]
    /\ UNCHANGED forks_state

eat(i) ==
    /\ state[i] = Hungry  \* Transition from hungry to eating
    /\ state[left(i)] /= Eating  \* Ensures left neighbor is not eating
    /\ state[right(i)] /= Eating  \* Ensures right neighbor is not eating
    /\ forks_state[left(i)] = i  \* Ensures left fork is held by the philosopher
    /\ forks_state[right(i)] = i  \* Ensures right fork is held by the philosopher
    /\ state' = [ state EXCEPT ![i] = Eating ]
    /\ UNCHANGED forks_state

think(i) ==
    /\ state[i] = Eating  \* Transition from eating to thinking
    /\ forks_state' = [ forks_state EXCEPT
        ![left(i)] = Unhold,
        ![right(i)] = Unhold]  \* Release both forks
    /\ state' = [ state EXCEPT ![i] = Thinking ]

request_left_fork(i) ==
    /\ state[i] = Hungry  \* Transition to request left fork
    /\ forks_state[left(i)] = Unhold  \* Ensure left fork is unheld
    /\ forks_state' = [ forks_state EXCEPT ![left(i)] = i ]  \* Hold left fork
    /\ UNCHANGED state

request_right_fork(i) ==
    /\ state[i] = Hungry  \* Transition to request right fork
    /\ forks_state[right(i)] = Unhold  \* Ensure right fork is unheld
    /\ forks_state' = [ forks_state EXCEPT ![right(i)] = i ]  \* Hold right fork
    /\ UNCHANGED state

Next ==
  \E i \in Philos : \/ ask(i)  \* Non-deterministic choice of transitions
                    \/ eat(i)
                    \/ think(i)
                    \/ request_left_fork(i)
                    \/ request_right_fork(i)

Fairness ==
    \A i \in Philos :
        /\ WF_<<state, forks_state>>(eat(i))  \* Weak fairness for eat transition
        /\ WF_<<state, forks_state>>(think(i))  \* Weak fairness for think transition
        /\ SF_<<state, forks_state>>(request_left_fork(i))  \* Strong fairness for request left fork transition
        /\ SF_<<state, forks_state>>(request_right_fork(i))  \* Strong fairness for request right fork transition

Spec ==
  /\ Init  \* Specification includes the initial state
  /\ [] [ Next ]_<<state, forks_state>>  \* Specification includes the next-state relation
  /\ Fairness  \* Specification includes fairness constraints

================================