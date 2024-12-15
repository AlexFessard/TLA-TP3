---------------- MODULE philosophes3 ----------------

EXTENDS Naturals

CONSTANT N

Philos == 0..N-1
Forks == 0..N-1

left(i) == (i+1)%N       \* get the philo or fork at the left of n°i
right(i) == (i+N-1)%N     \* get the philo or fork at the right of n°i

Hungry == "H"
Thinking == "T"
Eating == "E"
Unhold == N

VARIABLES
    state,
    forks_state

TypeInvariant ==
    [](/\ state \in [ Philos -> { Hungry, Thinking, Eating }]
        /\ forks_state \in [ Forks -> 0..N])

Safety == [](\A x \in Philos: \A y \in Philos \ { x }: ~(state[x] = Eating /\ state[y] = Eating))

Liveness == [](\A i \in Philos : state[i] = Hungry => <>(state[i] = Eating))

GlobalLiveness == []((\E i \in Philos: state[i] = Hungry) => <>(\E j \in Philos: state[j] = Eating))

----------------------------------------------------------------

Init ==
    /\ state = [ i \in Philos |-> Thinking ]
    /\ forks_state = [ i \in Forks |-> Unhold ]

ask(i) ==
    /\ state[i] = Thinking
    /\ state' = [ state EXCEPT ![i] = Hungry ]
    /\ UNCHANGED forks_state

eat(i) ==
    /\ state[i] = Hungry
    /\ state[left(i)] /= Eating
    /\ state[right(i)] /= Eating
    /\ forks_state[left(i)] = i
    /\ forks_state[right(i)] = i
    /\ state' = [ state EXCEPT ![i] = Eating ]
    /\ UNCHANGED forks_state

think(i) ==
    /\ state[i] = Eating
    /\ forks_state' = [ forks_state EXCEPT
        ![left(i)] = Unhold,
        ![right(i)] = Unhold]
    /\ state' = [ state EXCEPT ![i] = Thinking ]

request_both_forks(i) ==
    /\ state[i] = Hungry
    /\ forks_state[left(i)] = Unhold
    /\ forks_state[right(i)] = Unhold
    /\ forks_state' = [ forks_state EXCEPT ![left(i)] = i, ![right(i)] = i ]
    /\ UNCHANGED state

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ eat(i)
                    \/ think(i)
                    \/ request_both_forks(i)

Fairness ==
    \A i \in Philos :
        /\ WF_<<state, forks_state>>(eat(i))
        /\ WF_<<state, forks_state>>(think(i))
        /\ WF_<<state, forks_state>>(ask(i))

Spec ==
  /\ Init
  /\ [] [ Next ]_<<state, forks_state>>
  /\ Fairness

================================