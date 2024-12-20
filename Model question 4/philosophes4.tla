---------------- MODULE philosophes4 ----------------
EXTENDS Naturals, Sequences

CONSTANT N

Philos == 0..N-1
Forks == 0..N-1

right(i) == (i+1) % N
left(i) == (i+N-1) % N

left_fork(i) == i
right_fork(i) == right(i)

Hungry == "H"
Thinking == "T"
Eating == "E"
Dirty == "D"
Clean == "C"

VARIABLES
    state, forks_state, requested

TypeInvariant == 
  /\ state \in [Philos -> {Hungry, Thinking, Eating}]
  /\ forks_state \in [Forks -> [owner: Philos, state: {Dirty, Clean}]]
  /\ requested \in [Philos -> [left: BOOLEAN, right: BOOLEAN]]

(* Propriétés *)
MutualExclusion ==
  \A i \in Philos : state[i] = Eating => state[left(i)] # Eating /\ state[right(i)] # Eating

Liveness ==
  \A i \in Philos : (state[i] = Hungry) ~> (state[i] = Eating)

----------------------------------------------------------------

(* Initialisation *)
Init ==
  /\ state = [i \in Philos |-> Thinking]
  /\ forks_state = [i \in Forks |-> 
    [owner |-> IF i < left(i) THEN i 
               ELSE left(i), 
    state |-> Dirty]]
  /\ requested = [i \in Philos |-> [left |-> FALSE, right |-> FALSE]]

(* Transitions *)

ask(i) ==
    /\ state[i] \in {Hungry, Thinking}
    /\ forks_state[left_fork(i)].owner # i
    /\ forks_state[right_fork(i)].owner # i
    /\ (requested[i].left = FALSE \/ requested[i].right = FALSE)
    /\ requested' = 
        [requested EXCEPT ![i] = 
            [left |-> 
                (
                \/ requested[i].left 
                \/ (/\ forks_state[left_fork(i)].owner # i 
                    /\ (\/ forks_state[left_fork(i)].state = Clean 
                        \/ state[left(i)] = Eating)
                    )
                ),
            right |-> 
                (
                \/ requested[i].right 
                \/ (/\ forks_state[right_fork(i)].owner # i
                    /\ (\/ forks_state[right_fork(i)].state = Clean
                        \/ state[right(i)] = Eating)
                    )
                )
            ]
        ]
    /\ state' = [state EXCEPT ![i] = Hungry]
    /\ forks_state' = [forks_state EXCEPT
        ![left_fork(i)] = [owner |-> 
            IF state[forks_state[left_fork(i)].owner] # Eating /\ forks_state[left_fork(i)].state = Dirty 
                THEN i 
            ELSE @.owner,
                         state |-> 
            IF state[forks_state[left_fork(i)].owner] # Eating /\ forks_state[left_fork(i)].state = Dirty 
                THEN Clean 
            ELSE @.state],
        ![right_fork(i)] = [owner |-> 
            IF state[forks_state[right_fork(i)].owner] # Eating /\ forks_state[right_fork(i)].state = Dirty 
                THEN i 
            ELSE @.owner,
                          state |-> 
            IF state[forks_state[right_fork(i)].owner] # Eating /\ forks_state[right_fork(i)].state = Dirty 
                THEN Clean 
            ELSE @.state]]

eat(i) ==
  /\ state[i] = Hungry
  /\ forks_state[left_fork(i)].owner = i
  /\ forks_state[right_fork(i)].owner = i
  /\ state' = [state EXCEPT ![i] = Eating]
  /\ forks_state' = [forks_state EXCEPT
      ![left_fork(i)] = [owner |-> @.owner, state |-> Dirty],
      ![right_fork(i)] = [owner |-> @.owner, state |-> Dirty]]
  /\ UNCHANGED requested

release(i) ==
    /\ state[i] = Eating
    /\ state' = [state EXCEPT ![i] = Thinking]
    /\ forks_state' = [forks_state EXCEPT
        ![right_fork(i)] = 
        [owner |-> 
            IF requested[right(i)].left = TRUE 
                THEN right(i) 
            ELSE @.owner,
        state |-> 
            IF requested[right(i)].left = TRUE 
                THEN Clean 
            ELSE @.state],
        ![left_fork(i)] =  
        [owner |-> 
            IF requested[left(i)].right = TRUE 
                THEN left(i) 
            ELSE @.owner,
        state |-> 
            IF requested[left(i)].right = TRUE 
                THEN Clean 
            ELSE @.state]]
    /\ requested' = [requested EXCEPT 
        ![left(i)] = [left |-> @.left, right |-> FALSE],
        ![right(i)] = [left |-> FALSE, right |-> @.right]]

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ eat(i)
                    \/ release(i)

(* Contraintes d'équité *)
Fairness ==
  \A i \in Philos : 
    /\ WF_<<state, forks_state, requested>>(ask(i))
    /\ WF_<<state, forks_state, requested>>(eat(i))
    /\ WF_<<state, forks_state, requested>>(release(i))

Spec ==
  /\ Init
  /\ [][Next]_<<state, forks_state, requested>>
  /\ Fairness

================================