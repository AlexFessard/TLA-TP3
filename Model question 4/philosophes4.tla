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
    state, forks_state, requests

TypeInvariant == 
  /\ state \in [Philos -> {Hungry, Thinking, Eating}]
  /\ forks_state \in [Forks -> [owner: Philos, state: {Dirty, Clean}]]
  /\ requests \in [Forks -> Seq(Philos)] \* mapping from forks to sequences of 
                                         \* philosophers waiting for them

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
  /\ requests = [i \in Forks |-> <<>>]

(* Transitions *)

ask(i) ==
  /\ state[i] \in {Hungry, Thinking}
  /\ (SelectSeq(requests[left_fork(i)], LAMBDA x: x = i) = <<>> \* check if i is already in the queue
      \/ SelectSeq(requests[right_fork(i)], LAMBDA x: x = i) = <<>>)
  /\ requests' = [requests EXCEPT
      ![left_fork(i)] = 
        IF forks_state[left_fork(i)].owner # i /\ SelectSeq(requests[left_fork(i)], LAMBDA x: x = i) = <<>>
            THEN Append(requests[left_fork(i)], i) 
        ELSE requests[left_fork(i)],
      ![right_fork(i)] = 
        IF forks_state[right_fork(i)].owner # i /\ SelectSeq(requests[right_fork(i)], LAMBDA x: x = i) = <<>>
            THEN Append(requests[right_fork(i)], i) 
        ELSE requests[right_fork(i)]]
  /\ state' = [state EXCEPT ![i] = Hungry]
  /\ UNCHANGED forks_state

receiveFork(i, j) == \* philosopher i receives fork j
  /\ state[i] = Hungry
  /\ requests[j] # <<>>
  /\ Head(requests[j]) = i
  /\ state[forks_state[j].owner] # Eating \* the owner of the fork is not eating
  /\ forks_state[j].owner # i
  /\ forks_state[j].state = Dirty
  /\ forks_state' = [forks_state EXCEPT 
        ![j] = [owner |-> i, state |-> Clean]] \* pass over the clean fork to i
  /\ requests' = [requests EXCEPT ![j] = Tail(requests[j])] \* remove i from the queue
  /\ UNCHANGED state

eat(i) ==
  /\ state[i] = Hungry
  /\ forks_state[left_fork(i)].owner = i
  /\ forks_state[right_fork(i)].owner = i
  /\ state' = [state EXCEPT ![i] = Eating]
  /\ UNCHANGED forks_state
  /\ UNCHANGED requests

think(i) ==
  /\ state[i] = Eating
  /\ state' = [state EXCEPT ![i] = Thinking]
  /\ forks_state' = [forks_state EXCEPT
      ![left_fork(i)] = [owner |-> forks_state[left_fork(i)].owner, state |-> Dirty],
      ![right_fork(i)] = [owner |-> forks_state[right_fork(i)].owner, state |-> Dirty]]
  /\ UNCHANGED requests

Next ==
  \E i \in Philos : \/ ask(i)
                    \/ \E j \in Forks : receiveFork(i, j)
                    \/ eat(i)
                    \/ think(i)

(* Contraintes d'équité *)
Fairness ==
  \A i \in Philos : 
    /\ WF_<<state, forks_state, requests>>(ask(i))
    /\ WF_<<state, forks_state, requests>>(receiveFork(i, left(i)))
    /\ WF_<<state, forks_state, requests>>(receiveFork(i, right(i)))
    /\ WF_<<state, forks_state, requests>>(eat(i))
    /\ WF_<<state, forks_state, requests>>(think(i))

Spec ==
  /\ Init
  /\ [][Next]_<<state, forks_state, requests>>
  /\ Fairness

================================