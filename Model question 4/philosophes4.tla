---------------- MODULE philosophes4 ----------------
EXTENDS Naturals, Sequences

CONSTANT N

Philos == 0..N-1
Forks == 0..N-1

left(i) == (i+1) % N
right(i) == (i+N-1) % N

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
  /\ forks_state = [i \in Forks |-> [owner |-> 
    IF i < right(i) THEN i 
    ELSE right(i), state |-> Dirty]]
  /\ requests = [i \in Forks |-> <<>>]

(* Transitions *)

ask(i) ==
  /\ state[i] = Thinking
  /\ IF forks_state[i].owner # i THEN
        requests' = [requests EXCEPT ![i] = Append(requests[i], i)]
     ELSE
        requests' = requests
  /\ IF forks_state[right(i)].owner # i THEN
        requests' = [requests EXCEPT ![right(i)] = Append(requests[right(i)], i)]
     ELSE
        requests' = requests
    /\ state' = [state EXCEPT ![i] = Hungry]
    /\ UNCHANGED forks_state

receiveFork(i, j) ==
  /\ state[i] = Hungry
  /\ requests[j] /= <<>>
  /\ Head(requests[j]) = i
  /\ forks_state[j].owner # i
  /\ forks_state[j].state = Dirty
  /\ forks_state' = [forks_state EXCEPT ![j] = [owner |-> i, state |-> Clean]]
  /\ requests' = [requests EXCEPT ![j] = Tail(requests[j])]
  /\ UNCHANGED state

eat(i) ==
  /\ state[i] = Hungry
  /\ forks_state[i].owner = i
  /\ forks_state[right(i)].owner = i
  /\ state' = [state EXCEPT ![i] = Eating]
  /\ UNCHANGED forks_state
  /\ UNCHANGED requests

think(i) ==
  /\ state[i] = Eating
  /\ state' = [state EXCEPT ![i] = Thinking]
  /\ forks_state' = [forks_state EXCEPT
      ![left(i)] = [owner |-> forks_state[left(i)].owner, state |-> Dirty],
      ![right(i)] = [owner |-> forks_state[right(i)].owner, state |-> Dirty]]
  /\ requests' = [requests EXCEPT
      ![left(i)] = Append(requests[left(i)], i),
      ![right(i)] = Append(requests[right(i)], i)]

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