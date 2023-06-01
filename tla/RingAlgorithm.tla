--------------------------- MODULE RingAlgorithm ---------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

ProcessID == 1..N

VARIABLES State, MessageBox

Message == {"PROBE", "SELECTED"} \X ProcessID

\* Initializzes the variables: State and MessageBox
Init == /\ State = [p \in ProcessID |-> [ 
                        ID |-> p,
                        Condition |-> "Active",
                        Leader |-> N,
                        Participating |-> FALSE]]
        /\ MessageBox = [p \in ProcessID |-> <<>>]

\* Finds the highest ID that is not dead.
MaxAliveID == CHOOSE id \in ProcessID : 
        \A p \in ProcessID : 
            State[p].Condition = "Dead" \/ id >= p

\* Get the next alive process
Neighbour(p) == 
    LET AliveProcesses == {q \in ProcessID : State[q].Condition = "Active"}
    IN
    IF p = MaxAliveID THEN CHOOSE q \in AliveProcesses : TRUE ELSE
            CHOOSE neighbour \in AliveProcesses :
                    /\ p < neighbour
                    /\ \A q \in AliveProcesses : q <= p \/ neighbour <= q

\* Sends a message and removes the head from the inbox. Sends message msg to q with id id, 
\* and removes the first message from p.
SendMessageAndTailMessageBox(p, q, id, msg) == 
            MessageBox' = [MessageBox EXCEPT ![q] = Append(MessageBox[q], <<msg, id>>), 
                            ![p] = Tail(MessageBox[p])]

\* Simple SendMessage. Sends message msg to q with id id.
SendMessage(q, id, msg) ==
            MessageBox' = [MessageBox EXCEPT ![q] = Append(MessageBox[q], <<msg, id>>)]

\* Send message to q and empty message box of p
SendMessageAndEmptyMessageBox(p, q, id, msg) ==
            MessageBox' = [MessageBox EXCEPT ![q] = Append(MessageBox[q], <<msg, id>>), ![p] = <<>>]

\* Handle Messages
HandleMessages(p) == LET
            id == Head(MessageBox[p])[2]
            msg == Head(MessageBox[p])[1]
            IN
            /\ State[p].Condition = "Active" \* Only if the process is active
            /\ MessageBox[p] /= <<>>         \* The message box shouldn't be empty
            /\ \/ /\ State[id].Condition = "Dead"
                  /\ MessageBox' = [MessageBox EXCEPT ![p] = Tail(MessageBox[p])]
                  /\ UNCHANGED State
               \/ /\ msg = "PROBE" \* If the message is PROBE
                  /\ \/ /\ State[p].Participating = FALSE \* Make sure the participation status is TRUE
                        /\ State' = [State EXCEPT ![p].Participating = TRUE]
                     \/ /\ State[p].Participating = TRUE
                        /\ UNCHANGED State
                  /\ \/ /\ p = id \* If p = id, send SELECTED
                        /\ SendMessageAndEmptyMessageBox(p, Neighbour(p), p, "SELECTED")
                     \/ /\ p > id  /\ State[p].Participating = FALSE \* If p > id ignore message 
                        /\ SendMessageAndTailMessageBox(p, Neighbour(p), p, "PROBE")
                     \/ /\ p > id /\ State[p].Participating = TRUE
                        /\ MessageBox' = [MessageBox EXCEPT ![p] = Tail(MessageBox[p])]
                     \/ /\ p < id \* If p < id send probe to neighbour
                        /\ SendMessageAndTailMessageBox(p, Neighbour(p), id, "PROBE")
               \/ /\ msg = "SELECTED" \* If the message is SELECTED
                  /\ \/ /\ p /= id \* If p /= id, then send SELECTED to neighbour
                        /\ State' = [State EXCEPT ![p].Leader = id, ![p].Participating = FALSE]
                        /\ SendMessageAndEmptyMessageBox(p, Neighbour(p), id, "SELECTED")
                     \/ /\ p = id \* if p = id then declare itself the leader
                        /\ State' = [State EXCEPT ![p].Leader = id, ![p].Participating = FALSE]
                        /\ MessageBox' = [MessageBox EXCEPT ![p] = <<>>]

\* If the leader is dead, send a PROBE message, if the only alive process is the first one, 
\* then make p the process, end the election and go into deadlock
CheckLeader(p) == /\ State[p].Condition = "Active"
                  /\ State[State[p].Leader].Condition = "Dead"
                  /\ State[p].Participating = FALSE
                  /\ \/ /\ MaxAliveID = 1 
                        /\ State' = [State EXCEPT ![p].Leader = p, ![p].Participating = FALSE]
                        /\ UNCHANGED MessageBox
                     \/ /\ MaxAliveID /= 1
                        /\ SendMessage(Neighbour(p), p, "PROBE")
                        /\ State' = [State EXCEPT ![p].Participating = TRUE]   

\* Makes sure the algorithm runs correctly                  
KillLeader ==
   /\ State[MaxAliveID].Leader = MaxAliveID
   /\ State' = [State EXCEPT ![MaxAliveID].Condition = "Dead"]
   /\ Cardinality({p \in ProcessID : State[p].Condition = "Active"}) >= 2
   /\ UNCHANGED MessageBox

Next == \/ KillLeader
        \/ \E p \in 1..MaxAliveID : HandleMessages(p) \/ CheckLeader(p)

Spec == Init /\ [][Next]_<<State, MessageBox>> /\ SF_<<State, MessageBox>>(Next)

----
\*Invariants

TypeOK == \A p \in ProcessID:
        /\ State[p].ID \in ProcessID
        /\ State[p].Condition \in {"Active", "Dead"}
        /\ State[p].Leader \in ProcessID
        /\ State[p].Participating \in BOOLEAN
        /\ MessageBox \in [ProcessID -> Seq(Message)]
      
UniqueID == \A p,q \in ProcessID : (State[p].ID = State[q].ID) => (p = q)

----
\*Properties
 
ElectionTerminationImpliesSameLeader == \A p, q \in ProcessID : 
    (State[p].Condition = "Active" 
    /\ State[q].Condition = "Active" 
    /\ State[p].Participating = FALSE 
    /\ State[q].Participating = FALSE) 
    => (State[p].Leader = State[q].Leader)

\* Eventually, the election will end
ElectionWillEnd == \A p \in ProcessID : State[p].Participating ~> (<> (State[p].Participating = FALSE))

HighestAliveProcessIsLeader == \A p \in ProcessID:
    State[p].Participating = FALSE =>
       (State[MaxAliveID].Condition = "Active" => State[p].Leader = MaxAliveID)

=============================================================================
