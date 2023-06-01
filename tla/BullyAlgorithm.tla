--------------------------- MODULE BullyAlgorithm --------------------------

EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANT N

ASSUME N \in Nat

ProcessID == 1..N

VARIABLES State, MessageBox

Message == ProcessID \X {"ELECTION", "ALIVE", "VICTORY"}

Init == /\ State = [p \in ProcessID |->
                        [ID |-> p,
                        Condition |-> "Active",
                        Leader |-> N,
                        Participating |-> FALSE]]
        /\ MessageBox = [p \in ProcessID |-> <<>>]

\* Finds the maximum ID which is not dead
MaxAliveID == CHOOSE id \in ProcessID : 
                \A p \in ProcessID: State[p].Condition = "Dead" 
                                     \/ id >= State[p].ID

HigherIDs(p) == {q \in 1..MaxAliveID: q > p}

SendAliveAndTail(p, q) == 
    MessageBox' = [MessageBox EXCEPT ![q] = Append(MessageBox[q], <<p, "ALIVE">>), 
                                     ![p] = Tail(MessageBox[p])]

SendVictory(p) ==   
    MessageBox' = [q \in ProcessID |-> 
            IF q /= p /\ State[q].Condition = "Active" 
            THEN Append(MessageBox[q], <<p, "VICTORY">>) 
            ELSE MessageBox[q]]

SendVictoryAndTail(p) == 
    MessageBox' = [q \in ProcessID |-> 
        IF State[q].Condition = "Active" 
        THEN IF q = p THEN Tail(MessageBox[q]) ELSE Append(MessageBox[q], <<p, "VICTORY">>) 
        ELSE MessageBox[q]]

SendElection(p) == 
    MessageBox' = [q \in ProcessID |-> 
        IF q \in HigherIDs(p) /\ State[q].Condition = "Active" 
        THEN Append(MessageBox[q], <<p, "ELECTION">>) 
        ELSE MessageBox[q]]
  
ReceiveAlive(p, q) == /\ State[p].Participating = TRUE \* Make sure they are already participating
                      /\ p > q
                      /\ State' = [State EXCEPT ![p].Participating = FALSE] \* No longer participate

ReceiveElection(p, q) ==  \/ /\ p = MaxAliveID
                             /\ SendVictoryAndTail(p)
                             /\ State' = [State EXCEPT ![p].Participating = FALSE, 
                                                       ![p].Leader = p]
                          \/ /\ p /= MaxAliveID
                             /\ \/ /\ State[p].Participating = TRUE
                                   /\ SendAliveAndTail(p, q)
                                   /\ UNCHANGED State
                                \/ /\ State[p].Participating = FALSE
                                   /\ SendAliveAndTail(p, q) 
                                   /\ State' = [State EXCEPT ![p].Participating = TRUE]

ReceiveVictory(p, q) == State' = [State EXCEPT ![p].Leader = q] \* Set the leader of receiver to p sender

\* Handle messages
HandleMessages(p) == LET 
                    sender == Head(MessageBox[p])[1] 
                    msg == Head(MessageBox[p])[2]
                    IN
                     /\ State[p].Condition = "Active"
                     /\ MessageBox[p] /= <<>>  \* Message box shouldn't be empty
                     /\ \/ /\ msg = "VICTORY" \* If the message is VICTORY
                           /\ State[sender].Condition = "Active"
                           /\ ReceiveVictory(p, sender)
                           /\ MessageBox' = [MessageBox EXCEPT ![p] = <<>>] \* Remove all messages, so that the election does not run forever.
                        \/ /\ msg = "ELECTION" \* If the message is ELECTION
                           /\ State[sender].Condition = "Active"
                           /\ ReceiveElection(p, sender) \* Tail is done incide ReceiveElection
                        \/ /\ msg = "ALIVE" \* If the message is ALIVE
                           /\ State[sender].Condition = "Active"
                           /\ ReceiveAlive(p, sender) \* Handle in ReceiveAlive
                           /\ MessageBox' = [MessageBox EXCEPT ![p] = Tail(MessageBox[p])] \* Remove first message
                            
\* If the leader is found to be dead                          
CheckLeader(p) ==   /\ State[p].Condition = "Active"
                    /\ State[State[p].Leader].Condition = "Dead"
                    /\ \/ /\ p = MaxAliveID
                          /\ SendVictory(p)
                          /\ State' = [State EXCEPT ![p].Participating = FALSE, ![p].Leader = p]
                       \/ /\ p /= MaxAliveID 
                          /\ State[p].Participating = FALSE
                          /\ SendElection(p)
                          /\ State' = [State EXCEPT ![p].Participating = TRUE] 
                          
KillLeader ==
   /\ State[MaxAliveID].Leader = MaxAliveID
   /\ State' = [State EXCEPT ![MaxAliveID].Condition = "Dead", ![MaxAliveID].Participating = FALSE]
   /\ Cardinality({p \in ProcessID : State[p].Condition = "Active"}) >= 2
   /\ UNCHANGED MessageBox

Next == \/ KillLeader
        \/ \E p \in 1..MaxAliveID : CheckLeader(p) \/ HandleMessages(p)

Spec == Init /\ [][Next]_<<State, MessageBox>> /\ SF_<<State, MessageBox>>(Next)
----
\* Invariants

\* Each variable should be within the type constraints
TypeOK == \A p \in ProcessID :
        /\ State[p].ID \in ProcessID
        /\ State[p].Condition \in {"Active", "Dead"}
        /\ State[p].Leader \in ProcessID
        /\ State[p].Participating \in BOOLEAN
        /\ MessageBox \in [ProcessID -> Seq(Message)]

\* Every process should have a unique ID
UniqueID == \A p,q \in ProcessID : (State[p].ID = State[q].ID) => (p = q)

\* If a process is participating in the election, then it should not be the leader
Participating == \A p \in ProcessID: State[p].Participating = TRUE => State[p].Leader /= p
----
\* Properties
ElectionTerminationImpliesSameLeader == \A p, q \in ProcessID : 
    (State[p].Condition = "Active" 
    /\ State[q].Condition = "Active" 
    /\ State[p].Participating = FALSE 
    /\ State[q].Participating = FALSE) 
    => (State[p].Leader = State[q].Leader)


\* The highest alive process should become the leader
HighestAliveProcessIsLeader == \A p \in ProcessID :
    State[p].Participating = FALSE => 
    (State[MaxAliveID].Condition = "Active" => State[p].Leader = MaxAliveID)

\* Eventually, the election will end
ElectionWillEnd == \A p \in ProcessID : State[p].Participating ~> State[p].Participating = FALSE

============================================================================
