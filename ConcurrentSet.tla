---- MODULE ConcurrentSet ----

CONSTANTS
    Inserters,
    Values

VARIABLES
    pc,
    values_to_insert,
    output,
    set

Vars == <<pc, values_to_insert, output, set>>

Init ==
    /\ pc = [i \in Inserters |-> "PickValue"]
    /\ values_to_insert \in [Inserters -> Values]
    /\ output = [i \in Inserters |-> "maybe"]
    /\ set \subseteq Values

MapSet(m, k, v) == m' = [m EXCEPT ![k] = v]

PickValue(i) ==
    /\ pc[i] = "PickValue"
    /\ \E v \in Values: MapSet(values_to_insert, i, v)
    /\ MapSet(pc, i, "DoInsert")
    /\ UNCHANGED <<output, set>>

\* return "yes" if value is newly inserted
\* return "no" if it was already in the set
\* can always return "maybe"
DoInsert(i) ==
    /\ pc[i] = "DoInsert"
    /\ LET legal_output == {"maybe", IF values_to_insert[i] \notin set THEN "yes" ELSE "no"} IN
       \E o \in legal_output: MapSet(output, i, o)
    /\ set' = set \union {values_to_insert[i]}
    /\ MapSet(pc, i, "PickValue")
    /\ UNCHANGED <<values_to_insert>>

Next ==
    \E i \in Inserters:
    \/ PickValue(i)
    \/ DoInsert(i)

Spec == Init /\ [][Next]_Vars

====
