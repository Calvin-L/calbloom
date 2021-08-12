---- MODULE ConcurrentSetLog ----

EXTENDS Naturals, Sequences, TLC

PartialFunction(D, R) == UNION {[d -> R] : d \in SUBSET D}
Last(seq) == seq[Len(seq)]

CONSTANTS
    Inserters,
    Values

State == [
    pc :     [Inserters -> {"DoInsert", "Done"}],
    values_to_insert : [Inserters -> Values],
    output : PartialFunction(Inserters, {"yes", "no", "maybe"})]

VARIABLES
    log

Vars == <<log>>

TypeOK ==
    log \in Seq(State)

Init ==
    \E values_to_insert \in [Inserters -> Values]:
        log = <<[
            pc |-> [i \in Inserters |-> "DoInsert"],
            values_to_insert |-> values_to_insert,
            output |-> <<>>]>>

\* predicate over (State, State), with State extended to include the actual set
\* return "yes" if value is newly inserted
\* return "no" if it was already in the set
\* can always return "maybe"
DoInsert(st0, st1) ==
    \E i \in Inserters:
    /\ st0.pc[i] = "DoInsert"
    /\ LET val == st0.values_to_insert[i] IN
        /\ LET legal_output == {"maybe", IF val \notin st0.set THEN "yes" ELSE "no"} IN
            \E o \in legal_output: st1.output = (i :> o) @@ st0.output
        /\ st1.set = st0.set \union {val}
        /\ st1.pc = [st0.pc EXCEPT ![i] = "Done"]
        /\ st1.values_to_insert = st0.values_to_insert

\* Solve temporal existential \EE
Next ==
    /\ Len(log') = Len(log) + 1
    /\ Last(log) \in State
    /\ \E set_trace_tail \in [1..Len(log) -> SUBSET Values]:
       LET set_trace == <<{}>> \o set_trace_tail IN
        \A i \in 1..(Len(log) - 1):
         DoInsert(
            log[i] @@ ("set" :> set_trace[i]),
            log[i+1] @@ ("set" :> set_trace[i+1]))

Spec == Init /\ [][Next]_Vars

====
