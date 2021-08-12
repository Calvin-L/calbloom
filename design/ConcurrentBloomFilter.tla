---- MODULE ConcurrentBloomFilter ----

EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS
    Inserters,
    Values,
    Cells,
    NumHashFunctions

(*

--algorithm Bloom {

    variables
        values_to_insert \in [Inserters -> Values];

        \* for correctness
        log = <<[
            pc |-> [i \in Inserters |-> "DoInsert"],
            values_to_insert |-> values_to_insert,
            output |-> <<>>]>>;

        output = << >>;

        \* not actually a var, but doing it this way lets us explore all possible
        \* sets of hash functions (as opposed to a constant, which would only let
        \* us check one per TLC run)
        hash_functions \in [1..NumHashFunctions -> [Values -> Cells]];

        bits = [c \in Cells |-> FALSE];

    process (inserter \in Inserters)
    variables
        is_new = FALSE;
        hashes = { hash_functions[i][values_to_insert[self]] : i \in DOMAIN hash_functions };
    {
        "insert_loop":
        while (hashes /= {}) {
            with (h \in hashes, oldbit = bits[h]) {
                bits[h] := TRUE;
                is_new := is_new \/ ~oldbit;
                hashes := hashes \ {h};
            };
        };

        "produce_output":
        with (prev = log[Len(log)]) {
            output := (self :> IF is_new THEN "yes" ELSE "maybe") @@ output;
            log := log \o <<[
                pc |-> [prev.pc EXCEPT ![self] = "Done"],
                values_to_insert |-> prev.values_to_insert,
                output |-> output]>>;
        };
    }

}

*)

\* BEGIN TRANSLATION
VARIABLES values_to_insert, log, output, hash_functions, bits, pc, is_new, 
          hashes

vars == << values_to_insert, log, output, hash_functions, bits, pc, is_new, 
           hashes >>

ProcSet == (Inserters)

Init == (* Global variables *)
        /\ values_to_insert \in [Inserters -> Values]
        /\ log =   <<[
                 pc |-> [i \in Inserters |-> "DoInsert"],
                 values_to_insert |-> values_to_insert,
                 output |-> <<>>]>>
        /\ output = << >>
        /\ hash_functions \in [1..NumHashFunctions -> [Values -> Cells]]
        /\ bits = [c \in Cells |-> FALSE]
        (* Process inserter *)
        /\ is_new = [self \in Inserters |-> FALSE]
        /\ hashes = [self \in Inserters |-> { hash_functions[i][values_to_insert[self]] : i \in DOMAIN hash_functions }]
        /\ pc = [self \in ProcSet |-> "insert_loop"]

insert_loop(self) == /\ pc[self] = "insert_loop"
                     /\ IF hashes[self] /= {}
                           THEN /\ \E h \in hashes[self]:
                                     LET oldbit == bits[h] IN
                                       /\ bits' = [bits EXCEPT ![h] = TRUE]
                                       /\ is_new' = [is_new EXCEPT ![self] = is_new[self] \/ ~oldbit]
                                       /\ hashes' = [hashes EXCEPT ![self] = hashes[self] \ {h}]
                                /\ pc' = [pc EXCEPT ![self] = "insert_loop"]
                           ELSE /\ pc' = [pc EXCEPT ![self] = "produce_output"]
                                /\ UNCHANGED << bits, is_new, hashes >>
                     /\ UNCHANGED << values_to_insert, log, output, 
                                     hash_functions >>

produce_output(self) == /\ pc[self] = "produce_output"
                        /\ LET prev == log[Len(log)] IN
                             /\ output' = (self :> IF is_new[self] THEN "yes" ELSE "maybe") @@ output
                             /\ log' =    log \o <<[
                                       pc |-> [prev.pc EXCEPT ![self] = "Done"],
                                       values_to_insert |-> prev.values_to_insert,
                                       output |-> output']>>
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << values_to_insert, hash_functions, bits, 
                                        is_new, hashes >>

inserter(self) == insert_loop(self) \/ produce_output(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Inserters: inserter(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

Symmetry == UNION {
    Permutations(Inserters),
    Permutations(Values),
    Permutations(Cells)}

Abstract == INSTANCE ConcurrentSetLog
RefinesAbstractSet == Abstract!Spec

NoMissedValues ==
    \A v \in Values:
      LET inserters_for_v == {i \in Inserters : values_to_insert[i] = v} IN
        ((inserters_for_v /= {}) /\ (\A i \in inserters_for_v: i \in DOMAIN output)) =>
          \E i \in Inserters: output[i] = "yes"

Interesting ==
    \/ FALSE
    \* \/ Len(log) = 1 + Cardinality(Inserters)
    \* \/ \E i \in DOMAIN log:
    \*     \E x \in DOMAIN log[i].output:
    \*      log[i].output[x] = "yes"
    \* \/ \E v \in Values:
    \*     /\ \E i \in Inserters: values_to_insert[i] = v
    \*     /\ \A i \in Inserters:
    \*      (values_to_insert[i] = v) =>
    \*      (i \in DOMAIN output /\ output[i] \in {"maybe", "no"})

Debug == ~Interesting

====
