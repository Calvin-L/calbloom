---- MODULE ConcurrentBloomFilter ----

CONSTANTS
    Inserters,
    Values

VARIABLES
    pc,
    values_to_insert,
    output,
    set

(*

--algorithm Bloom {

    process (i \in Inserters)
    variables
        value_to_insert,
        output
    {
        "go":
        skip;
    }

}

*)

\* BEGIN TRANSLATION
\* END TRANSLATION

====
