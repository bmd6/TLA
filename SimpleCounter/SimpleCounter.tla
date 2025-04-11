-------------------- MODULE SimpleCounter --------------------

EXTENDS Naturals, Integers  \* Import standard modules for numbers
                            \* Includes definitions for numbers like the set Not (0,1,2,..) and Int (...-1,0,1...)

CONSTANTS Procs             \* The set of processes accessing the counter
                            \* Declares constant Procs, with the actual value defined in the model configuration.
                            \* This represents the set of entities that can interact with the system.

VARIABLES counter     \* The shared counter variable

vars == <<counter>>         \* Tuple of variables (useful for fairness/stuttering)
                            \* A convenience definition grouping of variables. Used in Spec for stuttering
                            \* ([][Next]_vars) and fairness (WF_vars(Next))


\* Define the initial state: counter starts at 0.
Init == counter = 0

\* Define the action for a process 'p' to increment the counter.
\* This action is enabled only if 'p' is in the set of processes.
Increment(p) == /\ p \in Procs
                /\ counter' = counter + 1 \* The next state of counter

\* Define the next-state relation.
\* A step consists of *some* process 'p' executing the Increment action.
Next == \E p \in Procs : Increment(p)

\* Define the complete specification.
\* It starts in Init and always takes a Next step or stutters (keeps vars unchanged).
\* We also add Weak Fairness (WF) on the Next action globally. This means
\* if it's always possible for *some* process to increment, eventually one will.
\* A more fine-grained fairness would be WF per process action.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)  \* Defines the temporal logic formula describing the allowed behaviors
                                                \* of the system.
                                                    \* - Init: Behavior must start in a state satisfying Init
                                                    \* - [][Next]_vars: Always ([]) either the next state satisfies
                                                    \*      the Next relation or the variables (vars) remain unchanged
                                                    \*      (this is the stuttering part of _vars)
                                                    \* - WF_vars(Next): Weak Fairness on the Next action. If the Next
                                                    \*      action (meaning some process can increment) is continuously
                                                    \*      enabled from some point onwards, it must eventually be taken.
                                                    \*      This prevents the system from halting arbitrarily if 
                                                    \*      increments are always possible.

\* ---- Properties to check ----

\* TypeOK Invariant: The counter should always  be a natural number (non-negative integer).
TypeOK == counter \in Nat       \* Defines an invariant. This predicate should be true in all reachable states of the
                                \*  system if the specification is correct regarding this property. Not is the 
                                \*  set (0, 1, 2, ...)

==============================================================