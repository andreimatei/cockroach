---- MODULE MC ----
EXTENDS crdb_writes, TLC

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
c1, c2, c3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
s1, s2, s3
----

\* MV CONSTANT declarations@modelParameterConstants
CONSTANTS
v1, v2
----

\* MV CONSTANT definitions Clients
const_155882897499152000 == 
{c1, c2, c3}
----

\* MV CONSTANT definitions Servers
const_155882897499153000 == 
{s1, s2, s3}
----

\* MV CONSTANT definitions Values
const_155882897499254000 == 
{v1, v2}
----

\* SPECIFICATION definition @modelBehaviorSpec:0
spec_155882897499255000 ==
Spec
----
\* INVARIANT definition @modelCorrectnessInvariants:0
inv_155882897499256000 ==
StorageOk
----
\* INVARIANT definition @modelCorrectnessInvariants:1
inv_155882897499257000 ==
RequestsOk
----
\* INVARIANT definition @modelCorrectnessInvariants:2
inv_155882897499258000 ==
ResponsesOk
----
\* INVARIANT definition @modelCorrectnessInvariants:3
inv_155882897499259000 ==
OnlyOneIntent
----
\* INVARIANT definition @modelCorrectnessInvariants:4
inv_155882897499260000 ==
NoPartialCommit
----
\* PROPERTY definition @modelCorrectnessProperties:0
prop_155882897499261000 ==
StaysCommitted
----
=============================================================================
\* Modification History
\* Created Sat May 25 20:02:54 EDT 2019 by ajwerner
