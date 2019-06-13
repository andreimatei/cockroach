---------------------------- MODULE crdb_writes ----------------------------

EXTENDS TLC, Integers, FiniteSets

CONSTANT Servers
CONSTANT Values
CONSTANT Clients
CONSTANT ClockTicker
CONSTANT NULL

MsgTypes == { 
    "write",    
    "push",
    "commit" 
}

Range(f) == {f[x] : x \in DOMAIN f}
Timestamps == 0..2
MaxTimestamp == CHOOSE ts \in Timestamps : 
    \A other \in Timestamps : 
        other <= ts

ASSUME Cardinality(Servers) > 0
ASSUME Cardinality(Clients) = Cardinality(Servers)

ClientToServer == CHOOSE f \in [ Clients -> Servers ] : TRUE 

PrioritizePushes(set) ==
    LET
        pushes == { r \in set : r.type = "push"}
    IN
        IF pushes = {}
        THEN set
        ELSE pushes

IntentExists(store) ==
    \E k \in DOMAIN store : ~store[k][2]

GetIntent(store) ==
    CHOOSE k \in DOMAIN store : ~store[k][2]

(*--algorithm crdb

variables
    lease = CHOOSE s \in Servers : TRUE,
    storage = <<>>,
    requests = {},
    responses = {},
    clock = [ s \in Servers |-> 1 ],
    tsCache = [s \in Servers |-> 0 ],
    \* Set of timestamps corresponding to committed transactions
    committed = {};

process server \in Servers
variables
    msg = NULL;
begin
Run:
while \E c \in Clients : pc[c] /= "Done" do
Receive:
    await /\ lease = self;
    with
        req \in PrioritizePushes(requests)
    do
        msg := req ||
        requests := requests \ {req};
    end with;
PushClock:
    \* Push the clock to request header ts
    if clock[self] < msg.txn.ts then
        clock[self] := msg.txn.ts;
    end if;
EvalRequest:
    if msg.type = "write" then
        HandleWrite:
            if IntentExists(storage)
            then
                requests := requests \union {[
                    type |-> "push",
                    txn |-> msg.txn,
                    from |-> msg.from,
                    intent |-> GetIntent(storage)
                ]};
            else
                storage := msg.txn.ts :> <<msg.txn.value, FALSE>> @@ storage;
                responses := responses \union {[
                    to |-> msg.from
                ]}         
            end if;
    elsif msg.type = "push" then
        HandlePush:
            tsCache[self] := msg.intent;
            requests := requests \union {[
                type |-> "write",
                from |-> msg.from,
                txn |-> msg.txn
            ]};
            storage := [ ts \in (DOMAIN storage \ {msg.intent}) |-> storage[ts] ];                        
    else
        HandleCommit:
            storage := msg.txn.ts :> <<msg.txn.value, TRUE>> @@ storage
    end if;
end while;
end process;

process client \in Clients
variables
    client_txn \in [ts: {0}, value: Values]
begin
Begin:
    with 
        now = clock[ClientToServer[self]]
    do   
        client_txn.ts := now;
    end with;
SendWrite:
    requests := requests \union {[
        type |-> "write",
        from |-> self,
        txn |-> client_txn
    ]};
WaitForResponse:
    await \E resp \in responses : resp.to = self;
    with
        resp \in { r \in responses : r.to = self }
    do
        print resp;
        responses := responses \ {resp};
    end with;
SendCommit:
    requests := requests \union {[
        type |-> "commit",
        to |-> lease,
        from |-> self,
        txn |-> client_txn
    ]};
end process;

process clock_ticker = ClockTicker
begin
TickClocks:
    while (\E ts \in Range(clock) : ts < MaxTimestamp) do
        with
            s \in { s \in Servers : clock[s] < MaxTimestamp }
        do
            clock[s] := clock[s] + 1;
        end with;
    end while;
end process;
end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES lease, storage, requests, responses, clock, tsCache, committed, pc, 
          msg, client_txn

vars == << lease, storage, requests, responses, clock, tsCache, committed, pc, 
           msg, client_txn >>

ProcSet == (Servers) \cup (Clients) \cup {ClockTicker}

Init == (* Global variables *)
        /\ lease = (CHOOSE s \in Servers : TRUE)
        /\ storage = <<>>
        /\ requests = {}
        /\ responses = {}
        /\ clock = [ s \in Servers |-> 1 ]
        /\ tsCache = [s \in Servers |-> 0 ]
        /\ committed = {}
        (* Process server *)
        /\ msg = [self \in Servers |-> NULL]
        (* Process client *)
        /\ client_txn \in [Clients -> [ts: {0}, value: Values]]
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "Run"
                                        [] self \in Clients -> "Begin"
                                        [] self = ClockTicker -> "TickClocks"]

Run(self) == /\ pc[self] = "Run"
             /\ IF \E c \in Clients : pc[c] /= "Done"
                   THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << lease, storage, requests, responses, clock, 
                             tsCache, committed, msg, client_txn >>

Receive(self) == /\ pc[self] = "Receive"
                 /\ /\ lease = self
                 /\ \E req \in PrioritizePushes(requests):
                      /\ msg' = [msg EXCEPT ![self] = req]
                      /\ requests' = requests \ {req}
                 /\ pc' = [pc EXCEPT ![self] = "PushClock"]
                 /\ UNCHANGED << lease, storage, responses, clock, tsCache, 
                                 committed, client_txn >>

PushClock(self) == /\ pc[self] = "PushClock"
                   /\ IF clock[self] < msg[self].txn.ts
                         THEN /\ clock' = [clock EXCEPT ![self] = msg[self].txn.ts]
                         ELSE /\ TRUE
                              /\ clock' = clock
                   /\ pc' = [pc EXCEPT ![self] = "EvalRequest"]
                   /\ UNCHANGED << lease, storage, requests, responses, 
                                   tsCache, committed, msg, client_txn >>

EvalRequest(self) == /\ pc[self] = "EvalRequest"
                     /\ IF msg[self].type = "write"
                           THEN /\ pc' = [pc EXCEPT ![self] = "HandleWrite"]
                           ELSE /\ IF msg[self].type = "push"
                                      THEN /\ pc' = [pc EXCEPT ![self] = "HandlePush"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "HandleCommit"]
                     /\ UNCHANGED << lease, storage, requests, responses, 
                                     clock, tsCache, committed, msg, 
                                     client_txn >>

HandleWrite(self) == /\ pc[self] = "HandleWrite"
                     /\ IF IntentExists(storage)
                           THEN /\ requests' = (            requests \union {[
                                                    type |-> "push",
                                                    txn |-> msg[self].txn,
                                                    from |-> msg[self].from,
                                                    intent |-> GetIntent(storage)
                                                ]})
                                /\ UNCHANGED << storage, responses >>
                           ELSE /\ storage' = (msg[self].txn.ts :> <<msg[self].txn.value, FALSE>> @@ storage)
                                /\ responses' = (             responses \union {[
                                                     to |-> msg[self].from
                                                 ]})
                                /\ UNCHANGED requests
                     /\ pc' = [pc EXCEPT ![self] = "Run"]
                     /\ UNCHANGED << lease, clock, tsCache, committed, msg, 
                                     client_txn >>

HandlePush(self) == /\ pc[self] = "HandlePush"
                    /\ tsCache' = [tsCache EXCEPT ![self] = msg[self].intent]
                    /\ requests' = (            requests \union {[
                                        type |-> "write",
                                        from |-> msg[self].from,
                                        txn |-> msg[self].txn
                                    ]})
                    /\ storage' = [ ts \in (DOMAIN storage \ {msg[self].intent}) |-> storage[ts] ]
                    /\ pc' = [pc EXCEPT ![self] = "Run"]
                    /\ UNCHANGED << lease, responses, clock, committed, msg, 
                                    client_txn >>

HandleCommit(self) == /\ pc[self] = "HandleCommit"
                      /\ storage' = (msg[self].txn.ts :> <<msg[self].txn.value, TRUE>> @@ storage)
                      /\ pc' = [pc EXCEPT ![self] = "Run"]
                      /\ UNCHANGED << lease, requests, responses, clock, 
                                      tsCache, committed, msg, client_txn >>

server(self) == Run(self) \/ Receive(self) \/ PushClock(self)
                   \/ EvalRequest(self) \/ HandleWrite(self)
                   \/ HandlePush(self) \/ HandleCommit(self)

Begin(self) == /\ pc[self] = "Begin"
               /\ LET now == clock[ClientToServer[self]] IN
                    client_txn' = [client_txn EXCEPT ![self].ts = now]
               /\ pc' = [pc EXCEPT ![self] = "SendWrite"]
               /\ UNCHANGED << lease, storage, requests, responses, clock, 
                               tsCache, committed, msg >>

SendWrite(self) == /\ pc[self] = "SendWrite"
                   /\ requests' = (            requests \union {[
                                       type |-> "write",
                                       from |-> self,
                                       txn |-> client_txn[self]
                                   ]})
                   /\ pc' = [pc EXCEPT ![self] = "WaitForResponse"]
                   /\ UNCHANGED << lease, storage, responses, clock, tsCache, 
                                   committed, msg, client_txn >>

WaitForResponse(self) == /\ pc[self] = "WaitForResponse"
                         /\ \E resp \in responses : resp.to = self
                         /\ \E resp \in { r \in responses : r.to = self }:
                              /\ PrintT(resp)
                              /\ responses' = responses \ {resp}
                         /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                         /\ UNCHANGED << lease, storage, requests, clock, 
                                         tsCache, committed, msg, client_txn >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ requests' = (            requests \union {[
                                        type |-> "commit",
                                        to |-> lease,
                                        from |-> self,
                                        txn |-> client_txn[self]
                                    ]})
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << lease, storage, responses, clock, tsCache, 
                                    committed, msg, client_txn >>

client(self) == Begin(self) \/ SendWrite(self) \/ WaitForResponse(self)
                   \/ SendCommit(self)

TickClocks == /\ pc[ClockTicker] = "TickClocks"
              /\ IF (\E ts \in Range(clock) : ts < MaxTimestamp)
                    THEN /\ \E s \in { s \in Servers : clock[s] < MaxTimestamp }:
                              clock' = [clock EXCEPT ![s] = clock[s] + 1]
                         /\ pc' = [pc EXCEPT ![ClockTicker] = "TickClocks"]
                    ELSE /\ pc' = [pc EXCEPT ![ClockTicker] = "Done"]
                         /\ clock' = clock
              /\ UNCHANGED << lease, storage, requests, responses, tsCache, 
                              committed, msg, client_txn >>

clock_ticker == TickClocks

Next == clock_ticker
           \/ (\E self \in Servers: server(self))
           \/ (\E self \in Clients: client(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION


    
IsTxn(txn) == 
    /\ txn.ts \in Timestamps
    /\ txn.value \in Values
    
IsRequest(req) == 
    /\ req.type \in MsgTypes
    /\ IsTxn(req.txn)
    
IsResponse(req) ==
    /\ req.to \in Clients
    
ServerOk ==
    \A m \in Range(msg) : 
        \/ m = NULL 
        \/ IsRequest(m)

RequestsOk == \A req \in requests : IsRequest(req)

ResponsesOk == \A resp \in responses : IsResponse(resp)    

StorageOk ==
    \/ storage = <<>>
    \/ \A ts \in DOMAIN storage :
        /\ ts \in Timestamps
        /\ storage[ts] \in (Values \X BOOLEAN)
        
NothingIsCommitted == \A record \in Range(storage) : ~record[2]

StaysCommitted ==
    [][\A x \in DOMAIN storage:
        storage[x][2] => /\ x \in DOMAIN storage'
                         /\ storage[x] = (storage')[x]   
     ]_vars

CommittedOk == committed \subseteq Timestamps

OnlyOneIntent ==
    \A a, b \in DOMAIN storage :
        ~storage[a][2] /\ ~storage[b][2] => a = b

NoPartialCommit ==
    \A ts \in committed :
        /\ ts \in DOMAIN storage
        /\ storage[ts][2]    

=============================================================================
\* Modification History
\* Last modified Wed May 15 17:15:55 EDT 2019 by ajwerner
\* Created Wed May 15 13:18:23 EDT 2019 by ajwerner
