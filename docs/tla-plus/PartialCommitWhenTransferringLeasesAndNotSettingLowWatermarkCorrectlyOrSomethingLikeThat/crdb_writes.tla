---------------------------- MODULE crdb_writes ----------------------------

EXTENDS TLC, Integers, FiniteSets

CONSTANT Servers
CONSTANT Values
CONSTANT Clients
CONSTANT ClockTicker
CONSTANT NULL
CONSTANT LeaseTransferrer
CONSTANT Ranges

(*

The bug in mind is a partial commit bug whereby 

The biggest reason to do this is so that
    PushTxn requests properly update their receiver's clock. This is critical
    because a PushTxn request can result in a timestamp cache entry to be
    created with a value up to this time, so for safety, we need to ensure
    that the leaseholder updates its clock at least to this time _before_
    evaluating the request. Otherwise, a lease transfer could miss the
    request's effect on the timestamp cache and result in a lost push/abort.


1) Txn A sends writes for an intent (r1, n1) and txn record (r2, n2) at ts 200
2) Intent gets written to (r1, n1)@200
3) Txn B sends write to (r1,n1)@150 and run into intent A leading to a push abort
4) Push request goes to (r2, n2) and succeeds because there is no txn record
   it populates the write tscache with 200 but it does not bump the clock on n2
5) Txn B removes the intent A on (r1, n1)
6) Lease transfer from (r2, n2) -> (r2, n3) and n2 and n3's clocks are below 200
   leading to a write tscache low watermark below 200.
7) Txn record A arrives is redirected to (r2, n3) and is written succesfully at 200
8) Txn A commits despite having had its intent removed (partial commit).

*)

Range(f) == {f[x] : x \in DOMAIN f}

Max(set) == CHOOSE elem \in set : 
    \A other \in set : 
        other <= elem

MsgTypes == {
    "begin",
    "write",
    "push",
    "commit" 
}

Timestamps == 0..2        
MaxTimestamp == Max(Timestamps)

NumTransfers == 1

ASSUME Cardinality(Ranges) >= 2
ASSUME Cardinality(Servers) > 0
ASSUME Cardinality(Clients) = Cardinality(Servers)

ClientToServer == CHOOSE f \in [ Clients -> Servers ] : TRUE 

\*PrioritizePushes(set) ==
\*    LET
\*        pushes == { r \in set : r.type = "push"}
\*    IN
\*        IF pushes = {}
\*        THEN set
\*        ELSE pushes

IntentExists(store) ==
    \E k \in DOMAIN store : ~store[k][2]

GetIntent(store) ==
    CHOOSE k \in DOMAIN store : ~store[k][2]
   

(*--algorithm crdb

variables
    leases = CHOOSE f \in [Ranges -> Servers] : TRUE,
    storage = <<>>,
    requests = [Ranges |-> {}],
    responses = {},
    clock = [ s \in Servers |-> 1 ],
    tsCache = [r \in Ranges |-> 0 ],
    \* Set of timestamps corresponding to committed transactions
    committed = {};

macro bumpTsCache(s, ts)
begin
    if tsCache[s] < ts then
        tsCache[s] := ts
    end if
end macro

macro bumpClock(s, ts)
begin
    if clock[s] < ts then
        clock[s] := ts
    end if
end macro

process server \in Servers
variables
    msg = NULL;
begin
Run:
while \E c \in Clients : pc[c] /= "Done" do
Receive:
    await \E r \in Ranges :
        /\ leases[r] = self
        /\ Cardinality(requests[r]) > 0;
    with
        r \in { r \in Ranges :  leases[r] = self}, 
        req \in requests[r]
    do
        msg := req ||
        requests[r] := requests[r] \ {req};
    end with;
    bumpClock(self, msg.ts);
EvalRequest:
    if msg.type = "write" then
        HandleWrite:
            if IntentExists(r, storage)
            then
                with 
                    intent = GetIntent(r, storage)
                do
                    \* The bug is about putting a timestamp in the header
                    \* of this message.
                    requests := requests \union {[
                        type |-> "push",
                        ts |-> 0, \* !!!
                        from |-> msg.from,
                        intent |-> intent
                    ]};
                end with;
            elsif \E ts \in DOMAIN storage : ts >= msg.txn.ts
            then
                    responses := responses \union {[
                        to |-> msg.from,
                        error |-> "WriteTooOld"
                    ]}
            else
                storage := msg.txn.ts :> <<msg.txn.value, FALSE>> @@ storage;
                responses := responses \union {[
                        to |-> msg.from,
                        error |-> NULL
                ]}
            end if;
\*    elsif msg.type = "push" then
\*        HandlePush:
\*            tsCache[self] := msg.intent;
\*            requests := requests \union {[
\*                type |-> "write",
\*                from |-> msg.from,
\*                txn |-> msg.txn
\*            ]};
\*            storage := [ ts \in (DOMAIN storage \ {msg.intent}) |-> storage[ts] ];                        
\*    else
\*        HandleCommit:
\*            if msg.txn.ts > tsCache[self] then
\*                assert /\ msg.txn.ts \in DOMAIN storage
\*                       /\ ~storage[msg.txn.ts][2];
\*                storage := msg.txn.ts :> <<msg.txn.value, TRUE>> @@ storage;
\*                committed := committed \union {msg.txn.ts}
\*            end if
\*    end if;
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
WaitForWriteResponse:
    await \E resp \in responses : resp.to = self;
    with
        resp \in { r \in responses : r.to = self }
    do
        if resp.error = "WriteTooOld"
        then
            goto Done;
        else 
            responses := responses \ {resp};
        end if;
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

process lease_transferrer = LeaseTransferrer
variables
    transfers = 0
begin
TransferLease:
    while transfers < NumTransfers do
        with
            s \in Servers
        do
            bumpTsCache(s, clock[lease]);
            bumpClock(s, clock[lease]+1);
            leases := s;
            transfers :=  transfers + 1;
        end with;
    end while;
end process;

end algorithm;
*)


\* BEGIN TRANSLATION
VARIABLES leases, storage, requests, responses, clock, tsCache, committed, pc, 
          msg, client_txn, transfers

vars == << leases, storage, requests, responses, clock, tsCache, committed, 
           pc, msg, client_txn, transfers >>

ProcSet == (Servers) \cup (Clients) \cup {ClockTicker} \cup {LeaseTransferrer}

Init == (* Global variables *)
        /\ leases = (CHOOSE f \in [Ranges -> Servers] : TRUE)
        /\ storage = <<>>
        /\ requests = [Ranges |-> {}]
        /\ responses = {}
        /\ clock = [ s \in Servers |-> 1 ]
        /\ tsCache = [r \in Ranges |-> 0 ]
        /\ committed = {}
        (* Process server *)
        /\ msg = [self \in Servers |-> NULL]
        (* Process client *)
        /\ client_txn \in [Clients -> [ts: {0}, value: Values]]
        (* Process lease_transferrer *)
        /\ transfers = 0
        /\ pc = [self \in ProcSet |-> CASE self \in Servers -> "Run"
                                        [] self \in Clients -> "Begin"
                                        [] self = ClockTicker -> "TickClocks"
                                        [] self = LeaseTransferrer -> "TransferLease"]

Run(self) == /\ pc[self] = "Run"
             /\ IF \E c \in Clients : pc[c] /= "Done"
                   THEN /\ pc' = [pc EXCEPT ![self] = "Receive"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << leases, storage, requests, responses, clock, 
                             tsCache, committed, msg, client_txn, transfers >>

Receive(self) == /\ pc[self] = "Receive"
                 /\   \E r \in Ranges :
                    /\ leases[r] = self
                    /\ Cardinality(requests[r]) > 0
                 /\ \E r \in { r \in Ranges :  leases[r] = self}:
                      \E req \in requests[r]:
                        /\ msg' = [msg EXCEPT ![self] = req]
                        /\ requests' = [requests EXCEPT ![r] = requests[r] \ {req}]
                 /\ IF clock[self] < (msg'[self].txn.ts)
                       THEN /\ clock' = [clock EXCEPT ![self] = msg'[self].txn.ts]
                       ELSE /\ TRUE
                            /\ clock' = clock
                 /\ pc' = [pc EXCEPT ![self] = "EvalRequest"]
                 /\ UNCHANGED << leases, storage, responses, tsCache, 
                                 committed, client_txn, transfers >>

EvalRequest(self) == /\ pc[self] = "EvalRequest"
                     /\ TRUE
                     /\ pc' = [pc EXCEPT ![self] = "Run"]
                     /\ UNCHANGED << leases, storage, requests, responses, 
                                     clock, tsCache, committed, msg, 
                                     client_txn, transfers >>

server(self) == Run(self) \/ Receive(self) \/ EvalRequest(self)

Begin(self) == /\ pc[self] = "Begin"
               /\ LET now == clock[ClientToServer[self]] IN
                    client_txn' = [client_txn EXCEPT ![self].ts = now]
               /\ pc' = [pc EXCEPT ![self] = "SendWrite"]
               /\ UNCHANGED << leases, storage, requests, responses, clock, 
                               tsCache, committed, msg, transfers >>

SendWrite(self) == /\ pc[self] = "SendWrite"
                   /\ requests' = (            requests \union {[
                                       type |-> "write",
                                       from |-> self,
                                       txn |-> client_txn[self]
                                   ]})
                   /\ pc' = [pc EXCEPT ![self] = "WaitForWriteResponse"]
                   /\ UNCHANGED << leases, storage, responses, clock, tsCache, 
                                   committed, msg, client_txn, transfers >>

WaitForWriteResponse(self) == /\ pc[self] = "WaitForWriteResponse"
                              /\ \E resp \in responses : resp.to = self
                              /\ \E resp \in { r \in responses : r.to = self }:
                                   IF resp.error = "WriteTooOld"
                                      THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                           /\ UNCHANGED responses
                                      ELSE /\ responses' = responses \ {resp}
                                           /\ pc' = [pc EXCEPT ![self] = "SendCommit"]
                              /\ UNCHANGED << leases, storage, requests, clock, 
                                              tsCache, committed, msg, 
                                              client_txn, transfers >>

SendCommit(self) == /\ pc[self] = "SendCommit"
                    /\ requests' = (            requests \union {[
                                        type |-> "commit",
                                        to |-> lease,
                                        from |-> self,
                                        txn |-> client_txn[self]
                                    ]})
                    /\ pc' = [pc EXCEPT ![self] = "Done"]
                    /\ UNCHANGED << leases, storage, responses, clock, tsCache, 
                                    committed, msg, client_txn, transfers >>

client(self) == Begin(self) \/ SendWrite(self)
                   \/ WaitForWriteResponse(self) \/ SendCommit(self)

TickClocks == /\ pc[ClockTicker] = "TickClocks"
              /\ IF (\E ts \in Range(clock) : ts < MaxTimestamp)
                    THEN /\ \E s \in { s \in Servers : clock[s] < MaxTimestamp }:
                              clock' = [clock EXCEPT ![s] = clock[s] + 1]
                         /\ pc' = [pc EXCEPT ![ClockTicker] = "TickClocks"]
                    ELSE /\ pc' = [pc EXCEPT ![ClockTicker] = "Done"]
                         /\ clock' = clock
              /\ UNCHANGED << leases, storage, requests, responses, tsCache, 
                              committed, msg, client_txn, transfers >>

clock_ticker == TickClocks

TransferLease == /\ pc[LeaseTransferrer] = "TransferLease"
                 /\ IF transfers < NumTransfers
                       THEN /\ \E s \in Servers:
                                 /\ IF tsCache[s] < (clock[lease])
                                       THEN /\ tsCache' = [tsCache EXCEPT ![s] = clock[lease]]
                                       ELSE /\ TRUE
                                            /\ UNCHANGED tsCache
                                 /\ IF clock[s] < (clock[lease]+1)
                                       THEN /\ clock' = [clock EXCEPT ![s] = clock[lease]+1]
                                       ELSE /\ TRUE
                                            /\ clock' = clock
                                 /\ leases' = s
                                 /\ transfers' = transfers + 1
                            /\ pc' = [pc EXCEPT ![LeaseTransferrer] = "TransferLease"]
                       ELSE /\ pc' = [pc EXCEPT ![LeaseTransferrer] = "Done"]
                            /\ UNCHANGED << leases, clock, tsCache, transfers >>
                 /\ UNCHANGED << storage, requests, responses, committed, msg, 
                                 client_txn >>

lease_transferrer == TransferLease

Next == clock_ticker \/ lease_transferrer
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

RequestsOk == \A r \in DOMAIN requests :
    /\ r \in Ranges
    /\ \A req \in requests[r] : IsRequest(req)

ResponsesOk == \A resp \in responses : IsResponse(resp)
 
WrittenValueOk == Clients \X Timestamps

TxnRecordOk == Clients \X BOOLEAN 

IsTxnRecord(r) == r \in TxnRecordOk

IsWrittenValue(r) == r \in WrittenValueOk

StoredValueOk == TxnRecordOk \/ WrittenValueOk

StorageOk == 
    \/ \A r \in DOMAIN storage :
       /\ r \in Ranges
       /\ \A s \in storage[r] :
            s \in StoredValueOk

NoPartialCommits ==
    \/ \A r \in DOMAIN storage :
        \A txn \in { x \in storage[r] : IsTxnRecord(x) } :
            txn[2] => 
                \E r2 \in (DOMAIN storage \ r) :
                 \E val \in { x \in storage[r2] : IsWrittenValue(x) } :
                    val[1] = txn[1]
                   

=============================================================================
\* Modification History
\* Last modified Thu Jun 13 12:36:24 EDT 2019 by ajwerner
\* Created Wed May 15 13:18:23 EDT 2019 by ajwerner
