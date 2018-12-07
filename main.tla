-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Servers, MaxMsgs, NULL

CONSTANTS FOLLOWER, CANDIDATE, LEADER



Range(fn) == {fn[i]:  i \in DOMAIN fn}

(*--algorithm main
variables
  vote_responses = [s \in Servers |-> {}],
  vote_requests = [s \in Servers |-> {}]; \* [dest1 |-> { msg1, msg2 }]

define
  ValidVoteRequest(current_term, voted_for, msg) ==
      /\ current_term <= msg.term
      /\ (voted_for = NULL \/ voted_for = msg.source) 
end define;

macro vote_response(target, message) begin
  vote_responses[target] := 
    vote_responses[target] \union {[source |-> self] @@ message};
  end if;
end macro;

macro start_election() begin
  current_term := current_term + 1;
  voted_for := self;
  votes_for_me := 1;
  vote_requests := [
    s \in Servers \ {self} |-> 
      vote_requests[s] \union {[source |-> self, term |-> current_term]}
  ] @@ vote_requests
end macro;

process server \in Servers
variables
  current_term = 0,
  server_role = FOLLOWER,
  voted_for = NULL,
  votes_for_me = 0;
begin
Follower:
  await server_role = FOLLOWER;
  HandleVoteRequests:
  while Cardinality(vote_requests[self]) > 0 do
    with msg \in vote_requests[self] do
        if ValidVoteRequest(current_term, voted_for, msg) then
          current_term := msg.term;
          voted_for := msg.source;
        end if;     
        vote_response(
          msg.source,
          [ term |-> current_term
          , vote_granted |-> ValidVoteRequest(current_term, voted_for, msg)]
        )
    end with;
  end while;
  \* handle append entries heartbeat
  \* if valid heartbeat: go back to follower label; no timeout.
  
  either
    goto Follower; \* no timeout
  or
    server_role := CANDIDATE; \* timed out, seize power
    start_election();
    goto Candidate;
  end either;
Candidate:
  await server_role = CANDIDATE;
  HandleVoteResponses:
  while Cardinality(vote_responses[self]) > 0 do
    with msg \in vote_responses[self] do
      if msg.term > current_term then
        current_term := msg.term;
        server_role := FOLLOWER;
        goto Follower;        
      elsif msg.vote_granted then
        votes_for_me := votes_for_me + 1;
        if votes_for_me * 2 > Cardinality(Servers) then
          server_role := LEADER;
          goto Leader;
        end if;
      end if;
    end with;
  end while;
  either
    goto Candidate; \* no timeout
  or
    start_election(); \* timeout, start a new election
    goto Candidate;
  end either;
Leader:
  await server_role = LEADER;
  LeaderHandleVoteRequests:
  while Cardinality(vote_requests[self]) > 0 do
    with msg \in vote_requests[self] do
      if msg.term > current_term then
        current_term := msg.term;
        server_role := FOLLOWER;
        goto Follower;
      end if;
    end with;
  end while;
  skip;
end process;

end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES vote_responses, vote_requests, pc

(* define statement *)
ValidVoteRequest(current_term, voted_for, msg) ==
    /\ current_term <= msg.term
    /\ (voted_for = NULL \/ voted_for = msg.source)

VARIABLES current_term, server_role, voted_for, votes_for_me

vars == << vote_responses, vote_requests, pc, current_term, server_role, 
           voted_for, votes_for_me >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ vote_responses = [s \in Servers |-> {}]
        /\ vote_requests = [s \in Servers |-> {}]
        (* Process server *)
        /\ current_term = [self \in Servers |-> 0]
        /\ server_role = [self \in Servers |-> FOLLOWER]
        /\ voted_for = [self \in Servers |-> NULL]
        /\ votes_for_me = [self \in Servers |-> 0]
        /\ pc = [self \in ProcSet |-> "Follower"]

Follower(self) == /\ pc[self] = "Follower"
                  /\ server_role[self] = FOLLOWER
                  /\ pc' = [pc EXCEPT ![self] = "HandleVoteRequests"]
                  /\ UNCHANGED << vote_responses, vote_requests, current_term, 
                                  server_role, voted_for, votes_for_me >>

HandleVoteRequests(self) == /\ pc[self] = "HandleVoteRequests"
                            /\ IF Cardinality(vote_requests[self]) > 0
                                  THEN /\ \E msg \in vote_requests[self]:
                                            /\ IF ValidVoteRequest(current_term[self], voted_for[self], msg)
                                                  THEN /\ current_term' = [current_term EXCEPT ![self] = msg.term]
                                                       /\ voted_for' = [voted_for EXCEPT ![self] = msg.source]
                                                  ELSE /\ TRUE
                                                       /\ UNCHANGED << current_term, 
                                                                       voted_for >>
                                            /\ vote_responses' = [vote_responses EXCEPT ![(msg.source)] = vote_responses[(msg.source)] \union {[source |-> self] @@ ([ term |-> current_term'[self]
                                                                                                                                                                     , vote_granted |-> ValidVoteRequest(current_term'[self], voted_for'[self], msg)])}]
                                       /\ pc' = [pc EXCEPT ![self] = "HandleVoteRequests"]
                                       /\ UNCHANGED << vote_requests, 
                                                       server_role, 
                                                       votes_for_me >>
                                  ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "Follower"]
                                             /\ UNCHANGED <<vote_requests, current_term, server_role, voted_for, votes_for_me>>
                                          \/ /\ server_role' = [server_role EXCEPT ![self] = CANDIDATE]
                                             /\ current_term' = [current_term EXCEPT ![self] = current_term[self] + 1]
                                             /\ voted_for' = [voted_for EXCEPT ![self] = self]
                                             /\ votes_for_me' = [votes_for_me EXCEPT ![self] = 1]
                                             /\ vote_requests' =                  [
                                                                   s \in Servers \ {self} |->
                                                                     vote_requests[s] \union {[source |-> self, term |-> current_term'[self]]}
                                                                 ] @@ vote_requests
                                             /\ pc' = [pc EXCEPT ![self] = "Candidate"]
                                       /\ UNCHANGED vote_responses

Candidate(self) == /\ pc[self] = "Candidate"
                   /\ server_role[self] = CANDIDATE
                   /\ pc' = [pc EXCEPT ![self] = "HandleVoteResponses"]
                   /\ UNCHANGED << vote_responses, vote_requests, current_term, 
                                   server_role, voted_for, votes_for_me >>

HandleVoteResponses(self) == /\ pc[self] = "HandleVoteResponses"
                             /\ IF Cardinality(vote_responses[self]) > 0
                                   THEN /\ \E msg \in vote_responses[self]:
                                             IF msg.term > current_term[self]
                                                THEN /\ current_term' = [current_term EXCEPT ![self] = msg.term]
                                                     /\ server_role' = [server_role EXCEPT ![self] = FOLLOWER]
                                                     /\ pc' = [pc EXCEPT ![self] = "Follower"]
                                                     /\ UNCHANGED votes_for_me
                                                ELSE /\ IF msg.vote_granted
                                                           THEN /\ votes_for_me' = [votes_for_me EXCEPT ![self] = votes_for_me[self] + 1]
                                                                /\ IF votes_for_me'[self] * 2 > Cardinality(Servers)
                                                                      THEN /\ server_role' = [server_role EXCEPT ![self] = LEADER]
                                                                           /\ pc' = [pc EXCEPT ![self] = "Leader"]
                                                                      ELSE /\ pc' = [pc EXCEPT ![self] = "HandleVoteResponses"]
                                                                           /\ UNCHANGED server_role
                                                           ELSE /\ pc' = [pc EXCEPT ![self] = "HandleVoteResponses"]
                                                                /\ UNCHANGED << server_role, 
                                                                                votes_for_me >>
                                                     /\ UNCHANGED current_term
                                        /\ UNCHANGED << vote_requests, 
                                                        voted_for >>
                                   ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "Candidate"]
                                              /\ UNCHANGED <<vote_requests, current_term, voted_for, votes_for_me>>
                                           \/ /\ current_term' = [current_term EXCEPT ![self] = current_term[self] + 1]
                                              /\ voted_for' = [voted_for EXCEPT ![self] = self]
                                              /\ votes_for_me' = [votes_for_me EXCEPT ![self] = 1]
                                              /\ vote_requests' =                  [
                                                                    s \in Servers \ {self} |->
                                                                      vote_requests[s] \union {[source |-> self, term |-> current_term'[self]]}
                                                                  ] @@ vote_requests
                                              /\ pc' = [pc EXCEPT ![self] = "Candidate"]
                                        /\ UNCHANGED server_role
                             /\ UNCHANGED vote_responses

Leader(self) == /\ pc[self] = "Leader"
                /\ server_role[self] = LEADER
                /\ pc' = [pc EXCEPT ![self] = "LeaderHandleVoteRequests"]
                /\ UNCHANGED << vote_responses, vote_requests, current_term, 
                                server_role, voted_for, votes_for_me >>

LeaderHandleVoteRequests(self) == /\ pc[self] = "LeaderHandleVoteRequests"
                                  /\ IF Cardinality(vote_requests[self]) > 0
                                        THEN /\ \E msg \in vote_requests[self]:
                                                  IF msg.term > current_term[self]
                                                     THEN /\ current_term' = [current_term EXCEPT ![self] = msg.term]
                                                          /\ server_role' = [server_role EXCEPT ![self] = FOLLOWER]
                                                          /\ pc' = [pc EXCEPT ![self] = "Follower"]
                                                     ELSE /\ pc' = [pc EXCEPT ![self] = "LeaderHandleVoteRequests"]
                                                          /\ UNCHANGED << current_term, 
                                                                          server_role >>
                                        ELSE /\ TRUE
                                             /\ pc' = [pc EXCEPT ![self] = "Done"]
                                             /\ UNCHANGED << current_term, 
                                                             server_role >>
                                  /\ UNCHANGED << vote_responses, 
                                                  vote_requests, voted_for, 
                                                  votes_for_me >>

server(self) == Follower(self) \/ HandleVoteRequests(self)
                   \/ Candidate(self) \/ HandleVoteResponses(self)
                   \/ Leader(self) \/ LeaderHandleVoteRequests(self)

Next == (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

MaxTerm == CHOOSE x \in Range(current_term): \A y \in Range(current_term): x >= y

LatestTermHasAtMostOneLeader ==
  Cardinality({s \in Servers: current_term[s] = MaxTerm /\ server_role[s] = LEADER}) <= 1

  
=============================================================================
\* Modification History
\* Last modified Fri Dec 07 14:19:42 EST 2018 by john
\* Created Tue Dec 04 17:40:33 EST 2018 by john
