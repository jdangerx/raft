-------------------------------- MODULE main --------------------------------
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS Servers, NULL

States == {"follower", "candidate", "leader"}

(*--algorithm main
variables
    vote_requests = [s \in Servers |-> NULL],
    append_entries = [s \in Servers |-> NULL],
    vote_responses = [s \in Servers |-> NULL],
    append_responses = [s \in Servers |-> NULL];
    
define
EligibleVoters == {s \in Servers: vote_requests[s] = NULL}
end define;

process server \in Servers
variable
  state = "follower",
  term = 0,
  leader = NULL,
  voted_for = NULL,
  num_votes_for_me = 0,
  entries = <<>>;
begin
Follower:
  \* heartbeat
  if append_entries[self] /= NULL then
    if append_entries[self].term < term then
      append_responses[self] := [term |-> term, success |-> FALSE]; 
      append_entries[self] := NULL;
    else \* the heartbeat is legitimate
      term := append_entries[self].term;
      leader := append_entries[self].source;
      \* append entries
      \* respond with term and success
      goto Follower;
    end if;
  end if;
  \* vote request
  CheckVoteRequets:
  if vote_requests[self] /= NULL then
    skip; 
    \* vote_responses[self] := [term |-> term, voteGranted |-> FALSE]
  end if;
  either
    goto Follower;
  or
    goto Candidate;
  end either;
  \* if we get a vote request, look at it.
  \* if vote request is valid, respond and remain follower
  \* if we get a heartbeat, look at it.
  \* if it's valid, remain follower ("goto follower") (and set leader to leader)
  \* either stay follower, or, goto candidate
Candidate:
  state := "candidate";
  term := term + 1;
  voted_for := self;
  num_votes_for_me := 1; \* resetting if we time out and decide to re-run
  RequestVotes:
  while Cardinality(EligibleVoters \ { self }) > 0 do
    \* candidate magically knows who's already voted, then only sends to non-voters  
    SendVoteRequest:
      with voter \in EligibleVoters do
        vote_requests[voter] := [term |-> term, candidateId |-> self];
      end with;
  end while;
  
  \* await votes
  \* vote for self
  \* send requests for votes
  \* handle responses from other servers
    \* if term is higher, go to follower
    \* if we got the majority of votes, go to leader.
    \* if not, either: go to candidate, or, decrement term and go to candidate ("wait")
  either
    goto Candidate;
  
  skip;
Leader:
  state := "leader";
  \* send heartbeat
  \* if response has higher term: goto follower
  skip;
  
end process;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES vote_requests, append_entries, vote_responses, append_responses, pc

(* define statement *)
EligibleVoters == {s \in Servers: vote_requests[s] = NULL}

VARIABLES state, term, leader, voted_for, num_votes_for_me, entries

vars == << vote_requests, append_entries, vote_responses, append_responses, 
           pc, state, term, leader, voted_for, num_votes_for_me, entries >>

ProcSet == (Servers)

Init == (* Global variables *)
        /\ vote_requests = [s \in Servers |-> NULL]
        /\ append_entries = [s \in Servers |-> NULL]
        /\ vote_responses = [s \in Servers |-> NULL]
        /\ append_responses = [s \in Servers |-> NULL]
        (* Process server *)
        /\ state = [self \in Servers |-> "follower"]
        /\ term = [self \in Servers |-> 0]
        /\ leader = [self \in Servers |-> NULL]
        /\ voted_for = [self \in Servers |-> NULL]
        /\ num_votes_for_me = [self \in Servers |-> 0]
        /\ entries = [self \in Servers |-> <<>>]
        /\ pc = [self \in ProcSet |-> "Follower"]

Follower(self) == /\ pc[self] = "Follower"
                  /\ IF append_entries[self] /= NULL
                        THEN /\ IF append_entries[self].term < term[self]
                                   THEN /\ append_responses' = [append_responses EXCEPT ![self] = [term |-> term[self], success |-> FALSE]]
                                        /\ append_entries' = [append_entries EXCEPT ![self] = NULL]
                                        /\ pc' = [pc EXCEPT ![self] = "CheckVoteRequets"]
                                        /\ UNCHANGED << term, leader >>
                                   ELSE /\ term' = [term EXCEPT ![self] = append_entries[self].term]
                                        /\ leader' = [leader EXCEPT ![self] = append_entries[self].source]
                                        /\ pc' = [pc EXCEPT ![self] = "Follower"]
                                        /\ UNCHANGED << append_entries, 
                                                        append_responses >>
                        ELSE /\ pc' = [pc EXCEPT ![self] = "CheckVoteRequets"]
                             /\ UNCHANGED << append_entries, append_responses, 
                                             term, leader >>
                  /\ UNCHANGED << vote_requests, vote_responses, state, 
                                  voted_for, num_votes_for_me, entries >>

CheckVoteRequets(self) == /\ pc[self] = "CheckVoteRequets"
                          /\ IF vote_requests[self] /= NULL
                                THEN /\ TRUE
                                ELSE /\ TRUE
                          /\ \/ /\ pc' = [pc EXCEPT ![self] = "Follower"]
                             \/ /\ pc' = [pc EXCEPT ![self] = "Candidate"]
                          /\ UNCHANGED << vote_requests, append_entries, 
                                          vote_responses, append_responses, 
                                          state, term, leader, voted_for, 
                                          num_votes_for_me, entries >>

Candidate(self) == /\ pc[self] = "Candidate"
                   /\ state' = [state EXCEPT ![self] = "candidate"]
                   /\ term' = [term EXCEPT ![self] = term[self] + 1]
                   /\ voted_for' = [voted_for EXCEPT ![self] = self]
                   /\ num_votes_for_me' = [num_votes_for_me EXCEPT ![self] = 1]
                   /\ pc' = [pc EXCEPT ![self] = "RequestVotes"]
                   /\ UNCHANGED << vote_requests, append_entries, 
                                   vote_responses, append_responses, leader, 
                                   entries >>

RequestVotes(self) == /\ pc[self] = "RequestVotes"
                      /\ IF Cardinality(EligibleVoters \ { self }) > 0
                            THEN /\ pc' = [pc EXCEPT ![self] = "SendVoteRequest"]
                            ELSE /\ IF Cardinality({s \in Servers: vote_responses[s] /= NULL}) > 0
                                       THEN /\ TRUE
                                       ELSE /\ TRUE
                                 /\ TRUE
                                 /\ pc' = [pc EXCEPT ![self] = "Leader"]
                      /\ UNCHANGED << vote_requests, append_entries, 
                                      vote_responses, append_responses, state, 
                                      term, leader, voted_for, 
                                      num_votes_for_me, entries >>

SendVoteRequest(self) == /\ pc[self] = "SendVoteRequest"
                         /\ \E voter \in EligibleVoters:
                              vote_requests' = [vote_requests EXCEPT ![voter] = [term |-> term[self], candidateId |-> self]]
                         /\ pc' = [pc EXCEPT ![self] = "RequestVotes"]
                         /\ UNCHANGED << append_entries, vote_responses, 
                                         append_responses, state, term, leader, 
                                         voted_for, num_votes_for_me, entries >>

Leader(self) == /\ pc[self] = "Leader"
                /\ state' = [state EXCEPT ![self] = "leader"]
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << vote_requests, append_entries, vote_responses, 
                                append_responses, term, leader, voted_for, 
                                num_votes_for_me, entries >>

server(self) == Follower(self) \/ CheckVoteRequets(self) \/ Candidate(self)
                   \/ RequestVotes(self) \/ SendVoteRequest(self)
                   \/ Leader(self)

Next == (\E self \in Servers: server(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

TypeInvariant ==
  /\ \A s \in Servers: state[s] \in States
  /\ Cardinality({s \in Servers: state[s] = "leader"}) <= 1

  
=============================================================================
\* Modification History
\* Last modified Wed Dec 05 15:58:03 EST 2018 by john
\* Created Tue Dec 04 17:40:33 EST 2018 by john
