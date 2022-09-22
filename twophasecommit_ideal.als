module twophasecommit_ideal

sig Value {}

/* abstract sig Vote {} */
/* one sig Yep extends Vote {} */
/* one sig Nope extends Vote {} */
enum Vote {Yep, Nope}

sig Node {
   var val: one Value,
   var proposed: lone Value,
   var voted: lone Vote
}
one sig TransactionCoordinator in Node {
   var proposals_sent: set Node,
   var responses_recv: Vote -> Node
}

fact init {
   no proposed
   no proposals_sent
   no voted
   no responses_recv
}

pred stutter {
   val' = val
   proposed' = proposed
   proposals_sent' = proposals_sent
   voted' = voted
   responses_recv' = responses_recv
}

pred send_proposal[tc: TransactionCoordinator, v: Value, n : Node] {
   // precondition: this node did not receive a proposal yet
   n not in tc.proposals_sent

   // effect
   tc.val = v
   tc.proposed' = v
   tc.proposals_sent' = tc.proposals_sent + n
   proposed' = proposed + n->v

   // frame conditions
   val' = val
   voted' = voted
   responses_recv' = responses_recv
}

pred send_response[tc: TransactionCoordinator, vote: Vote, n : Node] {
   // preconditions
   no n.voted
   some n.proposed

   // effect
   n.voted' = vote
   tc.responses_recv' = tc.responses_recv + vote->n

   // frame conditions
   val' = val
   proposed' = proposed
   proposals_sent' = proposals_sent
   all m : Node - n | m.voted' = m.voted
}

pred send_decision_abort[tc: TransactionCoordinator, n: Node] {
   // preconditions
   all m : Node | some tc.responses_recv.m
   some m : Node | tc.responses_recv.m = Nope

   // effect
   val' = val
   proposed' = proposed - n->Value

   // frame conditions
   voted' = voted
   proposals_sent' = proposals_sent
   responses_recv' = responses_recv
}

pred send_decision_commit[tc: TransactionCoordinator, n: Node] {
   // preconditions
   all m : Node | tc.responses_recv.m = Yep
   some n.proposed

   // effect
   n.val' = n.proposed
   all m : Node - n | {
      m.val' = m.val
   }
   proposed' = proposed - n->Value

   // frame conditions
   voted' = voted
   proposals_sent' = proposals_sent
   responses_recv' = responses_recv
}

fact step {
   always (
     stutter or
     (some v: Value, n : Node, tc: TransactionCoordinator |
        send_proposal[tc, v, n]) or
     (some vote: Vote, n : Node, tc: TransactionCoordinator |
        send_response[tc, vote, n]) or
     (some n: Node, tc: TransactionCoordinator |
        send_decision_abort[tc, n]) or
     (some n: Node, tc: TransactionCoordinator |
        send_decision_commit[tc, n])
   )
}

pred fairness {
   all tc: TransactionCoordinator, n: Node | {
      (eventually historically (n not in tc.proposals_sent))
        => (eventually some v: Value, tc: TransactionCoordinator |
            send_proposal[tc, v, n])
      (eventually always (n in tc.proposals_sent))
        => (eventually some v: Vote, tc: TransactionCoordinator |
            send_response[tc, v, n])
      (eventually always (n in Vote.(tc.responses_recv)))
        => (eventually some tc: TransactionCoordinator |
            (send_decision_abort[tc, n] or send_decision_commit[tc, n]))
   }
}

pred ReachesConclusion {
   Node = TransactionCoordinator.proposals_sent
   all m : Node | some TransactionCoordinator.responses_recv.m
   no proposed
}

pred Commited {
   ReachesConclusion
   all m : Node | m.voted = Yep
}

assert ReachesConclusion0 {
   eventually ReachesConclusion
}

assert ReachesConclusion {
   fairness => eventually ReachesConclusion
}

assert CommitMeansAgreement {
   Commited => all disj n1, n2 : Node | n1.val = n2.val
}

check ReachesConclusion0 for 3 but 1..15 steps
check ReachesConclusion for 3 but 1..15 steps
check CommitMeansAgreement for 3 but 1..15 steps

run example0 {
   #Node > 1
}

run example {
   #Node > 1
   eventually ReachesConclusion
}

/* run commit_example { */
/*    #Node > 1 */
/*    /\* WRONG!!! makes the send be simultaneous for all nodes... *\/ */
/*    eventually (all n : Node | send_decision_commit[n]) */
/* } for 3 but 1..10 steps */

run same_votes {
   #Node > 1
   eventually (all n : Node | some v : Vote | TransactionCoordinator.responses_recv.n = v)
}

run commit_example {
   #Node > 1
   eventually {
      ReachesConclusion
      all m : Node | m.voted = Yep
   }
}

run abort_example {
   #Node > 1
   eventually {
      ReachesConclusion
      some m : Node | m.voted = Nope
   }
}
