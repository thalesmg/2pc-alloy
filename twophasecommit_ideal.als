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

pred send_proposal[v: Value, n : Node] {
   all tc : TransactionCoordinator | {
      n not in tc.proposals_sent
      tc.val = v
      tc.proposed' = v
      tc.proposals_sent' = tc.proposals_sent + n
   }

   proposed' = proposed + n->v
   val' = val
   voted' = voted
   responses_recv' = responses_recv
}

pred send_response[vote: Vote, n : Node] {
   // this node has not yet voted
   no n.voted
   // this node must have received a proposal
   some n.proposed

   n.voted' = vote
   all tc : TransactionCoordinator | {
      tc.responses_recv' = tc.responses_recv + vote->n
   }

   val' = val
   proposed' = proposed
   proposals_sent' = proposals_sent
   all m : Node - n | m.voted' = m.voted
}

pred send_decision_abort[n: Node] {
   all tc : TransactionCoordinator | {
      all m : Node | some tc.responses_recv.m
      some m : Node | tc.responses_recv.m = Nope
   }

   val' = val
   proposed' = proposed - n->Value
   voted' = voted
   proposals_sent' = proposals_sent
   responses_recv' = responses_recv
}

pred send_decision_commit[n: Node] {
   all tc : TransactionCoordinator | {
      /* all m : Node | some tc.responses_recv.m */
      all m : Node | tc.responses_recv.m = Yep
   }
   some n.proposed

   n.val' = n.proposed
   all m : Node - n | {
      m.val' = m.val
   }
   proposed' = proposed - n->Value

   voted' = voted
   proposals_sent' = proposals_sent
   responses_recv' = responses_recv
}

fact step {
   always (
     stutter or
     (some v: Value, n : Node | send_proposal[v, n]) or
     (some vote: Vote, n : Node | send_response[vote, n]) or
     (some n : Node | send_decision_abort[n]) or
     (some n : Node | send_decision_commit[n])
   )
}

pred fairness {
   all tc: TransactionCoordinator, n: Node | {
      (eventually historically (n not in tc.proposals_sent)) => (eventually some v: Value | send_proposal[v, n])
      (eventually always (n in tc.proposals_sent)) => (eventually some v: Vote | send_response[v, n])
      (eventually always (n in Vote.(tc.responses_recv))) => (eventually (send_decision_abort[n] or send_decision_commit[n]))
   }
}

pred ReachesConclusion {
   /* eventually { */
     Node = TransactionCoordinator.proposals_sent
     all m : Node | some TransactionCoordinator.responses_recv.m
     no proposed
   /* } */
}

pred Commited {
   ReachesConclusion
   all m : Node | m.voted = Yep
}

assert ReachesConclusion {
   fairness => ReachesConclusion
}

assert CommitMeansAgreement {
   fairness => {
      ReachesConclusion
      Commited
      all disj n1, n2 : Node | n1.val = n2.val
   }
}

check ReachesConclusion for 3 but 1..15 steps
check CommitMeansAgreement

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
