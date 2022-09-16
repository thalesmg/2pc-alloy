module twophasecommit_ideal

sig Value {}

/* abstract sig Vote {} */
/* one sig Yep extends Vote {} */
/* one sig Nope extends Vote {} */
enum Vote {Yep, Nope}

sig Node {
   var val: one Value,
   var leader: lone TransactionCoordinator,
   var proposed: lone Value,
   var voted: lone Vote
}
sig TransactionCoordinator in Node {
   var proposals_sent: set Node,
   var responses_recv: Vote -> Node
}

fact init {
   some TransactionCoordinator
   // each TC is its own leader
   all tc: TransactionCoordinator | tc.leader = tc
   no proposed
   all n: Node - TransactionCoordinator | no n.leader
   no proposals_sent
   no voted
   no responses_recv
}

pred stutter {
   val' = val
   leader' = leader
   proposed' = proposed
   proposals_sent' = proposals_sent
   voted' = voted
   responses_recv' = responses_recv
}

pred send_proposal[tc: TransactionCoordinator, v: Value, n : Node] {
   // this node has not received a prepare request yet, or its the same TC
   /* no n.leader or n.leader = tc */
   // nope... TCs can't know that when sending!

   // this TC has not contacted this node yet
   n not in tc.proposals_sent

   tc.val = v
   /* tc.proposed' = v */
   proposals_sent' = proposals_sent + tc->n

   /* leader' = leader + n->tc */
   no n.leader =>   leader' = leader + n->tc
               else leader' = leader
   proposed' = proposed + n->v + tc->v
   val' = val
   voted' = voted
   responses_recv' = responses_recv
}

pred send_response[tc: TransactionCoordinator, vote: Vote, n : Node] {
   // this node has not yet voted
   no n.voted
   // this node must have received a proposal
   /* some n.proposed and some n.leader */
   n in tc.proposals_sent
   n not in Vote.(tc.responses_recv)

   tc = n.leader => {
     n.voted' = vote
     responses_recv' = responses_recv + tc->vote->n
   } else {
      n.voted' = n.voted
      responses_recv' = responses_recv + tc->Nope->n
   }

   leader' = leader
   val' = val
   proposed' = proposed
   proposals_sent' = proposals_sent
   all m : Node - n | m.voted' = m.voted
}

pred send_decision_abort[tc: TransactionCoordinator, n: Node] {
   all m : Node | some tc.responses_recv.m
   some m : Node | tc.responses_recv.m = Nope

   leader' = leader
   val' = val
   tc = n.leader =>   proposed' = proposed - n->Value
                 else proposed' = proposed
   voted' = voted
   proposals_sent' = proposals_sent
   responses_recv' = responses_recv
}

pred send_decision_commit[tc: TransactionCoordinator, n: Node] {
   all m : Node | tc.responses_recv.m = Yep
   some n.proposed

   tc = n.leader => {
     n.val' = n.proposed
     all m : Node - n | {
        m.val' = m.val
     }
     proposed' = proposed - n->Value
   } else {
     val' = val
     proposed' = proposed
   }

   leader' = leader
   voted' = voted
   proposals_sent' = proposals_sent
   responses_recv' = responses_recv
}

fact step {
   always (
     stutter or
     (some v: Value, n : Node, tc: TransactionCoordinator | send_proposal[tc, v, n]) or
     (some vote: Vote, n : Node, tc: TransactionCoordinator | send_response[tc, vote, n]) or
     (some n : Node, tc: TransactionCoordinator | send_decision_abort[tc, n]) or
     (some n : Node, tc: TransactionCoordinator | send_decision_commit[tc, n])
   )
}

pred fairness {
   all tc: TransactionCoordinator, n: Node | {
      (eventually historically (n not in tc.proposals_sent)) => (always eventually some v: Value | send_proposal[tc, v, n])
      (eventually always (n in tc.proposals_sent)) => (always eventually some v: Vote | send_response[tc, v, n])
   }
}

pred ReachesConclusion {
   eventually {
     some tc: TransactionCoordinator | Node = tc.proposals_sent
     all m : Node | some tc: TransactionCoordinator | some tc.responses_recv.m
     no proposed
   }
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

check ReachesConclusion for 1..15 steps
check CommitMeansAgreement

run example {
   #TransactionCoordinator = 2
   #Node = 3
   /* eventually ReachesConclusion */
   /* eventually some tc: TransactionCoordinator, n: Node, v: Value | send_proposal[tc, v, n] */
} for 1..20 steps

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
