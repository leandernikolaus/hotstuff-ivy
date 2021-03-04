------------------------------ MODULE hotstuff ------------------------------
EXTENDS Integers, FiniteSets, TLAPS, NaturalsInduction, Tree

(***************************************************************************)
(* Constants: CNodes correct nodes, FNodes faulty nodes                    *)
(***************************************************************************)
CONSTANT CNodes, FNodes, Quorums

Nodes == CNodes \cup FNodes

(***************************************************************************)
(* Quorum Assumption                                                       *)
(* - Quorums are sets of nodes                                             *)
(* - Two quorums intersect in a correct node                               *)
(* - The set of quorums is subset closed                                   *)
(* - The set of all nodes is a quorum                                      *)
(***************************************************************************)
ASSUME QuorumAssumption == 
            /\ \A Q \in Quorums : Q \subseteq Nodes
            /\ \A Q1, Q2 \in Quorums : \E n \in CNodes: n \in (Q1 \cap Q2)
            /\ \A Q \in Quorums: \A S \in SUBSET Nodes: 
                                Q \subseteq S => S \in Quorums
            /\ Nodes \in Quorums

(***************************************************************************)
(* votes stores the votes for every block, i.e.  which node has signed a   *)
(* block.                                                                  *)
(* lock is the locked block for every node                                 *)
(* max is the max signed block for every node                              *)
(***************************************************************************)
VARIABLE votes, lock, max

vars == <<round, parent, votes, lock, max>>

TypeOK == /\ round \in [Blocks -> Rounds]
          /\ parent \in [Blocks -> Blocks]
          /\ votes \in [Blocks -> SUBSET Nodes]
          /\ lock \in [Nodes -> Blocks]
          /\ max \in [Nodes -> Rounds]

(***************************************************************************)
(* Initially all blocks but genesis have round -1.                         *)
(* All blocks are their own parent.                                        *)
(* No block is voted for, except genesis.                                  *)
(* All nodes voted for the genesis block.                                  *)
(***************************************************************************)

Init == /\ lock = [n \in Nodes |-> gen]
        /\ max = [n \in Nodes |-> 0]
        /\ round = [[b \in Blocks |-> -1] EXCEPT ![gen]=0]
        /\ parent = [b \in Blocks |-> b]
        /\ votes = [[b \in Blocks |-> {}] EXCEPT ![gen]=Nodes]

(***************************************************************************)
(* A proposed block is a block in the tree, i.e. round > -1                *)
(***************************************************************************)
Proposed(b) == /\ b \in Blocks
               /\ round[b] /= -1

(***************************************************************************)
(* A block is confirmed if a quorum of nodes voted for the block,          *)
(* i.e. it has a certificate.                                              *)
(***************************************************************************)
Confirmed(b) == /\ Proposed(b)
                /\ votes[b] \in Quorums
 
(***************************************************************************)
(* The propose action adds a new block to the tree.                        *)
(* The parent must be confirmed,                                           *)
(* the new block gets a round larger than that of his parent.              *)
(***************************************************************************)
propose(b,p,r) == /\ round' = [round EXCEPT ![b] = r]
                  /\ parent' = [parent EXCEPT ![b] = p]
        
Propose(b,p,r) == /\ b \in Blocks 
                  /\ ~ Proposed(b)
                  /\ Confirmed(p)
                  /\ r > round[p]
                  /\ propose(b,p,r)
                  /\ UNCHANGED <<lock, max, votes>>

(***************************************************************************)
(* Vote models one node voting (or signing) a block.                       *)
(* The max and lock variables for the node are adjusted.                   *)
(***************************************************************************)
vote(n,b) == /\ max' = [max EXCEPT ![n] = round[b]]
             /\ votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
             /\ IF round[parent[parent[b]]] > round[lock[n]]
                    (*******************************************************)
                    (* If the grandbarent of the new signed block has a    *)
                    (* larger round than the current lock, the lock is     *)
                    (* updated.                                            *)
                    (*******************************************************) 
                    THEN lock' = [lock EXCEPT ![n] = parent[parent[b]]]
                ELSE lock' = lock  

Vote(n,b) == /\ Proposed(b)
             /\ n \in Nodes
             /\ \/ n \notin CNodes
                (***********************************************************)
                (* Below are the rules on signing, but they apply only to  *)
                (* correct nodes.                                          *)
                (***********************************************************)
                \/ /\ round[b] > max[n]
                   (********************************************************)
                   (* Below is the updated rule for simplified hotstuff.   *)
                   (********************************************************) 
                   /\ round[lock[n]] <= round[parent[b]]
                   (********************************************************)
                   (* The rule from original hotstuff includes the         *)
                   (* Ancestor predicate.                                  *)
                   (********************************************************)
                   \* /\ \/ Ancestor(lock[n],b) \* safety rule 
                   \*    \/ round[lock[n]] < round[parent[b]] \* lifeness rule
             /\ vote(n,b)
             /\ UNCHANGED <<round, parent>>
             
Next == \/ \E b,p \in Blocks: \E r \in Rounds: Propose(b,p,r)
        \/ \E b \in Blocks: \E n \in Nodes: Vote(n,b)
        
Spec == Init /\ [][Next]_vars
                      
(***************************************************************************)
(* Chain specifies that blocks from b to c form a 2-chain                  *)
(***************************************************************************)
chain(b,c) == /\ parent[parent[c]] = b
              /\ round[c] <= round[parent[c]] + 1
              /\ round[parent[c]] <= round[b] + 1

(***************************************************************************)
(* A block is committed if it is the start of a 2-chain, and the last node *)
(* in the 2-chain is confirmed.                                            *)
(***************************************************************************)                      
Committed(b) == \E c \in Blocks:
               /\ chain(b,c)
               /\ Confirmed(c)
               
(***************************************************************************)
(* Correct, is the main safety property.                                   *)
(* It shows that, for committed b, at rounds larger than b,                *)
(* only descendants of b can be confirmed.                                 *)
(*                                                                         *)
(* We prove Correct, by proving that iCorrect holds for all i,             *)
(* using induction over i.                                                 *)
(***************************************************************************)
cci(b,c,i) == /\ Committed(b)
              /\ Confirmed(c)
              /\ round[b] + i = round[c]


        
iCorrect(i) == \A b, c \in Blocks: 
               cci(b,c,i)
               => Ancestor(b,c)

cc(b,c) == /\ Committed(b)
           /\ Confirmed(c)
           /\ round[b] <= round[c]
            
Correct ==  \A b, c \in Blocks: 
               cc(b,c)
               => Ancestor(b,c)
               
               
Safe == \A b,c \in Blocks: Committed(b) /\ Committed(c) 
                        => Ancestor(c,b) \/ Ancestor(b,c)




(****************************************************************************
The inductive invariant is the conjunction of the following parts.

IConf: The parent of a proposed block is confirmed.
IPrepared: Nodes only vote for proposed blocks (blocks in the tree)
IPr: Blocks are either their own parent (genesis and unproposed blocks)
    or the parent has a lower round.
IPx: Blocks, that are their own parent have round 0 or -1
IMax, ILockMax, ILock: Max and Lock are correctly set on correct nodes
IVote: Ensures that votes from correct nodes follow rule 2
IVote2: Ensures that votes from correct nodes follow rule 1 
****************************************************************************)
IConf == \A b \in Blocks: Proposed(b) => Confirmed(parent[b])
IPrepared == \A b \in Blocks: \A n \in CNodes: n \in votes[b] => Proposed(b)
\* Different from IPR defined in Tree.tla
IPr == \A b \in Blocks: parent[b] = b \/ round[parent[b]] < round[b]
IPx == \A b \in Blocks: parent[b] = b => round[b] \in {0, -1}
IMax == \A n \in CNodes: \A b \in Blocks: n \in votes[b] => max[n] >= round[b]     
ILockMax == \A n \in CNodes: round[lock[n]] <= max[n] /\ Proposed(lock[n])
ILock == \A n \in CNodes: \A b \in Blocks: n \in votes[b] => round[lock[n]] >= round[parent[parent[b]]]

IVote == \A b,c \in Blocks: \A n \in CNodes:
        /\ n \in votes[b]
        /\ n \in votes[c]
        /\ round[b] <= round[c]
        => round[parent[parent[b]]] <= round[parent[c]]

IVote2 == \A b,c \in Blocks: \A n \in CNodes:
        /\ n \in votes[b]
        /\ n \in votes[c]
        /\ round[b] = round[c]
        => b = c

Inv ==  /\ TypeOK
        /\ IVote
        /\ IVote2
        /\ IConf
        /\ IPr
        /\ IPx
        /\ IMax
        /\ ILockMax
        /\ ILock
        /\ IPrepared


diff(c,b) == round[c] - round[b]




LEMMA ExistsI == TypeOK => (\A b,c \in Blocks: cc(b,c) <=> \E i \in Nat: cci(b,c,i))
  <1> SUFFICES ASSUME TypeOK,
                      NEW b \in Blocks, NEW c \in Blocks
               PROVE  cc(b,c) <=> \E i \in Nat: cci(b,c,i)
    OBVIOUS
  <1>1. round[b] \in Nat \cup{-1}
    BY DEF TypeOK, Rounds
  <1>2. round[c] \in Nat \cup{-1}
    BY DEF TypeOK, Rounds
  <1>3. \E i \in Nat: round[b] + i = round[c] => round[b] <= round[c] 
    BY <1>1, <1>2
  <1>4. round[b] <= round[c] => round[c] - round[b] \in Nat
    BY <1>1, <1>2
  <1>5. round[b] <= round[c] => diff(c,b) \in Nat
    BY <1>4 DEF diff
  <1>6. round[b] + diff(c,b) = round[c]
    BY <1>1, <1>2 DEF diff
  <1>7. round[b] <= round[c] => \E i \in Nat: round[b] + i = round[c]
    BY <1>5, <1>6
  <1> QED
    BY <1>4, <1>7 DEF cc,cci, Rounds, TypeOK
  
LEMMA CommittedConfirmed == TypeOK /\ IConf => \A b \in Blocks: Committed(b) => Confirmed(b)
  BY DEF TypeOK, Committed, chain, IConf, Confirmed

LEMMA InductionStart == TypeOK /\ IConf /\ IVote2 => \A b,c \in Blocks: cci(b,c,0) => Ancestor(b,c)
  <1> SUFFICES ASSUME TypeOK /\ IConf /\ IVote2,
                      NEW b \in Blocks, NEW c \in Blocks,
                      cci(b,c,0)
               PROVE  Ancestor(b,c)
    OBVIOUS
  <1>1. Confirmed(b)
    BY CommittedConfirmed DEF cci
  <1>2. Confirmed(c)
    BY DEF cci
  <1>3. \E n \in CNodes: n \in votes[b] \cap votes[c] 
    BY <1>1, <1>2, QuorumAssumption DEF Confirmed
  <1>4. round[b] + 0 = round[c]
    BY cci(b,c,0) DEF cci
  <1>5. round[b] = round[c]
    BY <1>4 DEF TypeOK, Rounds
  <1>6. b=c
    BY IVote2, <1>3, <1>5 DEF IVote2
  <1>7. Ancestor(b,c)
   BY Anc1, <1>6
  <1>8 QED
    BY <1>7

LEMMA TwoConfirmed == IVote2 => (\A b,c \in Blocks: 
                                    /\ Confirmed(b)
                                    /\ Confirmed(c)
                                    /\ round[b] = round[c]
                                    => b = c)
  <1> SUFFICES ASSUME IVote2,
                      NEW b \in Blocks, NEW c \in Blocks,
                      /\ Confirmed(b)
                      /\ Confirmed(c)
                      /\ round[b] = round[c]
               PROVE  b = c
    OBVIOUS
  <1>1. \E n \in CNodes: n \in votes[b] \cap votes[c]
    BY QuorumAssumption DEF Confirmed
  <1> QED
    BY <1>1 DEF IVote2
  
   
LEMMA CanUseI == TypeOK => ((\A i \in Nat: iCorrect(i)) => Correct)
  <1> SUFFICES ASSUME TypeOK,
                      \A i \in Nat: iCorrect(i),
                      NEW b \in Blocks, NEW c \in Blocks,
                      cc(b,c)
               PROVE  Ancestor(b,c)
    BY DEF Correct
  <1>1. \E i \in Nat: cci(b,c,i)
    BY ExistsI
  <1>2. Ancestor(b,c)
    BY <1>1 DEF iCorrect
  <1> QED
    BY <1>2
  
LEMMA PTypeOK == TypeOK => PType
  BY DEF TypeOK, PType 

LEMMA IPHh == TypeOK /\ IPr => IPR
  <1> SUFFICES ASSUME IPr, TypeOK,
                      NEW b \in Blocks
               PROVE  round[parent[b]] <= round[b]
    BY DEF IPR
  <1>2. CASE round[parent[b]] < round[b]
    BY DEF IPr, TypeOK, Rounds
  <1>3. CASE parent[b] = b
    BY <1>3 DEF TypeOK, Rounds
  <1> QED
    BY <1>2, <1>3, IPr DEF IPr
  
LEMMA HTypeOK == TypeOK => RType
  BY DEF TypeOK, RType

THEOREM Spec => []Correct
<1>1. Init => Inv
  <2> SUFFICES ASSUME Init
               PROVE  Inv
    OBVIOUS
  <2> gen \in Blocks
    BY ExistsBlock DEF gen
  <2>0. \A b \in Blocks: Proposed(b) => b = gen
    BY DEF Init, Proposed
  <2>1. TypeOK
    <3>1. gen \in Blocks
      BY ExistsBlock DEF gen
    <3> QED
      BY <3>1 DEF Init, TypeOK, Rounds
  <2>2. IVote
    <3> SUFFICES ASSUME NEW b \in Blocks, NEW c \in Blocks,
                        NEW n \in CNodes,
                        /\ n \in votes[b]
                        /\ n \in votes[c]
                        /\ round[b] <= round[c]
                 PROVE  round[parent[parent[b]]] <= round[parent[c]]
      BY DEF IVote
    <3>1. b = gen
      BY DEF Init
    <3>2. c = gen
      BY DEF Init
    <3>3. parent[b] = gen
      BY <3>1 DEF Init
    <3>4. parent[c] = gen
      BY <3>2 DEF Init
    <3>5 parent[parent[b]] = gen
      BY <3>3, <2>1 DEF Init, TypeOK 
    <3>6 parent[parent[b]] = parent[c]
      BY <3>5, <3>4
    <3>7 round[parent[parent[b]]] = round[parent[c]]
      BY <3>6, <2>1 DEF TypeOK
    <3> QED
      BY <3>7, <2>1 DEF TypeOK, Rounds
    
  <2>3. IVote2
    <3> SUFFICES ASSUME NEW b \in Blocks, NEW c \in Blocks,
                        NEW n \in CNodes,
                        /\ n \in votes[b]
                        /\ n \in votes[c]
                        /\ round[b] = round[c]
                 PROVE  b = c
      BY DEF IVote2
    <3>1. b = gen
      BY DEF Init
    <3>2. c = gen
      BY DEF Init
    <3> QED
      BY <3>1, <3>2 DEF Init, Inv
    
  <2>4. IConf
    <3> SUFFICES ASSUME NEW b \in Blocks,
                        Proposed(b)
                 PROVE  Confirmed(parent[b])
      BY DEF IConf
    <3>1. b = gen
      BY <2>0
    <3>2. parent[b] = gen
      BY <3>1 DEF Init
    <3>3. Proposed(gen)
      BY <3>1
    <3>4. votes[gen] = Nodes
      BY DEF Init
    <3>5. Confirmed(gen)
      BY <3>3, <3>4, QuorumAssumption DEF Confirmed
    <3> QED
      BY <3>5, <3>2
    
  <2>5. IPr
      BY DEF Init, IPr
  <2>6. IPx
    BY DEF Init, IPx
  <2>7. IMax
    BY DEF Init, IMax
  <2>8. ILockMax
    BY DEF Init, ILockMax, Proposed, Nodes
  <2>9. ILock
    BY DEF Init, ILock, Nodes
  <2>10. IPrepared
    BY DEF Init, IPrepared, Proposed, Nodes
  <2>11. QED
    BY <2>1, <2>10, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8, <2>9 DEF Inv
  
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW b \in Blocks,
               NEW p \in Blocks,
               NEW h \in Rounds,
               Propose(b,p,h)
        PROVE  Inv'
    <3>0. UNCHANGED <<lock, max, votes>>
      BY Propose(b,p,h) DEF Propose
    <3>01. \A bb \in Blocks: Proposed(bb) => round[bb] = round'[bb]
      BY Propose(b,p,h) DEF Propose, propose
    <3>011. \A bb \in Blocks: bb /= b => round[bb] = round'[bb]
      BY Propose(b,p,h) DEF Propose, propose
    <3>02. \A bb \in Blocks: Proposed(bb) => parent[bb] = parent'[bb]
      BY Propose(b,p,h) DEF Propose, propose
    <3>021. \A bb \in Blocks: bb /= b => parent[bb] = parent'[bb]
      BY Propose(b,p,h) DEF Propose, propose
    <3>04. \A bb \in Blocks: Proposed(bb) => Proposed(bb)'
      BY <3>01 DEF Proposed
    <3>05. \A bb \in Blocks: Proposed(bb) => Proposed(parent[bb])
      BY DEF Inv, IConf, Confirmed 
    <3>03. propose(b,p,h)
      BY Propose(b,p,h) DEF Propose
    <3>1. TypeOK'
      BY <3>0, <3>03 DEF propose, Inv, TypeOK
    <3>2. IVote'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks', NEW c \in Blocks',
                          NEW n \in CNodes',
                          (/\ n \in votes[b_1]
                           /\ n \in votes[c]
                           /\ round[b_1] <= round[c])'
                   PROVE  (round[parent[parent[b_1]]] <= round[parent[c]])'
        BY DEF IVote
      <4>1. n \in votes[b_1] /\ n \in votes[c]
        BY <3>0
      <4>2. Proposed(b_1) /\ Proposed(c)
        BY <4>1 DEF Inv, IPrepared
      <4>3. round[b_1] <= round[c]
        BY <4>2, <3>01
      <4>4. round[parent[parent[b_1]]] <= round[parent[c]]
        BY IVote, <4>1, <4>3 DEF Inv, IVote
      <4> QED
        BY <4>4, <4>2, <3>05, <3>02, <3>01 DEF Proposed
    <3>3. IVote2'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks', NEW c \in Blocks',
                          NEW n \in CNodes',
                          (/\ n \in votes[b_1]
                           /\ n \in votes[c]
                           /\ round[b_1] = round[c])'
                   PROVE  (b_1 = c)'
        BY DEF IVote2
      <4> QED
        BY <3>0, IPrepared, <3>01, IVote2 DEF Inv, IPrepared, IVote2
    <3>4. IConf'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks',
                          Proposed(b_1)'
                   PROVE  Confirmed(parent[b_1])'
        BY DEF IConf
      <4>0. parent'[b_1] \in Blocks
        BY <3>1 DEF TypeOK
      <4>c1. CASE b_1 = b
        <5>0. Confirmed(p)
          BY Propose(b,p,h) DEF Propose
        <5>1. parent'[b] = p
          BY <3>03, <3>1 DEF propose, TypeOK
        <5>2. Proposed(p)
          BY <5>0 DEF Confirmed
        <5>3. Proposed(parent'[b])
          BY <5>1, <5>2
        <5>4. Proposed(parent[b])'
          BY <5>3, <3>04 DEF Proposed 
        <5>5. votes[p] \in Quorums
          BY <5>0 DEF Confirmed
        <5>6. votes[parent'[b]] \in Quorums
          BY <5>5, <5>1
        <5>7. (votes'[parent'[b]] \in Quorums)
          BY <5>6, <3>0
        <5>8. (votes[parent[b]] \in Quorums)'
          BY <5>7
        <5> QED
          BY <5>8, <5>4, <4>c1 DEF Confirmed
      <4>c2. CASE b_1 /= b
        <5>1. parent[b_1] = parent'[b_1]
          BY <3>03, <4>c2 DEF propose
        <5>21. Proposed(b_1)
          BY <4>c2, <3>011 DEF Proposed
        <5>2. Proposed(parent[b_1])
          BY <3>05, <5>21
        <5>3. Proposed(parent'[b_1])
          BY <5>1, <5>2
        <5>4. Proposed(parent[b_1])'
          BY <5>3, <3>04 DEF Proposed
        <5>5. votes[parent[b_1]] \in Quorums
          BY <5>21 DEF Confirmed, Inv, IConf
        <5>6. votes[parent'[b_1]] \in Quorums
          BY <5>5, <5>1
        <5>7. (votes'[parent'[b_1]] \in Quorums)
          BY <5>6, <3>0
        <5>8. (votes[parent[b_1]] \in Quorums)'
          BY <5>7
        <5> QED
          BY <5>8, <5>4 DEF Confirmed
      <4>3. QED
        BY <4>c1, <4>c2 DEF Confirmed
    <3>5. IPr'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks
                   PROVE  (parent[b_1] = b_1 \/ round[parent[b_1]] < round[b_1])'
        BY DEF IPr
      <4>1. CASE b_1 = b
        <5>1. round'[b] = h
          BY <3>03 DEF propose, Inv, TypeOK
        <5>2. h > round[p]
          BY Propose(b,p,h) DEF Propose
        <5>3. parent'[b] = p
          BY <3>03 DEF propose, Inv, TypeOK
        <5>4. Proposed(p)
          BY Propose(b,p,h) DEF Propose, Confirmed
        <5>5. round'[p] = round[p]
          BY <5>4, <3>01
        <5>6. round'[parent'[b]] = round[p]
          BY <5>5, <5>3, <3>1 DEF TypeOK, Inv
        <5>7. round'[parent'[b]] < round'[b]
          BY <5>6, <5>2, <5>1, <3>1 DEF Inv, TypeOK, Rounds
        <5>goal. (round[parent[b_1]] < round[b_1])'
          BY <5>7, <4>1
        <5> QED
          BY <5>goal
      <4>2. CASE b_1 /= b
        <5>0. parent[b_1] = b_1 \/ round[parent[b_1]] < round[b_1]
          BY DEF Inv, IPr
        <5>1. parent[b_1] = parent'[b_1] /\ round[b_1] = round'[b_1]
          BY <4>2, <3>011, <3>021
        <5>2. CASE parent[b_1] = b_1
          BY <5>1, <5>2
        <5>3. CASE round[parent[b_1]] < round[b_1]
          <6>1. round[b_1] /= -1
            BY <5>3 DEF Inv, TypeOK, Rounds
          <6>2. Proposed(b_1)
            BY <6>1 DEF Proposed
          <6>3. Proposed(parent[b_1])
            BY <3>05, <6>2
          <6>5. (round'[parent[b_1]] < round'[b_1])
            BY <6>3, <6>2, <5>3, <3>01 DEF Inv, TypeOK
          <6>6. (round[parent[b_1]] < round[b_1])'
            BY <6>2, <3>02, <6>5
          <6> QED
            BY <6>6
        <5> QED
          BY <5>0, <5>2, <5>3
      <4> QED
        BY <4>1, <4>2
    <3>6. IPx'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks',
                          (parent[b_1] = b_1)'
                   PROVE  (round[b_1] \in {0, -1})'
        BY DEF IPx
      <4>1. CASE b_1 /= b
        <5>1. parent'[b_1] = parent[b_1]
          BY <4>1, <3>021
        <5>2. round'[b_1] = round[b_1]
          BY <4>1, <3>011
        <5> QED
          BY <5>1, <5>2, IPx DEF Inv, IPx
      <4>2. b_1 /= b
        <5>1. ~Proposed(b)
          BY Propose(b,p,h) DEF Propose, Confirmed
        <5>2. parent'[b] = p
          BY <3>03 DEF propose, Inv, TypeOK
        <5>3. Proposed(p) 
          BY Propose(b,p,h) DEF Propose, Confirmed
        <5>4. b /= p
          BY <5>3, <5>1
        <5>5. parent'[b] /= b
          BY <5>2, <5>4
        <5> QED
          BY <5>5
      <4> QED
        BY <4>1, <4>2
    <3>7. IMax'
      <4> SUFFICES ASSUME NEW n \in CNodes',
                          NEW b_1 \in Blocks',
                          (n \in votes[b_1])'
                   PROVE  (max[n] >= round[b_1])'
        BY DEF IMax
      <4>1. Proposed(b_1)
        BY IPrepared, <3>0 DEF Inv, IPrepared
      <4> QED
        BY <3>0, <4>1, <3>01 DEF Inv, IMax
    <3>8. ILockMax'
      <4> SUFFICES ASSUME NEW n \in CNodes'
                   PROVE  (round[lock[n]] <= max[n])' /\ (Proposed(lock[n]))'
        BY DEF ILockMax
      <4>1. Proposed(lock[n])
        BY DEF Inv, ILockMax
      <4>2. (Proposed(lock[n]))' 
        BY <4>1, <3>0, <3>01 DEF Proposed
      <4>3. round[lock[n]] <= max[n]
        BY DEF Inv, ILockMax
      <4>4. (round[lock'[n]] <= max'[n])
        BY <3>0, <4>3
      <4>5. Proposed(lock'[n])
        BY <3>0, <4>1
      <4>6. (round'[lock'[n]] <= max'[n])
        BY <4>5, <3>01, <4>4, <3>1 DEF TypeOK, Nodes
      <4>7. (round[lock[n]] <= max[n])'
        BY <4>6
      <4> QED
        BY <4>6, <4>2
    <3>9. ILock'
      <4> SUFFICES ASSUME NEW n \in CNodes',
                          NEW b_1 \in Blocks',
                          (n \in votes[b_1])'
                   PROVE  (round[lock[n]] >= round[parent[parent[b_1]]])'
        BY DEF ILock
      <4>1. Proposed(b_1)
        BY <3>0 DEF Inv, IPrepared
      <4>2. Proposed(parent[b_1])
        BY <4>1, <3>05
      <4>21. parent[b_1] \in Blocks
        BY DEF Inv, TypeOK
      <4>3. Proposed(parent[parent[b_1]])
        BY <4>2, <4>21, <3>05
      <4>4. Proposed(lock[n])
        BY DEF Inv, ILockMax
      <4>5. round[lock[n]] >= round[parent[parent[b_1]]]
        BY <3>0 DEF ILock, Inv
      <4>6. round'[lock[n]] = round[lock[n]] 
        BY <3>01, <4>4, <3>1 DEF Inv, TypeOK
      <4>7. round'[lock[n]] >= round'[parent[parent[b_1]]]
        BY <3>01, <4>4, <3>1, <4>3, <4>5 DEF Inv, TypeOK
      <4>8. round'[lock'[n]] >= round'[parent[parent[b_1]]]
        BY <4>7, <3>0
      <4>9. round'[lock'[n]] >= round'[parent'[parent[b_1]]]
        BY <3>02, <4>2, <4>21, <4>8
      <4>10. round'[lock'[n]] >= round'[parent'[parent'[b_1]]]
        BY <3>02, <4>1, <4>9
      <4> QED
        BY <4>10
    <3>10. IPrepared'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks',
                          NEW n \in CNodes',
                          (n \in votes[b_1])'
                   PROVE  Proposed(b_1)'
        BY DEF IPrepared
      <4>1. Proposed(b_1) 
        BY <3>0 DEF Inv, IPrepared
      <4> QED
        BY <4>1, <3>04
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10 DEF Inv
  <2>2. ASSUME NEW b \in Blocks,
               NEW n \in Nodes,
               Vote(n,b)
        PROVE  Inv'
    <3>0. UNCHANGED <<round, parent>>
      BY Vote(n,b)  DEF Vote, Inv, TypeOK
    <3>01. \A bb \in Blocks: Confirmed(bb) => Confirmed(bb)'
      <4> SUFFICES ASSUME NEW bb \in Blocks,
                          Confirmed(bb)
                   PROVE  Confirmed(bb)'
        OBVIOUS
      <4>1. Proposed(bb)'
        BY <3>0 DEF Proposed, Confirmed
      <4>2. (votes[bb] \in Quorums)'
        <5>0. votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
          BY Vote(n,b) DEF Vote, vote
        <5>c1. CASE bb /= b
          <6>1. votes[bb] = votes'[bb]
            BY <5>0, <5>c1
          <6> QED
            BY <6>1 DEF Confirmed
        <5>c2. CASE bb = b
          <6>1. votes'[bb] = votes[bb] \cup {n}
            BY <5>0, <5>c2 DEF Inv, TypeOK
          <6>2. votes[bb] \in Quorums
            BY DEF Confirmed
          <6>3. votes'[bb] \in Quorums
            BY <6>2, <6>1, QuorumAssumption
          <6> QED
            BY <6>3
          
        <5> QED 
          BY <5>c1, <5>c2
      <4>3. QED
        BY <4>1, <4>2 DEF Confirmed
       
    <3>1. TypeOK'
      <4>1. (round \in [Blocks -> Rounds])'
        BY <3>0 DEF Inv, TypeOK
      <4>2. (parent \in [Blocks -> Blocks])'
        BY <3>0 DEF Inv, TypeOK
      <4>3. (votes \in [Blocks -> SUBSET Nodes])'
        BY Vote(n,b),votes' = [votes EXCEPT ![b] = votes[b]\cup {n}] DEF Vote, vote, Inv, TypeOK
      <4>4. (lock \in [Nodes -> Blocks])'
        <5>0. lock' = lock \/ lock' = [lock EXCEPT ![n] = parent[parent[b]]]
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>1. CASE lock' = lock
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>2. CASE lock' = [lock EXCEPT ![n] = parent[parent[b]]]
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>3. QED
          BY <5>0, <5>1, <5>2
      <4>5. (max \in [Nodes -> Rounds])'
        <5>1. max \in [Nodes -> Rounds]
          BY DEF Inv, TypeOK
        <5>2. max' = [max EXCEPT ![n] = round[b]]
          BY Vote(n,b) DEF Vote, vote
        <5>3. max' \in [Nodes -> Rounds]
          BY <5>1, <5>2 DEF Inv, TypeOK
        <5>4. QED
          BY <5>3
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF TypeOK     
    <3>2. IVote'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks', NEW c \in Blocks',
                          NEW n_1 \in CNodes',
                          (/\ n_1 \in votes[b_1]
                           /\ n_1 \in votes[c]
                           /\ round[b_1] <= round[c])'
                   PROVE  (round[parent[parent[b_1]]] <= round[parent[c]])'
        BY DEF IVote
      <4>1. CASE n_1 \in votes[b_1] /\ n_1 \in votes[c]
        <5>0. round[b_1] =< round[c]
          BY <3>0
        <5>1. round[parent[parent[b_1]]] =< round[parent[c]]
          BY n_1 \in votes[b_1] /\ n_1 \in votes[c], <5>0 DEF Inv, IVote
        <5>. QED
          BY <3>0, <5>1
      <4>2. CASE n_1 \in votes[b_1] /\ n_1 \notin votes[c]
        <5>0. votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
          BY Vote(n,b) DEF vote, Vote
        <5>1. c = b /\ n_1 = n
          BY <5>0, n_1 \in votes[b_1] /\ n_1 \notin votes[c], n_1 \in votes'[c]
        <5>2. round[lock[n]] <= round[parent[b]]
          BY <5>1, Vote(n,b), n \in CNodes DEF Vote
        <5>3. round[parent[parent[b_1]]] <= round[lock[n]]
          <6>0. n_1 \in CNodes
            OBVIOUS
          <6>1. n_1 \in votes[b_1]
            BY <4>2
          <6>3. round[parent[parent[b_1]]] <= round[lock[n_1]]
            BY <6>0, <6>1, ILock DEF Inv, ILock
          <6> QED
            BY <5>1, <6>3
        <5>goal. round[parent[parent[b_1]]] <= round[parent[b]]
          BY <5>3, <5>2 DEF Inv, TypeOK, Rounds
        <5> QED
          BY <5>goal, <3>0, <5>1
      <4>3. CASE n_1 \notin votes[b_1]
        <5>0. votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
          BY Vote(n,b) DEF vote, Vote
        <5>1. b_1 = b /\ n_1 = n
          BY <5>0, <4>3, n_1 \in votes'[b_1]
        <5>2. round[b_1] <= round[c]
          BY <3>0
        <5>3. max[n] < round[b_1]
          BY Vote(n,b), <5>1 DEF Vote
        <5>4. max[n] < round[c]
          BY <5>3, <5>2 DEF Inv, TypeOK, Rounds
        <5>5. ~(max[n] >= round[c])
          BY <5>4 DEF Inv, TypeOK, Rounds
        <5>6. n \notin votes[c]
          BY IMax, <5>5, <5>1, n \in CNodes DEF Inv, IMax
        <5>7. c = b
          BY <5>0, <5>1, n_1 \in votes'[c], <5>6
        <5>8. c = b_1
          BY <5>7, <5>1
        <5>goal. round[parent[parent[b_1]]] <= round[parent[c]]
          BY <5>8 DEF Inv, TypeOK, IPr, Rounds
        <5> QED
          BY <5>goal, <3>0
      <4> QED
        BY <4>1, <4>2, <4>3
      
    <3>3. IVote2'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks', NEW c \in Blocks',
                          NEW n_1 \in CNodes',
                          (/\ n_1 \in votes[b_1]
                           /\ n_1 \in votes[c]
                           /\ round[b_1] = round[c])'
                   PROVE  (b_1 = c)'
        BY DEF IVote2
      <4>c0. CASE n_1 \in votes[b_1] /\ n_1 \in votes[c]
        BY <3>0, <4>c0, IVote2 DEF Inv, IVote2
      <4>c1. CASE n_1 /= n
        <5>1. votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
          BY Vote(n,b) DEF Vote, vote
        <5>2. n_1 \in votes[b_1] /\ n_1 \in votes[c]
          BY <5>1, <4>c1
        <5> QED
          BY <5>2, <4>c0
      <4>c2. CASE n = n_1
        <5>1. votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
          BY Vote(n,b) DEF Vote, vote
        <5>c21. CASE round[b] <= round[c]
          <6>1. round[b] > max[n]
            BY Vote(n,b), <4>c2 DEF Vote
          <6>2. max[n] < round[c]
            BY <5>c21, <6>1 DEF Inv, TypeOK, Rounds
          <6>3. n \notin votes[c]
            BY IMax, <6>2, <4>c2 DEF Inv, TypeOK, IMax, Rounds
          <6>4. max[n] < round[b_1]
            BY <6>2, <3>0 DEF Inv, TypeOK, Rounds
          <6>5. n \notin votes[b_1]
            BY IMax, <6>4, <4>c2 DEF Inv, TypeOK, IMax, Rounds
          <6>6. c = b
            BY <6>3, <4>c2, <5>1
          <6>7. b_1 = b
            BY <6>5, <4>c2, <5>1
          <6> QED
            BY <6>6, <6>7
        <5>c22. CASE round[b] > round[c]
          <6>1. c /= b
            BY <5>c22
          <6>2. b_1 /= b
            BY <5>c22, <3>0
          <6>3. n_1 \in votes[b_1] /\ n_1 \in votes[c]
            BY <6>1, <6>2, <5>1
          <6> QED  
            BY <4>c0, <6>3
        <5> QED
          BY <5>c21, <5>c22 DEF Inv, TypeOK, Rounds
      <4> QED
        BY <4>c1, <4>c2
    <3>4. IConf'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks,
                          NEW b_2 \in Blocks,
                          b_2 = parent'[b_1],
                          Proposed(b_1)'  
                   PROVE  Confirmed(b_2)'
        BY <3>1 DEF IConf, TypeOK
      <4>1. b_2 = parent[b_1]
        BY <3>0
      <4>3. Proposed(b_1)
        BY <3>0 DEF Proposed
      <4>2. Confirmed(b_2)
        BY IConf, <4>1, <4>3 DEF Inv, IConf
      <4> QED
        BY <4>2, <3>01
    
    <3>5. IPr'
      BY Vote(n,b), UNCHANGED <<round, parent>> DEF Vote, Inv, IPr
    <3>6. IPx'
      BY <3>0 DEF Inv, IPx
    <3>7. IMax'
      <4> SUFFICES ASSUME NEW n_1 \in CNodes,
                          NEW b_1 \in Blocks,
                          n_1 \in votes'[b_1]
                   PROVE  max'[n_1] >= round'[b_1]
        BY DEF IMax
      <4>0. max' = [max EXCEPT ![n] = round[b]]
        BY Vote(n,b) DEF Vote, vote
      <4>1. CASE n_1 \in votes[b_1]
        <5>1. max[n_1] >= round[b_1]
          BY <4>1 DEF Inv, IMax
        <5>2. CASE n = n_1
          <6>1. max[n] < round[b]
            BY <5>2, n \in CNodes, Vote(n,b) DEF Vote
          <6>2. round[b_1] <= max[n]
            BY <5>1, <5>2
          <6>3. round[b_1] < round[b]
            BY <6>1, <6>2 DEF Inv, TypeOK, Rounds  
          <6>4. round'[b_1] < round[b]
            BY <3>0, <6>3
          <6>5. max'[n] = round[b]
            BY <4>0 DEF Inv, TypeOK
          <6> QED
            BY <6>4, <6>5, <5>2
        <5>3. CASE n /= n_1
          <6>1. max'[n_1] = max[n_1]
            BY <4>0, <5>3
          <6> QED
            BY <5>1, <6>1, <3>0
        <5> QED
          BY <5>2, <5>3
      <4>2. CASE n_1 \notin votes[b_1]
        <5>1. n= n_1 /\ b_1 = b
          BY <4>2, n_1 \in votes'[b_1], Vote(n,b) DEF Vote, vote
        <5>2. max'[n_1] = round[b_1]
          BY <4>0, <5>1, TypeOK' DEF TypeOK
        <5>goal. max'[n_1] = round'[b_1]
          BY <5>2, <3>0
        <5> QED
          BY <5>goal, TypeOK' DEF TypeOK, Rounds

      <4> QED
        BY <4>1, <4>2
    <3>8. ILockMax'
      <4> SUFFICES ASSUME NEW n_1 \in CNodes'
                   PROVE  (round[lock[n_1]] <= max[n_1])' /\ (Proposed(lock[n_1]))'
        BY DEF ILockMax
      <4>0. lock' = [lock EXCEPT ![n] = parent[parent[b]]] \/ lock' = lock
        BY Vote(n,b) DEF Vote, vote
      <4>p. (Proposed(lock[n_1]))'
        <5>1. lock'[n_1] = lock[n_1] \/ lock'[n_1] = parent[parent[b]]
          <6>1. CASE lock' = lock
            BY <6>1, <3>1 DEF Inv, TypeOK
          <6>2. CASE lock' = [lock EXCEPT ![n] = parent[parent[b]]]
            BY <6>2, <3>1 DEF Inv, TypeOK
          <6> QED
            BY <4>0, <6>1, <6>2
        <5>2. Proposed(lock[n_1])
          BY DEF ILockMax, Inv
        <5>3. Proposed(b)
          BY Vote(n,b) DEF Vote
        <5>4. Proposed(parent[parent[b]])
          BY <5>3, Proposed(parent[b]) DEF Inv, IConf, Confirmed, TypeOK
        <5>5. Proposed(lock'[n_1])
          BY <5>1, <5>2, <5>4
        <5> QED
          BY <5>5, <3>0 DEF Proposed
      <4>1. max' = [max EXCEPT ![n] = round[b]]
        BY Vote(n,b) DEF Vote, vote
      <4>20. n_1 = n => round[b] > max[n]
        BY Vote(n,b) DEF Vote
      <4>2. n_1 = n => max'[n] > max[n]
        BY <4>1, <4>20 DEF Inv, TypeOK
      <4>c1. CASE n_1 /= n
        <5>1. max'[n_1] = max[n_1]
          BY <4>1, <4>c1
        <5>2. lock'[n_1] = lock[n_1]
          <6>1. CASE lock' = lock
            BY <6>1
          <6>2. CASE lock' = [lock EXCEPT ![n] = parent[parent[b]]]
            BY <6>2, <4>c1
          <6>3. QED
            BY <4>0, <6>1, <6>2
        <5>3. round[lock[n_1]] <= max[n_1]
          BY <5>1, <5>2 DEF Inv, ILockMax
        <5>5. QED
          BY <5>1, <5>2, <5>3, <4>p, <3>0 
      <4>c2. CASE n_1 = n
        <5>0. round[lock[n]] <= round[parent[b]]
          BY Vote(n,b), n_1 \in CNodes, <4>c2 DEF Vote
        <5>1. max'[n] = round[b]
          BY <4>1, <3>1 DEF TypeOK
        <5>2. CASE lock' = lock
            <6>1. round[parent[b]] <= round[b]
              BY IPHh, IPR DEF Inv, IPR
            <6>2. round[lock[n]]' = round[lock[n]]
              BY <5>2, <3>0
            <6>3. round[lock[n]]' <= round[parent[b]]
              BY <5>0, <6>2
            <6>4. round[lock[n]]' <= round[b]
              BY <6>3, <6>1, <3>1 DEF Inv, TypeOK, Rounds
            <6>5. max[n]' = round[b]
              BY <4>1, <3>0, <3>1 DEF Inv, TypeOK, Rounds
            <6> QED
              BY <6>4, <6>5, <4>c2, <4>p

        <5>3. CASE lock' = [lock EXCEPT ![n] = parent[parent[b]]]
          <6>1. round[b] >= round[parent[parent[b]]]
            BY IPR DEF Inv, TypeOK, IPr, Rounds, IPR
          <6>2. max'[n] = round[b]
            BY <4>1 DEF Inv, TypeOK
          <6>3. lock'[n] = parent[parent[b]]
            BY <5>3 DEF Inv, TypeOK
          <6>4. QED
            BY <6>1, <6>2, <4>c2, <6>3, <3>0, <3>1, <4>p DEF Inv, TypeOK
        <5> QED
          BY <5>2, <5>3, <4>0
      <4> QED
        BY <4>c1, <4>c2
    <3>9. ILock'
      <4> SUFFICES ASSUME NEW n_1 \in CNodes',
                          NEW b_1 \in Blocks',
                          (n_1 \in votes[b_1])'
                   PROVE  round[lock'[n_1]] >= round[parent[parent[b_1]]]
        BY <3>0 DEF ILock
      <4>0. lock' = [lock EXCEPT ![n] = parent[parent[b]]] \/ lock' = lock
        BY Vote(n,b) DEF Vote, vote
      <4>c0. CASE lock'[n_1] = lock[n_1] /\ n_1 \in votes[b_1]
        BY ILock, <4>c0 DEF ILock, Inv
      <4>c1. CASE n_1 /= n
        <5>1. lock'[n_1] = lock[n_1]
          BY <4>0, <4>c1, <3>1 DEF Inv, TypeOK
        <5>2. n_1 \in votes[b_1]
          BY <4>c1, Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>3. QED
          BY <5>1, <5>2, <4>c0
      <4>c2. CASE n_1 = n
        <5>0. round[lock'[n]] >= round[lock[n]]
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK, Rounds
        <5>c1. CASE b_1 /= b
          <6>0. n_1 \in votes[b_1]
            BY Vote(n,b), <5>c1 DEF Vote, vote
          <6>1. round[lock[n_1]] >= round[parent[parent[b_1]]]
            BY <6>0, ILock DEF Inv, ILock
          <6>2. round[lock'[n_1]] >= round[lock[n_1]]
            BY <5>0, <4>c2
          <6> QED  
            BY <6>2, <6>1, <3>1 DEF Inv, TypeOK, Rounds
        <5>c2. CASE b_1 = b
          <6>c1. CASE round[parent[parent[b]]] <= round[lock[n]]
            <7>0. ~(round[parent[parent[b]]] > round[lock[n]])
              BY <6>c1 DEF Inv, TypeOK, Rounds
            <7>1. lock' = lock
              BY Vote(n,b), <7>0 DEF Vote, vote
            <7>2. round[lock[n]] = round[lock'[n]]
              BY <7>1
            <7>3. round[lock'[n]] >= round[parent[parent[b]]]
              BY <7>2, <6>c1 DEF Inv, TypeOK, Rounds
            <7> QED
              BY <7>3, <5>c2, <4>c2
          <6>c2. CASE round[parent[parent[b]]] > round[lock[n]]
            <7>0. lock' = [lock EXCEPT ![n] = parent[parent[b]]]
              BY Vote(n,b), <6>c2 DEF Vote, vote
            <7>1. lock'[n] = parent[parent[b]]
              BY <7>0, <3>1 DEF TypeOK
            <7>2. round[lock'[n]] >= round[parent[parent[b]]]
              BY <7>1, TypeOK DEF Inv, TypeOK, Rounds
            <7> QED
              BY <7>2, <5>c2, <4>c2
          <6> QED 
            BY <6>c1, <6>c2 DEF Inv, TypeOK, Rounds
        <5> QED
          BY <5>c2, <5>c1
      <4> QED
        BY <4>c2, <4>c1
    <3>10. IPrepared'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks',
                          NEW n_1 \in CNodes',
                          (n_1 \in votes[b_1])'
                   PROVE  Proposed(b_1)'
        BY DEF IPrepared
      <4>1. Proposed(b_1) => Proposed(b_1)'
        BY <3>0 DEF Proposed
      <4>2. CASE n_1 \in votes[b_1]
        BY <4>1, <4>2 DEF Inv, IPrepared
      <4>3. CASE n_1 \notin votes[b_1]
        <5>1. b_1 = b
          BY Vote(n,b), <4>3 DEF Vote, vote
        <5>2. Proposed(b)
          BY Vote(n,b) DEF Vote, vote
        <5> QED
          BY <5>2, <5>1, <4>1
      <4> QED
        BY <4>2, <4>3
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10 DEF Inv
  <2>3. CASE UNCHANGED vars
    <3>1. TypeOK'
      BY TypeOK, UNCHANGED vars DEF vars, TypeOK, Inv
    <3>2. IPr'
      BY IPr, UNCHANGED vars DEF vars, IPr, Inv
    <3>3. IConf'
      BY IConf, UNCHANGED vars DEF vars, IConf, Inv, Confirmed, Proposed
    <3>4. IVote2'
      BY IVote2, UNCHANGED vars DEF vars, IVote2, Inv
    <3>5. IVote'
      BY IVote, UNCHANGED vars DEF vars, IVote, Inv, chain
    <3>6. IPx'
      BY UNCHANGED vars DEF vars, IPx, Inv
    <3>7. IMax'
      BY UNCHANGED vars DEF vars, IMax, Inv
    <3>8. ILockMax'
      BY UNCHANGED vars DEF vars, ILockMax, Inv, Proposed
    <3>9. ILock'
      BY UNCHANGED vars DEF vars, ILock, Inv, Proposed
    <3>10. IPrepared'
      BY UNCHANGED vars DEF vars, IPrepared, Inv, Proposed
    <3> QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7, <3>8, <3>9, <3>10 DEF Inv
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
  
<1>3. Inv => Correct
  <2>1. Inv => \A i \in Nat: iCorrect(i)
    <3>. SUFFICES ASSUME Inv
                 PROVE  \A i \in Nat: iCorrect(i)
      OBVIOUS
    <3>1. iCorrect(0)
      BY InductionStart DEF Inv, iCorrect
    <3>2. \A i \in Nat: (\A j \in 0..(i-1): iCorrect(j)) => iCorrect(i)
      <4> SUFFICES ASSUME NEW i \in Nat,
                          \A j \in 0..(i-1): iCorrect(j),
                          NEW b \in Blocks, NEW c \in Blocks,
                          NEW c_1 \in Blocks,
                          /\ chain(b,c_1)
                          /\ Confirmed(c_1),
                          Confirmed(c),
                          round[b] + i = round[c]
                   PROVE  Ancestor(b,c)
        BY DEF Committed, cci, iCorrect
      <4>1. b = parent[parent[c_1]]
        BY chain(b,c_1) DEF chain
      <4>2. CASE  round[b] = round[c]
        <5>1. Confirmed(c)
          OBVIOUS
        <5>2. round[b] = round[c]
          BY <4>2
        <5>3. Confirmed(b)
          <6>1. Proposed(c_1)
            BY DEF Confirmed
          <6>2. Confirmed(parent[c_1])
            BY <6>1 DEF Inv, IConf
          <6>3. Proposed(parent[c_1])
            BY <6>2 DEF Confirmed 
          <6>4. Confirmed(parent[parent[c_1]])
            BY <6>3 DEF Inv, IConf, TypeOK
          <6> QED
            BY <6>4, <4>1
        <5>4. b=c
          BY TwoConfirmed, <5>1, <5>2, <5>3 DEF Inv 
        <5>5. QED
          BY <5>4, Anc1
      <4>3. CASE round[parent[c_1]] = round[c]
        <5>1. Confirmed(c)
          OBVIOUS
        <5> DEFINE b_1 == parent[c_1]
        <5>0. b_1 \in Blocks
          BY DEF TypeOK, Inv
        <5>2. Confirmed(b_1)
          <6>1. Proposed(c_1)
            BY DEF Confirmed
          <6> QED
            BY IConf, <6>1 DEF Inv, IConf
        <5>3. round[b_1] = round[c]
          BY <4>3
        <5>4. b_1=c
          BY <5>1, <5>2, <5>3, <5>0, TwoConfirmed, IVote2 DEF Inv
        <5>5. Ancestor(b,b_1)
          BY <4>1, Anc2, <5>0, b=parent[b_1], PTypeOK DEF Inv
        <5> QED
          BY <5>5, <5>4
      <4>32. CASE round[c_1] = round[c]
        <5>1. Confirmed(c)
          OBVIOUS
        <5>2. Confirmed(c_1)
          OBVIOUS
        <5>4. c_1=c
          BY <5>1, <5>2, <4>32, TwoConfirmed, IVote2 DEF Inv
        <5> DEFINE b_1 == parent[c_1]
        <5>0. b_1 \in Blocks
          BY DEF b_1, Inv, TypeOK
        <5> HIDE DEF b_1
        <5>5. Ancestor(parent[b_1],b_1)
          BY <5>0, Anc2, PTypeOK DEF Inv
        <5>51. Ancestor(b,b_1)
          BY <4>1, <5>5 DEF b_1
        <5>6. Ancestor(b_1,c_1)
          BY Anc2, PTypeOK DEF Inv, b_1
        <5>7. Ancestor(b,c_1)
          BY Anc3, PTypeOK, <5>0, <5>51, <5>6  DEF Inv
        <5> QED
          BY <5>4, <5>7
      <4>4. CASE round[c] > round[c_1]
        <5> round[c] > round[c_1]
          BY <4>4
        <5>0. \E n \in CNodes: n \in votes[c] \cap votes[c_1]
          BY Confirmed(c), Confirmed(c_1), QuorumAssumption DEF Confirmed
        <5>1. round[b] <= round[parent[c]]
          <6>0. chain(parent[parent[c_1]],c_1)
            BY <4>1
          <6>1. round[c_1] <= round[c]
            OBVIOUS  
          <6>2. round[parent[parent[c_1]]] <= round[parent[c]]
            BY <5>0, <6>0, <6>1, IVote DEF Inv, IVote
          <6> QED
            BY <6>2, <4>1
        <5>3. Ancestor(b,c)
          <6> DEFINE c_2 == parent[c]
          <6>0. c_2 \in Blocks
            BY DEF TypeOK, Inv
          <6> DEFINE j == round[c_2] - round[b]
          <6>1. j \in 0..i-1
            <7>1. j \in Int
              BY DEF TypeOK, Rounds, Inv
            <7>2. j >= 0
              BY <5>1 DEF TypeOK, Inv, Rounds
            <7>3. j < i
              <8>1. round[c_1] >= 0
                BY Confirmed(c_1), TypeOK DEF Inv, TypeOK, Confirmed, Proposed, Rounds
              <8>2. round[c] > 0
                BY <4>4, <8>1, TypeOK DEF Inv, TypeOK, Rounds
              <8>3. round[parent[c]] < round[c]
                BY <8>2, IPx, IPr DEF Inv, TypeOK, Rounds, IPr, IPx
              <8> QED 
              BY IPr, <4>4, <8>3 DEF Rounds, Inv, TypeOK
            <7> QED
              BY <7>1, <7>2, <7>3
          <6>2. iCorrect(j)
            BY <6>1
          <6>3. cci(b,c_2,j)
            <7>1. Committed(b)
              BY DEF Committed
            <7>2. Confirmed(c_2)
              <8>1. Proposed(c)
                BY DEF Confirmed
              <8> QED
                BY <8>1 DEF Inv, IConf
            <7>3. round[b] + j = round[c_2]
              BY DEF TypeOK, Inv, Rounds
            <7> QED
              BY <7>1, <7>2, <7>3 DEF cci
          <6>4. Ancestor(b,c_2)
            BY <6>3, <6>2, <6>0 DEF iCorrect
          <6> QED
            BY <6>4, <6>0, Anc2, Anc3, PTypeOK DEF Inv
        
        <5> QED
          BY <5>3
      <4>5. round[c] > round[c_1] \/ round[c] <= round[c_1]
        BY TypeOK DEF Inv, TypeOK, Rounds
      <4>6. round[b] <= round[c]
        BY TypeOK DEF Inv, TypeOK, Rounds
      <4>7. round[c] <= round[c_1] => 
            \/ round[c] = round[c_1]
            \/ round[c] = round[parent[c_1]]
            \/ round[c] = round[b]   
        <5> SUFFICES ASSUME round[c] <= round[c_1]
                     PROVE  \/ round[c] = round[c_1]
                            \/ round[c] = round[parent[c_1]]
                            \/ round[c] = round[b]
          OBVIOUS
        <5>0. round[c] = round[c_1] \/ round[c] < round[c_1]
           BY DEF Inv, TypeOK, Rounds
        <5>1. CASE round[c] = round[c_1]
          BY <5>1
        <5>2. CASE round[c] < round[c_1]
          <6>0. round[c_1] =< round[parent[c_1]] + 1
            BY chain(b,c_1) DEF chain
          <6>1. round[parent[c_1]] <= round[c_1] 
            BY IPHh, IPR DEF Inv, IPR
          <6>2. round[parent[c_1]] = round[c_1] \/ round[parent[c_1]] = round[c_1] - 1
            BY <6>0, <6>1 DEF Inv, TypeOK, Rounds
          <6>3. round[c] <= round[parent[c_1]]
            BY <5>2, <6>2, TypeOK DEF Inv, TypeOK, Rounds
          <6>4. CASE round[c] = round[parent[c_1]]
            BY <6>4
          <6>5. CASE round[c] < round[parent[c_1]]
            <7> DEFINE pc == parent[c_1]
            <7> HIDE DEF pc
            <7>00. pc \in Blocks
              BY DEF Inv, TypeOK, pc
            <7>0. round[pc] =< round[parent[pc]] + 1
              BY chain(b,c_1) DEF chain, pc
            <7>1. round[parent[pc]] <= round[pc]
              BY <7>00, IPHh, IPR DEF Inv, IPR
            <7>2. round[parent[pc]] = round[pc] \/ round[parent[pc]] = round[pc] - 1
              BY <7>00, <7>0, <7>1 DEF Inv, TypeOK, Rounds
            <7>3. round[c] <= round[parent[pc]]
              BY <6>5, <7>2, TypeOK DEF Inv, TypeOK, Rounds, pc
            <7>4. round[c] <= round[b]
              BY <4>1, <7>3 DEF pc
            <7>5. round[c] >= round[b]
              BY DEF Inv, TypeOK, Rounds
            <7>6. round[c] = round[b]
              BY <7>4, <7>5 DEF Inv, TypeOK, Rounds
            <7> QED
              BY <7>6
            
          <6> QED
            BY <6>3, <6>4, <6>5 DEF Inv, TypeOK, Rounds
        <5> QED
          BY <5>0, <5>1, <5>2
        
        
      <4> QED
        BY <4>2, <4>3, <4>32, <4>4, <4>5, <4>7
    <3>3. \A n \in Nat: iCorrect(n)
      <4> DEFINE Q(i) == \A m \in 0..i: iCorrect(m)
      <4>1. Q(0) 
        BY <3>2
      <4>2. \A n \in Nat: Q(n) => Q(n+1)
        BY <3>2
      <4>3. \A n \in Nat: Q(n) BY <4>1, <4>2, NatInduction, Isa
      <4>4. QED BY <4>3
    <3> QED
      BY <3>3, GeneralNatInduction
    
  <2>2. QED
    BY <2>1, CanUseI DEF Inv
    
<1>4. QED
    BY <1>1,<1>2, <1>3, PTL DEF Inv, Spec



LEMMA Inv /\ Correct => Safe
  <1> SUFFICES ASSUME Inv /\ Correct,
                      NEW b \in Blocks, NEW c \in Blocks,
                      Committed(b) /\ Committed(c)
               PROVE  Ancestor(c,b) \/ Ancestor(b,c)
    BY DEF Safe
  <1>1. CASE round[b] <= round[c]
    <2>1. Confirmed(c) 
      BY CommittedConfirmed DEF Inv
    <2>2. QED
      BY <2>1, <1>1 DEF Correct, cc
  <1>2. CASE round[c] <= round[b]
    <2>1. Confirmed(b) 
      BY CommittedConfirmed DEF Inv
    <2>2. QED
      BY <2>1, <1>2 DEF Correct, cc
  <1> QED
    BY <1>1, <1>2 DEF Inv, TypeOK, Rounds

=============================================================================
\* Modification History
\* Last modified Tue Mar 02 21:16:04 CET 2021 by leanderjehl
\* Created Wed Oct 14 21:46:24 CEST 2020 by leanderjehl
