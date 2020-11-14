------------------------------ MODULE hotstuff ------------------------------
EXTENDS Integers, FiniteSets, TLAPS, NaturalsInduction, Tree

(***************************************************************************)
(*   *)
(***************************************************************************)
CONSTANT CNodes, FNodes, Quorums

Nodes == CNodes \cup FNodes

ASSUME QuorumAssumption == /\ \A Q \in Quorums : Q \subseteq Nodes
                           /\ \A Q1, Q2 \in Quorums : \E n \in CNodes: n \in (Q1 \cap Q2)

VARIABLE votes, lock, max

vars == <<height, prev, votes, lock, max>>

TypeOK == /\ height \in [Blocks -> Heights]
          /\ prev \in [Blocks -> Blocks]
          /\ votes \in [Blocks -> SUBSET Nodes]
          /\ lock \in [Nodes -> Blocks]
          /\ max \in [Nodes -> Heights]

dummyheigt == [b \in Blocks |-> -1]
dummyvotes == [b \in Blocks |-> {}]


Init == /\ lock = [n \in Nodes |-> gen]
        /\ max = [n \in Nodes |-> 0]
        /\ height = [dummyheigt EXCEPT ![gen]=0]
        /\ prev = [b \in Blocks |-> gen]
        /\ votes = [dummyvotes EXCEPT ![gen]=Nodes]
        
Proposed(b) == /\ b \in Blocks
               /\ height[b] /= -1

Confirmed(b) == /\ Proposed(b)
                /\ votes[b] \in Quorums
  
propose(b,p,h) == /\ height' = [height EXCEPT ![b] = h]
                  /\ prev' = [prev EXCEPT ![b] = p]
        
Propose(b,p,h) == /\ b \in Blocks 
                  /\ ~ Proposed(b)
                  /\ Confirmed(p)
                  /\ h > height[p]
                  /\ propose(b,p,h)
                  /\ UNCHANGED <<lock, max, votes>>


vote(n,b) == /\ max' = [max EXCEPT ![n] = height[b]]
             /\ votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
             /\ IF height[prev[prev[b]]] > height[lock[n]] 
                    THEN lock' = [lock EXCEPT ![n] = prev[prev[b]]]
                ELSE lock' = lock  

Vote(n,b) == /\ Proposed(b)
             /\ n \in Nodes
             /\ \/ n \notin CNodes
                \/ /\ height[b] > max[n]
                   /\ \/ Ancestor(lock[n],b) \* safety rule 
                      \/ height[lock[n]] < height[prev[b]] \* lifeness rule
             /\ vote(n,b)
             /\ UNCHANGED <<height, prev>>
             
Next == \/ \E b,p \in Blocks: \E h \in Heights: Propose(b,p,h)
        \/ \E b \in Blocks: \E n \in Nodes: Vote(n,b)
        
Spec == Init /\ [][Next]_vars
                      

chain(b,c) == /\ prev[prev[c]] = b
              /\ height[c] <= height[prev[c]] + 1
              /\ height[prev[c]] <= height[b] + 1

                      
Committed(b) == \E c \in Blocks:
               /\ chain(b,c)
               /\ Confirmed(c)
               

cci(b,c,i) == /\ Committed(b)
              /\ Confirmed(c)
              /\ height[b] + i = height[c]

cc(b,c) == /\ Committed(b)
           /\ Confirmed(c)
           /\ height[b] <= height[c]
        
iCorrect(i) == \A b, c \in Blocks: 
               cci(b,c,i)
               => Ancestor(b,c)
            
Correct ==  \A b, c \in Blocks: 
               cc(b,c)
               => Ancestor(b,c)

Inv2 == /\ TypeOK
        /\ \A b, c \in Blocks: 
            cc(b,c)
            => \/ ~Ancestor(b,c)
               \/ cc(b,prev[c])

IConf == \A b \in Blocks: Confirmed(prev[b])
\* Different from IPH defined in Tree.tla
IPh == \A b \in Blocks: prev[b] = b \/ height[prev[b]] < height[b]
IPx == \A b \in Blocks: prev[b] = b => height[b] \in {0, -1}
IMax == \A n \in Nodes: \A b \in Blocks: n \in votes[b] => max[n] >= height[b]     

IVote == \A b,c \in Blocks: \A n \in CNodes:
        /\ n \in votes[b]
        /\ chain(prev[prev[b]],b)
        /\ n \in votes[c]
        /\ height[b] <= height[c]
        => height[prev[prev[b]]] <= height[prev[c]]

IVote2 == \A b,c \in Blocks: \A n \in CNodes:
        /\ n \in votes[b]
        /\ n \in votes[c]
        /\ height[b] = height[c]
        => b = c

Inv ==  /\ TypeOK
        /\ IVote
        /\ IVote2
        /\ IConf
        /\ IPh
        /\ IPx
        /\ IMax

diff(c,b) == height[c] - height[b]

LEMMA ExistsI == TypeOK => (\A b,c \in Blocks: cc(b,c) <=> \E i \in Nat: cci(b,c,i))
  <1> SUFFICES ASSUME TypeOK,
                      NEW b \in Blocks, NEW c \in Blocks
               PROVE  cc(b,c) <=> \E i \in Nat: cci(b,c,i)
    OBVIOUS
  <1>1. height[b] \in Nat \cup{-1}
    BY DEF TypeOK, Heights
  <1>2. height[c] \in Nat \cup{-1}
    BY DEF TypeOK, Heights
  <1>3. \E i \in Nat: height[b] + i = height[c] => height[b] <= height[c] 
    BY <1>1, <1>2
  <1>4. height[b] <= height[c] => height[c] - height[b] \in Nat
    BY <1>1, <1>2
  <1>5. height[b] <= height[c] => diff(c,b) \in Nat
    BY <1>4 DEF diff
  <1>6. height[b] + diff(c,b) = height[c]
    BY <1>1, <1>2 DEF diff
  <1>7. height[b] <= height[c] => \E i \in Nat: height[b] + i = height[c]
    BY <1>5, <1>6
  <1> QED
    BY <1>4, <1>7 DEF cc,cci, Heights, TypeOK
  
LEMMA CommittedConfirmed == TypeOK /\ IConf => \A b : Committed(b) => Confirmed(b)
  BY DEF TypeOK, Committed, chain, IConf

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
  <1>4. height[b] + 0 = height[c]
    BY cci(b,c,0) DEF cci
  <1>5. height[b] = height[c]
    BY <1>4 DEF TypeOK, Heights
  <1>6. b=c
    BY IVote2, <1>3, <1>5 DEF IVote2
  <1>7. Ancestor(b,c)
   BY Anc1, <1>6
  <1>8 QED
    BY <1>7

LEMMA TwoConfirmed == IVote2 => (\A b,c \in Blocks: 
                                    /\ Confirmed(b)
                                    /\ Confirmed(c)
                                    /\ height[b] = height[c]
                                    => b = c)
  <1> SUFFICES ASSUME IVote2,
                      NEW b \in Blocks, NEW c \in Blocks,
                      /\ Confirmed(b)
                      /\ Confirmed(c)
                      /\ height[b] = height[c]
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

LEMMA IPHh == TypeOK /\ IPh => IPH
  <1> SUFFICES ASSUME IPh, TypeOK,
                      NEW b \in Blocks
               PROVE  height[prev[b]] <= height[b]
    BY DEF IPH
  <1>2. CASE height[prev[b]] < height[b]
    BY DEF IPh, TypeOK, Heights
  <1>3. CASE prev[b] = b
    BY <1>3 DEF TypeOK, Heights
  <1> QED
    BY <1>2, <1>3, IPh DEF IPh
  
         
THEOREM Spec => []Correct
<1>1. Init => Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  Inv'
    OBVIOUS
  <2>1. ASSUME NEW b \in Blocks,
               NEW p \in Blocks,
               NEW h \in Heights,
               Propose(b,p,h)
        PROVE  Inv'
  <2>2. ASSUME NEW b \in Blocks,
               NEW n \in Nodes,
               Vote(n,b)
        PROVE  Inv'
    <3>0. UNCHANGED <<height, prev>>
      BY Vote(n,b)  DEF Vote, Inv, TypeOK
    <3>1. TypeOK'
      <4>1. (height \in [Blocks -> Heights])'
        BY <3>0 DEF Inv, TypeOK
      <4>2. (prev \in [Blocks -> Blocks])'
        BY <3>0 DEF Inv, TypeOK
      <4>3. (votes \in [Blocks -> SUBSET Nodes])'
        BY Vote(n,b),votes' = [votes EXCEPT ![b] = votes[b]\cup {n}] DEF Vote, vote, Inv, TypeOK
      <4>4. (lock \in [Nodes -> Blocks])'
        <5>0. lock' = lock \/ lock' = [lock EXCEPT ![n] = prev[prev[b]]]
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>1. CASE lock' = lock
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>2. CASE lock' = [lock EXCEPT ![n] = prev[prev[b]]]
          BY Vote(n,b) DEF Vote, vote, Inv, TypeOK
        <5>3. QED
          BY <5>0, <5>1, <5>2
      <4>5. (max \in [Nodes -> Heights])'
        <5>1. max \in [Nodes -> Heights]
          BY DEF Inv, TypeOK
        <5>2. max' = [max EXCEPT ![n] = height[b]]
          BY Vote(n,b) DEF Vote, vote
        <5>3. max' \in [Nodes -> Heights]
          BY <5>1, <5>2 DEF Inv, TypeOK
        <5>4. QED
          BY <5>3
      <4>6. QED
        BY <4>1, <4>2, <4>3, <4>4, <4>5 DEF TypeOK     
    <3>2. IVote'
      <4> SUFFICES ASSUME NEW b_1 \in Blocks', NEW c \in Blocks',
                          NEW n_1 \in CNodes',
                          (/\ n_1 \in votes[b_1]
                           /\ chain(prev[prev[b_1]],b_1)
                           /\ n_1 \in votes[c]
                           /\ height[b_1] <= height[c])'
                   PROVE  (height[prev[prev[b_1]]] <= height[prev[c]])'
        BY DEF IVote
      <4>1. CASE n_1 \in votes[b_1] /\ n_1 \in votes[c]
        <5>0. chain(prev[prev[b_1]],b_1)
          BY <3>0, chain(prev[prev[b_1]],b_1)' DEF chain
        <5>01. height[b_1] =< height[c]
          BY <3>0
        <5>1. height[prev[prev[b_1]]] =< height[prev[c]]
          BY n_1 \in votes[b_1] /\ n_1 \in votes[c], <5>0, <5>01 DEF Inv, IVote
        <5>. QED
          BY <3>0, <5>1
      <4>2. CASE n_1 \in votes[b_1] /\ n_1 \notin votes[c]
        <5>0. votes' = [votes EXCEPT ![b] = votes[b]\cup {n}]
          BY Vote(n,b) DEF vote, Vote
        <5>1. c = b /\ n_1 = n
          BY <5>0, n_1 \in votes[b_1] /\ n_1 \notin votes[c], n_1 \in votes'[c]
        <5>2. \/ Ancestor(lock[n],b) \* safety rule 
              \/ height[lock[n]] < height[prev[b]] \* lifeness rule
          BY <5>1, Vote(n,b), n \in CNodes DEF Vote
        <5>3. \/ lock[n] = b
              \/ height[lock[n]] <= height[prev[b]]
          <6>0. CASE height[lock[n]] < height[prev[b]]
            BY height[lock[n]] < height[prev[b]]
          <6>1. CASE Ancestor(lock[n],b)
            <7>1. lock[n] = b \/ Ancestor(lock[n],prev[b])
              BY AncDef, <6>1, lock[n] \in Blocks DEF Inv, TypeOK
            <7>2. CASE lock[n] = b
              BY <7>2
            <7>3. CASE Ancestor(lock[n],prev[b])
            <7> QED
          <6> QED
            BY <5>2, <6>0, <6>1
        <5> QED
      <4>3. CASE n_1 \notin votes[b_1]
      <4> QED
        BY <4>1, <4>2, <4>3
      
    <3>3. IVote2'
    <3>4. IConf'
    <3>5. IPh'
      BY Vote(n,b), UNCHANGED <<height, prev>> DEF Vote, Inv, IPh
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Inv
  <2>3. CASE UNCHANGED vars
    <3>1. TypeOK'
      BY TypeOK, UNCHANGED vars DEF vars, TypeOK, Inv
    <3>2. IPh'
      BY IPh, UNCHANGED vars DEF vars, IPh, Inv
    <3>3. IConf'
      BY IConf, UNCHANGED vars DEF vars, IConf, Inv, Confirmed, Proposed
    <3>4. IVote2'
      BY IVote2, UNCHANGED vars DEF vars, IVote2, Inv
    <3>5. IVote'
      BY IVote, UNCHANGED vars DEF vars, IVote, Inv, chain
    <3>6. QED
      BY <3>1, <3>2, <3>3, <3>4, <3>5 DEF Inv
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
                          height[b] + i = height[c]
                   PROVE  Ancestor(b,c)
        BY DEF Committed, cci, iCorrect
      <4>1. b = prev[prev[c_1]]
        BY chain(b,c_1) DEF chain
      <4>2. CASE  height[b] = height[c]
        <5>1. Confirmed(c)
          OBVIOUS
        <5>2. height[b] = height[c]
          BY <4>2
        <5>3. Confirmed(b)
          BY <4>1, IConf DEF IConf, Inv, TypeOK
        <5>4. b=c
          BY TwoConfirmed, <5>1, <5>2, <5>3 DEF Inv 
        <5>5. QED
          BY <5>4, Anc1
      <4>3. CASE height[prev[c_1]] = height[c]
        <5>1. Confirmed(c)
          OBVIOUS
        <5> DEFINE b_1 == prev[c_1]
        <5>0. b_1 \in Blocks
          BY DEF TypeOK, Inv
        <5>2. Confirmed(b_1)
          BY IConf DEF Inv, IConf
        <5>3. height[b_1] = height[c]
          BY <4>3
        <5>4. b_1=c
          BY <5>1, <5>2, <5>3, <5>0, TwoConfirmed, IVote2 DEF Inv
        <5>5. Ancestor(b,b_1)
          BY <4>1, Anc2, <5>0, b=prev[b_1], PTypeOK DEF Inv
        <5> QED
          BY <5>5, <5>4
      <4>32. CASE height[c_1] = height[c]
        <5>1. Confirmed(c)
          OBVIOUS
        <5>2. Confirmed(c_1)
          OBVIOUS
        <5>4. c_1=c
          BY <5>1, <5>2, <4>32, TwoConfirmed, IVote2 DEF Inv
        <5> DEFINE b_1 == prev[c_1]
        <5>0. b_1 \in Blocks
          BY DEF b_1, Inv, TypeOK
        <5> HIDE DEF b_1
        <5>5. Ancestor(prev[b_1],b_1)
          BY <5>0, Anc2, PTypeOK DEF Inv
        <5>51. Ancestor(b,b_1)
          BY <4>1, <5>5 DEF b_1
        <5>6. Ancestor(b_1,c_1)
          BY Anc2, PTypeOK DEF Inv, b_1
        <5>7. Ancestor(b,c_1)
          BY Anc3, PTypeOK, <5>0, <5>51, <5>6  DEF Inv
        <5> QED
          BY <5>4, <5>7
      <4>4. CASE height[c] > height[c_1]
        <5> height[c] > height[c_1]
          BY <4>4
        <5>0. \E n \in CNodes: n \in votes[c] \cap votes[c_1]
          BY Confirmed(c), Confirmed(c_1), QuorumAssumption DEF Confirmed
        <5>1. height[b] <= height[prev[c]]
          <6>0. chain(prev[prev[c_1]],c_1)
            BY <4>1
          <6>1. height[c_1] <= height[c]
            OBVIOUS  
          <6>2. height[prev[prev[c_1]]] <= height[prev[c]]
            BY <5>0, <6>0, <6>1, IVote DEF Inv, IVote
          <6> QED
            BY <6>2, <4>1
        <5>3. Ancestor(b,c)
          <6> DEFINE c_2 == prev[c]
          <6>0. c_2 \in Blocks
            BY DEF TypeOK, Inv
          <6> DEFINE j == height[c_2] - height[b]
          <6>1. j \in 0..i-1
            <7>1. j \in Int
              BY DEF TypeOK, Heights, Inv
            <7>2. j >= 0
              BY <5>1 DEF TypeOK, Inv, Heights
            <7>3. j < i
              <8>1. height[c_1] >= 0
                BY Confirmed(c_1), TypeOK DEF Inv, TypeOK, Confirmed, Proposed, Heights
              <8>2. height[c] > 0
                BY <4>4, <8>1, TypeOK DEF Inv, TypeOK, Heights
              <8>3. height[prev[c]] < height[c]
                BY <8>2, IPx, IPh DEF Inv, TypeOK, Heights, IPh, IPx
              <8> QED 
              BY IPh, <4>4, <8>3 DEF Heights, Inv, TypeOK
            <7> QED
              BY <7>1, <7>2, <7>3
          <6>2. iCorrect(j)
            BY <6>1
          <6>3. cci(b,c_2,j)
            <7>1. Committed(b)
              BY DEF Committed
            <7>2. Confirmed(c_2)
              BY DEF Inv, IConf
            <7>3. height[b] + j = height[c_2]
              BY DEF TypeOK, Inv, Heights
            <7> QED
              BY <7>1, <7>2, <7>3 DEF cci
          <6>4. Ancestor(b,c_2)
            BY <6>3, <6>2, <6>0 DEF iCorrect
          <6> QED
            BY <6>4, <6>0, Anc2, Anc3, PTypeOK DEF Inv
        
        <5> QED
          BY <5>3
      <4>5. height[c] > height[c_1] \/ height[c] <= height[c_1]
        BY TypeOK DEF Inv, TypeOK, Heights
      <4>6. height[b] <= height[c]
        BY TypeOK DEF Inv, TypeOK, Heights
      <4>7. height[c] <= height[c_1] => 
            \/ height[c] = height[c_1]
            \/ height[c] = height[prev[c_1]]
            \/ height[c] = height[b]   
        <5> SUFFICES ASSUME height[c] <= height[c_1]
                     PROVE  \/ height[c] = height[c_1]
                            \/ height[c] = height[prev[c_1]]
                            \/ height[c] = height[b]
          OBVIOUS
        <5>0. height[c] = height[c_1] \/ height[c] < height[c_1]
           BY DEF Inv, TypeOK, Heights
        <5>1. CASE height[c] = height[c_1]
          BY <5>1
        <5>2. CASE height[c] < height[c_1]
          <6>0. height[c_1] =< height[prev[c_1]] + 1
            BY chain(b,c_1) DEF chain
          <6>1. height[prev[c_1]] <= height[c_1] 
            BY IPHh, IPH DEF Inv, IPH
          <6>2. height[prev[c_1]] = height[c_1] \/ height[prev[c_1]] = height[c_1] - 1
            BY <6>0, <6>1 DEF Inv, TypeOK, Heights
          <6>3. height[c] <= height[prev[c_1]]
            BY <5>2, <6>2, TypeOK DEF Inv, TypeOK, Heights
          <6>4. CASE height[c] = height[prev[c_1]]
            BY <6>4
          <6>5. CASE height[c] < height[prev[c_1]]
            <7> DEFINE pc == prev[c_1]
            <7> HIDE DEF pc
            <7>00. pc \in Blocks
              BY DEF Inv, TypeOK, pc
            <7>0. height[pc] =< height[prev[pc]] + 1
              BY chain(b,c_1) DEF chain, pc
            <7>1. height[prev[pc]] <= height[pc]
              BY <7>00, IPHh, IPH DEF Inv, IPH
            <7>2. height[prev[pc]] = height[pc] \/ height[prev[pc]] = height[pc] - 1
              BY <7>00, <7>0, <7>1 DEF Inv, TypeOK, Heights
            <7>3. height[c] <= height[prev[pc]]
              BY <6>5, <7>2, TypeOK DEF Inv, TypeOK, Heights, pc
            <7>4. height[c] <= height[b]
              BY <4>1, <7>3 DEF pc
            <7>5. height[c] >= height[b]
              BY DEF Inv, TypeOK, Heights
            <7>6. height[c] = height[b]
              BY <7>4, <7>5 DEF Inv, TypeOK, Heights
            <7> QED
              BY <7>6
            
          <6> QED
            BY <6>3, <6>4, <6>5 DEF Inv, TypeOK, Heights
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

                      
=============================================================================
\* Modification History
\* Last modified Sat Nov 14 15:51:27 CET 2020 by leanderjehl
\* Created Wed Oct 14 21:46:24 CEST 2020 by leanderjehl
