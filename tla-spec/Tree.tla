-------------------------------- MODULE Tree --------------------------------
EXTENDS Naturals, NaturalsInduction, TLAPS, FiniteSets, SequenceTheorems

(***************************************************************************)
(* A tree of blocks.                                                       *)
(* Every block has a hight                                                 *)
(***************************************************************************)
CONSTANT Blocks

Heights == Nat \cup {-1}

(* Need to assume that Blocks is nonempty, to be able to choose a block. *)
ASSUME ExistBlock == \E b \in Blocks: TRUE
(* gen is the genesis block, or root in the tree *)
gen == CHOOSE b \in Blocks : TRUE



(***************************************************************************
Variables: 
- height assigns a height to every block.
- blocks not yet added to the tree have hight -1
- prev is the parent pointer in the tree
- blocks not yet added are their own parent
- the genesis (root) is its own parent
***************************************************************************)

VARIABLE height, prev


(* I'm trying to define an ancestor relation using the previous certiciated. *)
Extend(A) == A \cup { bc \in Blocks \X Blocks: <<bc[1], prev[bc[2]]>> \in A }
A0 == { bc \in Blocks \X Blocks: bc[1] = bc[2] }

ancestors[i \in Nat] == IF i=0 THEN A0
                        ELSE Extend(ancestors[i-1])

Ancestor(b,c) == \E i \in Nat: <<b,c>> \in ancestors[i]

PType == \A b \in Blocks: prev[b] \in Blocks
HType == \A b \in Blocks: height[b] \in Heights
IPH == \A b \in Blocks: height[prev[b]] <= height[b]

\* Trying to prove the either step in this theorem triggers a bug in TLAPS
THEOREM AncestorsDefConclusion == NatInductiveDefConclusion(ancestors, A0, LAMBDA x,y : Extend(x))
<1>1. NatInductiveDefHypothesis(ancestors, A0, LAMBDA x,y : Extend(x))
  BY DEF NatInductiveDefHypothesis, ancestors, A0
<1>2. QED
  BY <1>1, NatInductiveDef
  
THEOREM AncestorsDef == \A i \in Nat: ancestors[i] = IF i=0 THEN A0 ELSE Extend(ancestors[i-1])
  BY AncestorsDefConclusion DEF NatInductiveDefConclusion
  
THEOREM AncestorsInit == \A b,c \in Blocks: <<b,c>> \in ancestors[0] <=> b = c
  <1>1. ancestors[0] = A0
    BY AncestorsDef
  <1>2. \A b,c \in Blocks: <<b,c>> \in A0 <=> b = c
      BY DEF A0
  <1> QED
    BY <1>1, <1>2




THEOREM AncestorsPrev == \A b,c \in Blocks: \A i \in Nat \ {0}: 
    <<b,c>> \in ancestors[i] <=> \/ <<b,c>> \in ancestors[i-1] 
                                 \/ <<b,prev[c]>> \in ancestors[i-1]  
  <1> SUFFICES ASSUME NEW b \in Blocks, NEW c \in Blocks,
                      NEW i \in Nat \ {0}
               PROVE  <<b,c>> \in ancestors[i] <=> \/ <<b,c>> \in ancestors[i-1] 
                                                   \/ <<b,prev[c]>> \in ancestors[i-1]
    OBVIOUS
  <1>0. i /= 0
    OBVIOUS
  <1>1. DEFINE bb == <<b,c>>
  <1>2. bb \in ancestors[i] <=> bb \in Extend(ancestors[i-1])
    BY  AncestorsDef, <1>0
  <1>3. bb \in Blocks \X Blocks
    OBVIOUS
  <1>4. bb \in Extend(ancestors[i-1]) <=> bb \in ancestors[i-1] \/ bb \in { bc \in Blocks \X Blocks: <<bc[1], prev[bc[2]]>> \in ancestors[i-1] }
    BY <1>3 DEF Extend
  <1>5. bb \in { bc \in Blocks \X Blocks: <<bc[1], prev[bc[2]]>> \in ancestors[i-1] } <=> <<bb[1], prev[bb[2]]>> \in ancestors[i-1]
    BY <1>3
  <1>6. <<bb[1], prev[bb[2]]>> \in ancestors[i-1] <=> <<b,prev[c]>> \in ancestors[i-1]
    OBVIOUS
  <1> QED
    BY <1>2, <1>4, <1>5, <1>6
  

THEOREM AncDef == \A b,c \in Blocks: Ancestor(b,c) <=> (b = c \/ Ancestor(b,prev[c]))
  <1> SUFFICES ASSUME NEW b \in Blocks, NEW c \in Blocks
               PROVE  Ancestor(b,c) <=> (b = c \/ Ancestor(b,prev[c]))
    OBVIOUS
  <1>1. Ancestor(b,c) => (b = c \/ Ancestor(b,prev[c]))
    <2> SUFFICES ASSUME NEW i \in Nat,
                        <<b,c>> \in ancestors[i]
                 PROVE  b = c \/ Ancestor(b,prev[c])
      BY DEF Ancestor
    <2>0. DEFINE InAnc(j) == <<b,c>> \in ancestors[j]
    <2> HIDE DEF InAnc
    <2>1. InAnc(i)
      BY DEF InAnc
    <2>2. \E m \in Nat: /\ InAnc(m)
                        /\ \A k \in 0..m-1: ~InAnc(k)
      BY SmallestNatural, InAnc(i), i \in Nat
    <2> SUFFICES ASSUME NEW j \in Nat,
                        InAnc(j),
                        \A k \in 0..j-1: ~InAnc(k)
                 PROVE  b = c \/ Ancestor(b,prev[c])
      BY <2>2
    <2>3. CASE j = 0
      BY AncestorsInit, j=0 DEF InAnc
    <2>4. CASE j /= 0
      <3>1. j-1 \in Nat
        BY j/= 0
      <3>2. j-1 \in 0..j-1 
        BY <3>1, j /= 0
      <3>3. InAnc(j) /\ ~InAnc(j-1)
        BY j-1 \in 0..j-1, <3>1
      <3>4. <<b,prev[c]>> \in ancestors[j-1]
        BY AncestorsPrev, <3>3, j /= 0 DEF InAnc
      <3>5. Ancestor(b,prev[c])
        BY <3>4, <3>1 DEF Ancestor
      <3> QED
        BY <3>5
    <2> QED
      BY <2>3, <2>4
     
  <1>2. (b = c \/ Ancestor(b,prev[c])) => Ancestor(b,c)
    <2>1. CASE b = c
      <3>1. <<b,c>> \in ancestors[0]
        BY AncestorsInit, b = c
      <3> QED
        BY <3>1 DEF Ancestor
    <2>2. ASSUME NEW i \in Nat,
                 <<b,prev[c]>> \in ancestors[i]
          PROVE  Ancestor(b,c)
        <3>1. <<b,c>> \in ancestors[i+1]
          BY AncestorsPrev, i+1 \in Nat \ {0}, <<b,prev[c]>> \in ancestors[i]
        <3> QED
          BY <3>1 DEF Ancestor
    <2>3. QED
      BY <2>1, <2>2 DEF Ancestor
    
  <1> QED
    BY <1>1, <1>2 
    
                                                          
(* These are the main properties that I would like to proof *)
COROLLARY Anc1 == \A b \in Blocks: Ancestor(b,b)
  BY AncDef
  
COROLLARY Anc2 == PType => \A b \in Blocks: Ancestor(prev[b],b)
  BY AncDef DEF PType
  
THEOREM Anc3 == PType => (\A b, c, d \in Blocks: 
                        Ancestor(b,c) /\ Ancestor(c,d) => Ancestor(b,d))
  <1> SUFFICES ASSUME PType,
                      NEW b \in Blocks, NEW c \in Blocks, NEW d \in Blocks,
                      NEW i \in Nat,
                      <<b,c>> \in ancestors[i],
                      NEW j \in Nat,
                      <<c,d>> \in ancestors[j]
               PROVE  <<b,d>> \in ancestors[i+j]
    BY DEF Ancestor
  <1> DEFINE IsAnc(jj) == \A dd \in Blocks: <<c,dd>> \in ancestors[jj] => <<b,dd>> \in ancestors[i+jj]
  <1> HIDE DEF IsAnc
  <1>1. IsAnc(0)
    <2> SUFFICES ASSUME NEW dd \in Blocks,
                        <<c,dd>> \in ancestors[0]
                 PROVE  <<b,dd>> \in ancestors[i]
      BY DEF IsAnc
    <2>1. c = dd 
      BY AncestorsInit
    <2> QED
      BY <2>1, <<b,c>> \in ancestors[i]
  <1>2. \A jj \in Nat: IsAnc(jj) => IsAnc(jj+1)
    <2> SUFFICES ASSUME NEW dd \in Blocks,
                        NEW jj \in Nat,
                        IsAnc(jj),
                        <<c,dd>> \in ancestors[jj+1]
                 PROVE  <<b,dd>> \in ancestors[i+(jj+1)]
      BY DEF IsAnc
    <2>0. jj+1 \in Nat \ {0}
      OBVIOUS
    <2>1. <<c,dd>> \in ancestors[jj] \/ <<c,prev[dd]>> \in ancestors[jj]
      BY <2>0, AncestorsPrev
    <2>2. CASE <<c,dd>> \in ancestors[jj]
      <3> DEFINE bddAnc(x) == <<b,dd>> \in ancestors[x]
      <3>1. bddAnc(i+jj)
        BY IsAnc(jj), <<c,dd>> \in ancestors[jj] DEF IsAnc
      <3>2. \A ii \in Nat \ {0}: <<b,dd>> \in ancestors[ii-1] => <<b,dd>> \in ancestors[ii]
        BY AncestorsPrev
      <3>20. \A ii \in Nat \ {0}: bddAnc(ii-1) => bddAnc(ii)
        BY <3>2
      <3> HIDE DEF bddAnc
      <3>3. \A ii \in Nat: bddAnc(ii) => bddAnc(ii+1)
        BY <3>20
      <3>4. bddAnc(i+jj+1)
        BY <3>1, <3>3
      <3> QED
        BY <3>4 DEF bddAnc
    <2>3. CASE <<c,prev[dd]>> \in ancestors[jj]
      <3> DEFINE pd == prev[dd]
      <3> HIDE DEF pd
      <3>0. pd \in Blocks
        BY PType DEF pd, PType
      <3>1. <<c,pd>> \in ancestors[jj]
        BY <<c,prev[dd]>> \in ancestors[jj] DEF pd
      <3>2. <<b,pd>> \in ancestors[i+jj]
        BY <3>0, <3>1, IsAnc(jj) DEF IsAnc
      <3>3. <<b,prev[dd]>> \in ancestors[i+jj]
        BY <3>2 DEF pd
      <3>4. \A ii \in Nat: <<b,prev[dd]>> \in ancestors[ii] => <<b,dd>> \in ancestors[ii+1]
        BY AncestorsPrev, PType DEF PType
      <3>5. <<b,dd>> \in ancestors[i+jj+1]
        BY <3>4, <3>3
      <3> QED 
        BY <3>5
    <2> QED
      BY <2>1, <2>2, <2>3
  
  <1>3. \A jj \in Nat: IsAnc(jj)
    BY <1>1, <1>2, NatInduction
  <1> QED
    BY <1>3 DEF IsAnc 
  
THEOREM Anc4 ==  /\ HType 
                 /\ PType
                 /\ IPH
                 => \A b, c \in Blocks: 
                    Ancestor(b,c) => height[b] <= height[c]
  <1> SUFFICES ASSUME HType, PType, IPH,
                      NEW b \in Blocks, NEW c \in Blocks,
                      NEW i \in Nat,
                      <<b,c>> \in ancestors[i]
               PROVE  height[b] <= height[c]
    BY DEF Ancestor
  <1> DEFINE ok(j) == \A cc \in Blocks: <<b,cc>> \in ancestors[j] => height[b] <= height[cc]
  <1> HIDE DEF ok
  <1>0. ok(0)
    <2> SUFFICES ASSUME NEW cc \in Blocks,
                        <<b,cc>> \in ancestors[0]
                 PROVE  height[b] <= height[cc]
      BY DEF ok
    <2>0. b = cc 
      BY AncestorsDef, ancestors[0] = A0 DEF A0
    <2> QED
      BY <2>0 DEF HType, Heights
  <1>1. \A j \in Nat: ok(j) => ok(j+1)
    <2> SUFFICES ASSUME NEW j \in Nat,
                        ok(j),
                        NEW cc \in Blocks,
                        <<b,cc>> \in ancestors[j+1]
                 PROVE  height[b] <= height[cc]
      BY DEF ok
    <2>1. <<b,cc>> \in ancestors[j] \/ <<b,prev[cc]>> \in ancestors[j]
      BY AncestorsPrev
    <2>2. CASE <<b,cc>> \in ancestors[j]
      BY ok(j), <2>2 DEF ok
    <2>3. CASE <<b,prev[cc]>> \in ancestors[j]
      <3>1. height[b] <= height[prev[cc]]
        BY ok(j), <2>3, PType DEF ok, PType
      <3>2. height[prev[cc]] <= height[cc]
        BY IPH DEF IPH
      <3> QED
        BY <3>1, <3>2, HType, PType DEF Heights, HType, PType
    <2> QED
      BY <2>1, <2>2, <2>3
    
  <1>2. \A j \in Nat: ok(j)
    BY <1>0, <1>1, NatInduction
  <1> QED
    BY <1>2 DEF ok
  

=============================================================================
\* Modification History
\* Last modified Mon Nov 16 14:49:38 CET 2020 by leanderjehl
\* Created Wed Nov 11 13:24:33 CET 2020 by leanderjehl
