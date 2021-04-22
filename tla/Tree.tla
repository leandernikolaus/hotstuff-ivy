-------------------------------- MODULE Tree --------------------------------
EXTENDS Naturals, NaturalsInduction, TLAPS, FiniteSets, SequenceTheorems

(***************************************************************************)
(* A tree of blocks.                                                       *)
(* One block is genesis                                                    *)
(***************************************************************************)
CONSTANT Blocks

Rounds == Nat \cup {-1}

ASSUME ExistsBlock == Blocks /= {}
gen == CHOOSE b \in Blocks: TRUE

(***************************************************************************)
(* Variables:                                                              *)
(* - round assigns a Round to every block.                                 *)
(* - blocks not yet added to the tree have round -1                        *)
(* - parent give for every block a parent                                  *)
(* - blocks not yet added are their own parent                             *)
(* - the genesis (root) is its own parent                                  *)
(***************************************************************************)

VARIABLE round, parent

(***************************************************************************)
(* TLAPS cannot handle recursive operator definitions.                     *)
(*                                                                         *)
(* Therefore the definition of the Ancestor operator below is a bit        *)
(* verbose.                                                                *)
(***************************************************************************)
Extend(A) == A \cup { bc \in Blocks \X Blocks: <<bc[1], parent[bc[2]]>> \in A }
A0 == { bc \in Blocks \X Blocks: bc[1] = bc[2] }

ancestors[i \in Nat] == IF i=0 THEN A0
                        ELSE Extend(ancestors[i-1])

Ancestor(b,c) == \E i \in Nat: <<b,c>> \in ancestors[i]

(***************************************************************************)
(* Proving the definition of the ancestor relation.                        *)
(***************************************************************************)
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




THEOREM AncestorsParent == \A b,c \in Blocks: \A i \in Nat \ {0}: 
    <<b,c>> \in ancestors[i] <=> \/ <<b,c>> \in ancestors[i-1] 
                                 \/ <<b,parent[c]>> \in ancestors[i-1]  
  <1> SUFFICES ASSUME NEW b \in Blocks, NEW c \in Blocks,
                      NEW i \in Nat \ {0}
               PROVE  <<b,c>> \in ancestors[i] <=> \/ <<b,c>> \in ancestors[i-1] 
                                                   \/ <<b,parent[c]>> \in ancestors[i-1]
    OBVIOUS
  <1>0. i /= 0
    OBVIOUS
  <1>1. DEFINE bb == <<b,c>>
  <1>2. bb \in ancestors[i] <=> bb \in Extend(ancestors[i-1])
    BY  AncestorsDef, <1>0
  <1>3. bb \in Blocks \X Blocks
    OBVIOUS
  <1>4. bb \in Extend(ancestors[i-1]) <=> bb \in ancestors[i-1] \/ bb \in { bc \in Blocks \X Blocks: <<bc[1], parent[bc[2]]>> \in ancestors[i-1] }
    BY <1>3 DEF Extend
  <1>5. bb \in { bc \in Blocks \X Blocks: <<bc[1], parent[bc[2]]>> \in ancestors[i-1] } <=> <<bb[1], parent[bb[2]]>> \in ancestors[i-1]
    BY <1>3
  <1>6. <<bb[1], parent[bb[2]]>> \in ancestors[i-1] <=> <<b,parent[c]>> \in ancestors[i-1]
    OBVIOUS
  <1> QED
    BY <1>2, <1>4, <1>5, <1>6

THEOREM AncDef == \A b,c \in Blocks: Ancestor(b,c) <=> (b = c \/ Ancestor(b,parent[c]))
  <1> SUFFICES ASSUME NEW b \in Blocks, NEW c \in Blocks
               PROVE  Ancestor(b,c) <=> (b = c \/ Ancestor(b,parent[c]))
    OBVIOUS
  <1>1. Ancestor(b,c) => (b = c \/ Ancestor(b,parent[c]))
    <2> SUFFICES ASSUME NEW i \in Nat,
                        <<b,c>> \in ancestors[i]
                 PROVE  b = c \/ Ancestor(b,parent[c])
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
                 PROVE  b = c \/ Ancestor(b,parent[c])
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
      <3>4. <<b,parent[c]>> \in ancestors[j-1]
        BY AncestorsParent, <3>3, j /= 0 DEF InAnc
      <3>5. Ancestor(b,parent[c])
        BY <3>4, <3>1 DEF Ancestor
      <3> QED
        BY <3>5
    <2> QED
      BY <2>3, <2>4
     
  <1>2. (b = c \/ Ancestor(b,parent[c])) => Ancestor(b,c)
    <2>1. CASE b = c
      <3>1. <<b,c>> \in ancestors[0]
        BY AncestorsInit, b = c
      <3> QED
        BY <3>1 DEF Ancestor
    <2>2. ASSUME NEW i \in Nat,
                 <<b,parent[c]>> \in ancestors[i]
          PROVE  Ancestor(b,c)
        <3>1. <<b,c>> \in ancestors[i+1]
          BY AncestorsParent, i+1 \in Nat \ {0}, <<b,parent[c]>> \in ancestors[i]
        <3> QED
          BY <3>1 DEF Ancestor
    <2>3. QED
      BY <2>1, <2>2 DEF Ancestor
    
  <1> QED
    BY <1>1, <1>2 
    
(***************************************************************************)
(* Usefull properties of the ancestor relation.                            *)
(*                                                                         *)
(* Anc1 reflexive                                                          *)
(*                                                                         *)
(* Anc2 parents are ancestor                                               *)
(*                                                                         *)
(* Anc3 transitive                                                         *)
(*                                                                         *)
(* Anc4 if parents have lower round (IPR), then ancestors have a lower     *)
(* round                                                                   *)
(*                                                                         *)
(* Anc3 and Anc4 use the type assumptions PType,                           *)
(* Anc4 uses the type assumption RType and invariant IPR                   *)
(***************************************************************************) 
PType == \A b \in Blocks: parent[b] \in Blocks
RType == \A b \in Blocks: round[b] \in Rounds
IPR == \A b \in Blocks: round[parent[b]] <= round[b]

                                                     
COROLLARY Anc1 == \A b \in Blocks: Ancestor(b,b)
  BY AncDef
  
COROLLARY Anc2 == PType => \A b \in Blocks: Ancestor(parent[b],b)
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
    <2>1. <<c,dd>> \in ancestors[jj] \/ <<c,parent[dd]>> \in ancestors[jj]
      BY <2>0, AncestorsParent
    <2>2. CASE <<c,dd>> \in ancestors[jj]
      <3> DEFINE bddAnc(x) == <<b,dd>> \in ancestors[x]
      <3>1. bddAnc(i+jj)
        BY IsAnc(jj), <<c,dd>> \in ancestors[jj] DEF IsAnc
      <3>2. \A ii \in Nat \ {0}: <<b,dd>> \in ancestors[ii-1] => <<b,dd>> \in ancestors[ii]
        BY AncestorsParent
      <3>20. \A ii \in Nat \ {0}: bddAnc(ii-1) => bddAnc(ii)
        BY <3>2
      <3> HIDE DEF bddAnc
      <3>3. \A ii \in Nat: bddAnc(ii) => bddAnc(ii+1)
        BY <3>20
      <3>4. bddAnc(i+jj+1)
        BY <3>1, <3>3
      <3> QED
        BY <3>4 DEF bddAnc
    <2>3. CASE <<c,parent[dd]>> \in ancestors[jj]
      <3> DEFINE pd == parent[dd]
      <3> HIDE DEF pd
      <3>0. pd \in Blocks
        BY PType DEF pd, PType
      <3>1. <<c,pd>> \in ancestors[jj]
        BY <<c,parent[dd]>> \in ancestors[jj] DEF pd
      <3>2. <<b,pd>> \in ancestors[i+jj]
        BY <3>0, <3>1, IsAnc(jj) DEF IsAnc
      <3>3. <<b,parent[dd]>> \in ancestors[i+jj]
        BY <3>2 DEF pd
      <3>4. \A ii \in Nat: <<b,parent[dd]>> \in ancestors[ii] => <<b,dd>> \in ancestors[ii+1]
        BY AncestorsParent, PType DEF PType
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
  
THEOREM Anc4 ==  /\ RType 
                 /\ PType
                 /\ IPR
                 => \A b, c \in Blocks: 
                    Ancestor(b,c) => round[b] <= round[c]
  <1> SUFFICES ASSUME RType, PType, IPR,
                      NEW b \in Blocks, NEW c \in Blocks,
                      NEW i \in Nat,
                      <<b,c>> \in ancestors[i]
               PROVE  round[b] <= round[c]
    BY DEF Ancestor
  <1> DEFINE ok(j) == \A cc \in Blocks: <<b,cc>> \in ancestors[j] => round[b] <= round[cc]
  <1> HIDE DEF ok
  <1>0. ok(0)
    <2> SUFFICES ASSUME NEW cc \in Blocks,
                        <<b,cc>> \in ancestors[0]
                 PROVE  round[b] <= round[cc]
      BY DEF ok
    <2>0. b = cc 
      BY AncestorsDef, ancestors[0] = A0 DEF A0
    <2> QED
      BY <2>0 DEF RType, Rounds
  <1>1. \A j \in Nat: ok(j) => ok(j+1)
    <2> SUFFICES ASSUME NEW j \in Nat,
                        ok(j),
                        NEW cc \in Blocks,
                        <<b,cc>> \in ancestors[j+1]
                 PROVE  round[b] <= round[cc]
      BY DEF ok
    <2>1. <<b,cc>> \in ancestors[j] \/ <<b,parent[cc]>> \in ancestors[j]
      BY AncestorsParent
    <2>2. CASE <<b,cc>> \in ancestors[j]
      BY ok(j), <2>2 DEF ok
    <2>3. CASE <<b,parent[cc]>> \in ancestors[j]
      <3>1. round[b] <= round[parent[cc]]
        BY ok(j), <2>3, PType DEF ok, PType
      <3>2. round[parent[cc]] <= round[cc]
        BY IPR DEF IPR
      <3> QED
        BY <3>1, <3>2, RType, PType DEF Rounds, RType, PType
    <2> QED
      BY <2>1, <2>2, <2>3
    
  <1>2. \A j \in Nat: ok(j)
    BY <1>0, <1>1, NatInduction
  <1> QED
    BY <1>2 DEF ok  
    
(***************************************************************************)
(* We where unable to prove primed variants of the corollaries above, e.g. *)
(* COROLLARY Anc2p == PType' => \A b \in Blocks: Ancestor(parent[b],b)'    *)
(*   BY Anc2                                                               *)
(***************************************************************************)

  

=============================================================================
\* Modification History
\* Last modified Thu Apr 22 15:15:53 CEST 2021 by leanderjehl
\* Created Wed Nov 11 13:24:33 CET 2020 by leanderjehl
