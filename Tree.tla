-------------------------------- MODULE Tree --------------------------------
EXTENDS Naturals, NaturalsInduction

(***************************************************************************)
(* A tree of blocks.                                                       *)
(* Every block has a hight                                                 *)
(***************************************************************************)
CONSTANT Blocks

Heights == Nat \cup {-1}

(***************************************************************************
Variables: 
- height assigns a height to every block.
- blocks not yet added to the tree have hight -1
- prev is the parent pointer in the tree
- blocks not yet added are their own parent
- the genesis (root) is its own parent
***************************************************************************)

VARIABLE height, prev

vars == <<height, prev>>

(* gen is the genesis block, or root in the tree *)
gen == CHOOSE b \in Blocks : TRUE



TypeOK == /\ height \in [Blocks -> Heights]
          /\ prev \in [Blocks -> Blocks]

dummyheigt == [b \in Blocks |-> -1]


Init == /\ height = [dummyheigt EXCEPT ![gen]=0]
        /\ prev = [b \in Blocks |-> b]
        
proposed(b) == /\ b \in Blocks
               /\ height[b] /= -1

propose(b,p,h) == /\ height' = [height EXCEPT ![b] = h]
                  /\ prev' = [prev EXCEPT ![b] = p]
        
Propose(b,p,h) == /\ b \in Blocks 
                  /\ ~proposed(b)
                  /\ proposed(p)
                  /\ h > height[p]
                  /\ propose(b,p,h)

Next == \/ \E b,p \in Blocks: \E h \in Heights: Propose(b,p,h)
        
Spec == Init /\ [][Next]_vars

(* I'm trying to define an ancestor relation using the previous certiciated. *)
Extend(A) == A \cup { <<b,c>> \in Blocks \X Blocks: <<b,prev[c]>> \in A }
A0 == { <<b,c>> \in Blocks \X Blocks: b=c }

ancestors[i \in Nat] == IF i=0 THEN A0
                        ELSE Extend(ancestors[i-1])

Ancestor(b,c) == /\ height[b] <= height[c] 
                 /\ height[c] - height[b] \in Nat 
                 /\ <<b,c>> \in ancestors[height[c] - height[b]]

\* Trying to prove the either step in this theorem triggers a bug in TLAPS
THEOREM AncestorsDefConclusion == NatInductiveDefConclusion(ancestors, A0, LAMBDA x,y : Extend(x))
<1>1. NatInductiveDefHypothesis(ancestors, A0, LAMBDA x,y : Extend(x))
  BY DEF NatInductiveDefHypothesis, ancestors, A0
<1>2. QED
  BY <1>1, NatInductiveDef
                                                                 
(* These are the main properties that I would like to proof *)
Anc1 == \A b \in Blocks: Ancestor(b,b)
Anc2 == \A b \in Blocks: Ancestor(prev[b],b)
Anc3 == \A b, c, d \in Blocks: Ancestor(b,c) /\ Ancestor(c,d) => Ancestor(b,d)

(* An alternative approach, trying to define the i-th ancestor of a block. *)
pre(b) == CHOOSE g \in [Nat -> Blocks] : g = [i \in Nat |-> IF i=0 THEN b ELSE prev[g[i-1]]]

prevOK == prev \in [Blocks -> Blocks]

\*Trying to prove the QED step below triggers the same bug
THEOREM prevOK => \A b \in Blocks: pre(b) = [ i \in Nat |-> IF i = 0 THEN b ELSE prev[b]]
  <1> SUFFICES ASSUME prevOK,
                      NEW b \in Blocks
               PROVE  pre(b) = [ i \in Nat |-> IF i = 0 THEN b ELSE prev[b]]
    OBVIOUS
  <1> QED
    BY DEF prevOK, pre
  

=============================================================================
\* Modification History
\* Last modified Thu Nov 12 08:54:52 CET 2020 by leanderjehl
\* Created Wed Nov 11 13:24:33 CET 2020 by leanderjehl
