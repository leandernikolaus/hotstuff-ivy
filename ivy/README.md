# hotstuff-ivy
Proving the HotStuff BFT protocol using the ivy language and tool

This repository contains a proof of safety for a high-level model of the chained [HotStuff BFT protocol](https://arxiv.org/abs/1803.05069).
The protocol is modelled using the [ivy](http://microsoft.github.io/ivy/) language and tool.
The model is based on a description of the HotStuff protocol I created for my blockchain technology course, available [here](https://ux.uis.no/~ljehl/pdf/hotStuffExplained.pdf).

Different from classical consensus protocols, chained HotStuff decides on branches in a tree, rather than values.
The repository contains the following files:

### Files

* [hotstuff_base](hotstuff_base.ivy) contains the basic for modelling hotstuff, including the tree.
* [hotstuff_proof](hotstuff_proof.ivy) contains the safety proof for hotstuff.
* [hotstuff_global](hotstuff_global.ivy) contains a model of the hotstuff algorithm using a global tree, but omitting the relations only introduced for the proof.

The *ivy* branch also contains a preliminary version of the proof for which ivy runs extremely long (`tree.ivy`), 
and first tries towards implementing the tree (`tree-imp.ivy`).

### Isolates (Information below is outdated)

[hotstuff_base](hotstuff_base.ivy) contain three isolates. 
* `height` contains a totally ordered set with minimum. These are used to describe the height of nodes in the tree.
* `tree` contains a model of a tree, rooted in the genesis block. 
  - The `propose` action successively adds new blocks to the tree by assigning a parent or previous block `prev`. 
  - The `propose` action also updates the reacability predicate `ancestor`.
* `hotstuff_base` contains the model of the protocol. The model contains two actions:
  - `propose` adds a new block to the tree, same as in `tree.ivy`.  Additionally `propose` also updates the `just` predicate. This predicate points to an ancestor block, that was certified, i.e., signed or voted for by a quorum of the processes (nodes).
  - `vote` models a node or process voting for a specific block.

[hotstuff_simple](hotstuff_simple.ivy) contains an isolate `hotstuffs_proof` that extends the `hotstuff_base` isolate.
Actions are the same, but additional predicates are introduced.
  - The invariant proven (Line 87) shows that, once a block is confirmed, only descendants of that block may get a certified.

### Invariant (Information below is outdated)
The main invariant proven is written on line `87` of [hotstuff_simple](hotstuff_simple.ivy).
This invariant shows that, once a block is confirmed by a 3-chain, all blocks that are certified, i.e. receive signatures from a quorum, and lye at a larger hight in the tree, are decentendts of the confirmed block. It is the same as the `Correct` property in the TLA model.

### Expressiveness
It was difficult to even express some of the invariants without introducing quantifier circles of the form, for every block B exists a block C.

Thus I was unable to write that every block in the tree should have a parent.
Similarly, I was unable to express the `ancestor` relation.
Therefore I ended up simply building the `ancestor` relation in the action.
The `votedb` and `votedh` relations are added for similar reasons.

### The proof effort
It took me about one week to prove the invariant.
I started of by adding lots of simple invariants to rule out unrelated counterexamples to inductivity.

Mostly I found working with Ivy great. 
However, in some cases it seems to run forever, i.e. hours. I believe this is what is referred to in the community as the SMT solver diverging.
In these cases, I usually came up with a counterexample to inductivity myself and changed the model. Using the `marco_finder=false` speeded up the process only in some cases.

Initially, verifying the complete proof took about 13 minutes, what is ok, but significantly more than what I was expecting based on the papers, where proof times of less than 10 seconds are reported [PoPL`17](https://dl.acm.org/doi/abs/10.1145/3140568).

Proof time was significantly reduced. Old proofs are available on *ivy* branch.