# hotstuff-ivy
Proving the HotStuff BFT protocol using the ivy language and tool

This repository contains a proof of safety for a high-level model of the chained [HotStuff BFT protocol](https://arxiv.org/abs/1803.05069).
The protocol is modelled using the [ivy](http://microsoft.github.io/ivy/) language and tool.

Different from classical consensus protocolls, chained HotStuff decides on branches in a tree, rather than values.
The repository contains the following files:

* [tree.ivy](tree.ivy) contains a model of a tree, rooted in the genesis block. 
  - The `propose` action successively adds new blocks to the tree by assigning a parent or previous block `prev`. 
  - The `propose` action also updates the reacability predicate `ancestor`.
* [hotstuff.ivy](hotstuff.ivy) contains the model of the protocol. The model contains two actions:
  - `propose` adds a new block to the tree, same as in `tree.ivy`.  Additionally `propose` also updates the `just` predicate. This predicate points to an ancestor block, that was certified, i.e., signed or voted for by a quorum of the processes (nodes).
  - `vote` models a node or process voting for a specific block.
  - The invariant proven (Line 133) shows that, once a block is confirmed, only descendants of that block may get a certified.
