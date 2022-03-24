[![DOI](https://zenodo.org/badge/299863250.svg)](https://zenodo.org/badge/latestdoi/299863250)

# Verifying Simplified Hotstuff 
This repository includes safety proof for the simplified HotStuff protocol.
Proofs are done using both TLAPS and Ivy tool.

| Proof              | Tool                                         |
| ------------------ | -------------------------------------------- |
| [Ivy Proof](ivy)   | [Ivy](http://microsoft.github.io/ivy/)       |
| [TLAPS Proof](tla) | [TLAPS](http://tla.msr-inria.inria.fr/tlaps) |

## The protocol: Simplified HotStuff

Simplified HotStuff is a variant of the [HotStuff BFT Algorithm](https://dl.acm.org/doi/10.1145/3293611.3331591).
The main difference is that simplified HotStuff requires that every block contains a certificate for its parent.
This allows to simplify the Safety rule.

## The model
Instead of explicitly modelling message passing, we model the algorithm as operations of multiple nodes/replicas on a tree structure.
The protocol is modelled through two actions. 

The `propose` action adds a new block to the tree.
We allow any block to be added to the tree, as long as its parent is certified.
We do note model view change and the restrictions this poses on proposing new blocks.
That is, because these restrictions only apply to correct nodes, and thus are only necessary for liveness, not safety.

The `vote` action add the signature of a node to a block.
The model enforces that correct nodes follow the rules of the algorithm for signing blocks.
We note that whether the `vote` action is enabled only depends on which blocks a node has previously signed.
It does not depend on the complete tree.
Thus, our model covers the case where a node does not know the complete tree, but only the subtree which he has signed.
