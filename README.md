# ARMv8-A Address Translation: Isabelle Proof Scripts

This directory contains the Isabelle scripts for the proof about ARMv8-A
address translation presented in §8 of the paper.  It imports our ARMv8-A model
and the Sail and Lem support libraries from the directory snapshots/isabelle in
this archive.  The main proof is structured into files as follows:

- `Address_Translation_Pure.thy` contains our pure characterisation of address
  translation.
- `Address_Translation_Soundness.thy` contains the formalisation of our
  assumptions on the system state, the definition of the equivalence relations
  we use to deal with undefined fields of result records, and the soundness proof
  of our characterisation w.r.t. the original model (Theorem 8.1 in the paper).

The remaining files contain auxiliary definitions and lemmas:

- `Address_Translation_Orig.thy` contains copies of some of the critical parts
  of the original model, in particular the loop for the translation table walk,
  so that we can reason about those individually.  Note that this just serves
  to make it easier to state some of the auxiliary lemmas; the main proof refers
  only to the original model.
- `AArch64_Aux.thy` contains Hoare triples about various auxiliary functions in
  the original ARMv8-A specification.
- `AArch64_Trivia.thy` contains various simplification rules that are useful
  for the computation of preconditions.
- `Proof_Methods.thy` contains the tactics we use to prove Hoare triples.
- `Hoare_Extras.thy` contains Hoare proof rules (in addition to those in the
  Sail library) tailored for the Hoare triples arising in this model, e.g.
  involving tuples with many elements.
- `Word_Extra.thy` contains helper lemmas about machine words.

These proofs require

- Isabelle 2018,
- the ARMv8-A model and the Sail library for Isabelle at revision
  07e3591e2427db2d9407d554ac57984ca566c6ed of
  [Sail](https://github.com/rems-project/sail),
- the Lem library at revision
  54e1c03a1f9997445132d326f568f429c924b0b1 of
  [Lem](https://github.com/rems-project/lem).

The Sail repository contains snapshots of these libraries in the directory
snapshots/isabelle (last checked that the versions there match the ones
required here at [Sail](https://github.com/rems-project/sail) revision
fb9a2e2367c912a04ae8cd1a8d2aa9c2f2220c14).

If SNAPSHOTS is substituted with the path to that snapshots directory, the
following command (executed in this directory) opens the main file of this
proof:

```
isabelle jedit -d SNAPSHOTS -l Sail-AArch64 Address_Translation_Soundness.thy
```

On our test machine (Intel Core i7-7700 CPU @ 3.60GHz, 64GB RAM) checking the
proof and the supporting theories requires roughly 15 minutes.
