# Club Sets and Fodor's Lemma
Project Overview

## File info

### Contents of `Club.lean`:

* Basic properties of restrictions of sets of ordinals by taking the elemtnts that are smaller
  than a given ordinal (i.e, the equivalent of intersections of sets and ordinals).
* All definitions: Unbounded sets, club sets, stationary sets, regressive functions, diagonal intersection.
* All inductive constructions of sequences needed for the proofs and their basic properties.

### Contents of `Fodor.lean`:

* Proof that the intersection of two club sets in o is club in o, in the generality that o is any ordinal with
  uncountable cofinality.
* Proof that intersections of less than κ club sets in κ are club in κ, for a regular cardinal κ.
  > The unboundedness part is also proved for any κ with uncountable cofinality with an extra
  condition on the sets: each one has to be a subset of the ones before it.
* Proof that the diagonal intersection of κ club sets in κ is club in κ.
* Proof of Fodor's lemma.

> Each statement uses the one before it. \
> The proofs are split into unboundedness and closedness.

## To-do list

The proof is complete (don't look at this before Friday), but there is a lot of optimization to be made.
I highlight the main improvements that I have in mind:

* The theorem `int_lt_card_club` can also be proven in a more general setting, namely for sequences
  of sets indexed in an ordinal less than the cofinality of κ.