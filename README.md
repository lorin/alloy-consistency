---
title: Eventual consistency and Alloy
---

In [Principles of Eventual Consistency][PoEC] (PoEC), Sebastian
Burckhardt introduces techniques for reasoning about eventually consistent data
types. His approach uses sets, relations, and first order logic.

This sounds like a good fit for the [Alloy modeling
language](http://alloytools.org/), which is also based on sets, relations, and
first order logic.

As an example, from page 22 of PoEC, Burckhardt lists some properties of
binaries relations, along with algebraic definitions. It's straightforward to translate these into Alloy syntax.


|Property    |Algebraic definition                          |Alloy syntax                       |
|------------|----------------------------------------------|-----------------------------------|
|symmetric   |rel=rel<sup>-1</sup>                          |`rel=~rel`                         |
|reflexive   |id<sub>A</sub> ⊆ rel                          |`(iden & A->A) in rel`             |
|irreflexive |id<sub>A</sub> ∩ rel= ∅                       |`no (iden & A->A)`                 |
|transitive  |(rel;rel) ⊆ rel                               |`rel.rel in rel`                   |
|acyclic     |id<sub>A</sub> ∩ rel<sup>+</sup> = ∅          |`no (iden & A->A & ^rel)`          |
|total       |rel ∪ rel<sup>-1</sup> ∪ id<sub>A</sub> = A×A |`rel + ~rel + (iden & A->A) = A->A`|


[PoEC]: https://www.microsoft.com/en-us/research/publication/principles-of-eventual-consistency/
