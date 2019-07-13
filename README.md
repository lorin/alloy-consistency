---
title: Eventual consistency and Alloy
---

In the (free!) book [Principles of Eventual Consistency][PoEC], Sebastian
Burckhardt introduces techniques for reasoning about eventually consistent data
types. His approach uses sets, relations, and first order logic.

This sounds like a good fit for the [Alloy modeling
language](http://alloytools.org/), which is also based on sets, relations, and
first order logic.

As an example, from page 22 of Burckhardt, Burckhardt lists some properties of
binaries relations, along with element-wise and algebraic definitions. These
are very easy to translate from the algebraic definition to Alloy

|Property    |Alloy                              |
|------------|-----------------------------------|
|symmetric   |`rel=~rel`                         |
|reflexive   |`(iden & A->A) in rel`             |
|irreflexive |`no (iden & A->A)`                 |
|transitive  |`rel.rel in rel`                   |
|acyclic     |`no (iden & A->A & ^rel)`          |
|total       |`rel + ~rel + (iden & A->A) = A->A`|


[PoEC]: https://www.microsoft.com/en-us/research/publication/principles-of-eventual-consistency/
