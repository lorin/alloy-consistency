---
title: Eventual consistency and Alloy
---

# Overview

In [Principles of Eventual Consistency][PoEC] (PoEC), Sebastian
Burckhardt introduces an approach for reasoning about eventually consistent data
types. His approach relies heavily on *event graphs*, which are defined using sets, relations, and first order logic.

This sounds like a good fit for the [Alloy modeling
language](http://alloytools.org/), which is also based on sets, relations, and
first order logic.

Note: PoEC is written as a book in PDF format. It is free to download.

# Using Alloy to model relations

Here's an example of how well suited Alloy is to Burckhardt's approach. On page 22 of PoEC, Burckhardt has a table properties of
binaries relations, along with their algebraic definitions. Translating from the algebraic definitions to Alloy is straightforward.


|Property    |Algebraic definition                          |Alloy syntax                       |
|------------|----------------------------------------------|-----------------------------------|
|symmetric   |rel=rel<sup>-1</sup>                          |`rel=~rel`                         |
|reflexive   |id<sub>A</sub> ⊆ rel                          |`(iden & A->A) in rel`             |
|irreflexive |id<sub>A</sub> ∩ rel= ∅                       |`no (iden & A->A & rel`            |
|transitive  |(rel;rel) ⊆ rel                               |`rel.rel in rel`                   |
|acyclic     |id<sub>A</sub> ∩ rel<sup>+</sup> = ∅          |`no (iden & A->A & ^rel)`          |
|total       |rel ∪ rel<sup>-1</sup> ∪ id<sub>A</sub> = A×A |`rel + ~rel + (iden & A->A) = A->A`|


[PoEC]: https://www.microsoft.com/en-us/research/publication/principles-of-eventual-consistency/


# Example: register


As our motivating example, we're going to use Alloy to model the behavior of a
register. A register is a very simple data structure that holds a single value.

A register supports two operations: *read a value* and *write a value*.

## Abstract executions

We'll use alloy to generate an *abstract execution* for a register. PoEC defines abstract executions
in section 3.2 (p34).

An abstract execution is made up of:

* E - set of events
* op - relation that maps events to operations
* rval - relation that maps events to values returned by the operation
* rb - "returns before" relation that captures which operations returned before which other ones
* ss - "same session" relation that captures which operations are part of the same "session" (you can think of as a thread or process)
* vis - visibility relation
* ar - arbitration relation



```alloy
abstract sig ReturnValue  {}

sig Value extends ReturnValue {}

one sig Undef extends ReturnValue {}

abstract sig Operation {}

sig Read extends Operation {}

sig Write extends Operation {
	value: Value
}

sig Event {
    op: Operation,
    rval: ReturnValue,
    rb: set Event,
    vis: set Event,
    ar: set Event
}


// Definition 3.1 on page 32
// (h3) rb is a natural partial order on E, the returns-before order.<Paste>
// Partial orders are irreflexive and transitive (Section 2.1.3, p21)
fact ReturnsBeforeIsNaturalPartialOrder {

// irreflexive
no (iden & Event->Event & rb)

// transitive
rb.rb in rb
}

// Definition 3.1 on page 32
// (h4) ss is an equivalence relation on E, the same-session relation.
// Equivalence relations are reflexive, transitive, and symmetric (Section 2.1.3, p22)
fact SameSessionIsAnEquivalenceRelation {
// reflexive
(iden & Event->Event) in ss

// transitive
ss.ss in ss

// symmetric
ss=~ss
}



```

Let's see an example:

```alloy
run {#vis > 0}
```


