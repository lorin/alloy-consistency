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
|irreflexive |id<sub>A</sub> ∩ rel= ∅                       |`no (iden & A->A & rel)`           |
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

The convention we'll use for return values is:

* For writes, the return value is `OK`
* For reads, the return value is either a legitimate value, or `Undef` if the register has never had a value written before:

# Allow model

In our alloy model, we'll define an E *signature*, and op,rval,rb,ss,vis,ar fields to model the relations.

I'd normally call this "Event" instead of "E", but I'll use "E" here to be
consistent with Burckhardt's syntax, and because it will make things a little shorter.

## Events

```alloy
sig E {
    op: Operation,
    rval: Value + Undef + OK,
    rb: set E,
    ss: set E,
    vis: set E,
    ar: set E
}
```

Note how the "op" and "rval" relations map an event to an individual element, and the other relations map an event to a set of events.

Next, we need to define *Operation, Value, Undef, OK*.

## Values

*Value* is just a set of values, it's the simplest possible definition of an Alloy signature:

```alloy
sig Value {}
```

*Undef* and *OK* are special values, we model those as singleton sets:

```alloy
one sig Undef {}

one sig OK {}
```

## Operations

To model operations, we need to model reads and writes. 

Writes also have return values, so we need a field on the *Write* signature that associates a write with a value.

```alloy
abstract sig Operation {}

sig Read extends Operation {}

sig Write extends Operation {
	value: Value
}
```

## Constraints on relations

There are a number of constraints we need to enforce on some of the relations. In particular:

* *rb* is a partial order on *E*, the returns-before order. (Definition 3.1, p32)
* *ss* is an equivalence relation on *E*, the same-session relation.  (Definition 3.1, p32)
* *vis* is an acyclic relation. (Definition 3.3, p35)
* *ar* is a total order (Definition 3.3, p35)


```alloy
fact ReturnsBeforeIsPartialOrder {
// Partial orders are irreflexive and transitive (Section 2.1.3, p21)

// irreflexive
no (iden & E->E & rb)

// transitive
rb.rb in rb
}

fact SameSessionIsAnEquivalenceRelation {
// Equivalence relations are reflexive, transitive, and symmetric (Section 2.1.3, p22)

// reflexive
(iden & E->E) in ss

// transitive
ss.ss in ss

// symmetric
ss=~ss
}

fact VisibilityIsAcyclic {
no (iden & E->E & ^vis)
}

fact ArbitrationIsTotalOrder {
// total order is partial order and total
// partial order is irreflexive and transitive
// order defintion is in section 2.1.3

// irreflexive
no (iden & E->E & ar)

// transitive
ar.ar in ar

// total
ar + ~ar + (iden & E->E) = E->E
}
```

## Register constraints

We need to constrain the return values so they match the operations.

* A write operation always returns *OK*
* A read operation returns either an ordinary value, or a special value, *Undef*, if it has not been intialized with a value.


```alloy
fact WritesReturnOK {
all e : E | e.op in Write => e.rval = OK
}

fact ReadsReturnValuesOrUndef {
all e : E | e.op in Read => e.rval in (Value + Undef)
}
```

We also add one last constraint, to capture the semantics of our register: a
read always corresponds to the last visible write in arbitration order, or
*Undef* if there is no visible write.

```alloy
fact ReadLastVisibleWrite {
	all r : reads[] | 
		let lvw = lastVisibleWrite[r] | 
		some lvw => r.rval=lvw.op.value else r.rval=Undef
}

//
// convenience functions
//

fun lastVisibleWrite(e: E): lone E {
	{w : writes[] | w->e in ar and no ww : writes | w->ww in ar and ww->e in ar}
}

fun reads(): set E {
	{w : E | w.op in Read}
}

fun writes(): set E {
	{w : E | w.op in Write}
}
```


## Other constraints

We don't want Alloy to generate any orphaned *Operation* instances, so we
specify that all operations have to be associated with an event.


```alloy
fact AllOpsAreAssociatedWithEvents {
all o : Operation | some op.o
}
```

## Running the model



```alloy
run {some Read and some Write and some vis}
```


