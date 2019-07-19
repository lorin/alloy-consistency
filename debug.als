let id[A] = A<:iden

sig E {
    op: Operation,
    rval: Value + NeverReturns,
    rb: set E,
    ss: set E,
    vis: set E,
    ar: set E
}

sig Value {}

sig V extends Value {}

one sig Undef extends Value {}

one sig OK extends Value {}

one sig NeverReturns {}

abstract sig Operation {}

sig Read extends Operation {}

sig Write extends Operation {
    value: V
}

run {some E} 


/*
fact ReturnsBeforeIsPartialOrder {
    // Partial orders are irreflexive and transitive (Section 2.1.3, p21)

    // irreflexive
    no id[E] & rb

    // transitive
    rb.rb in rb
}

fact SameSessionIsAnEquivalenceRelation {
    // Equivalence relations are reflexive, transitive, and symmetric (Section 2.1.3, p22)

    // reflexive
    id[E] in ss

    // transitive
    ss.ss in ss

    // symmetric
    ss=~ss
}


fact VisibilityIsAcyclic {
    no id[E] & ^vis
}

fact ArbitrationIsTotalOrder {
    // total order is partial order and total
    // partial order is irreflexive and transitive
    // order defintion is in section 2.1.3

    // irreflexive
    no id[E] & ar

    // transitive
    ar.ar in ar

    // total
    E->E in ar + ~ar + id[E]
}

fact WritesReturnOK {
    all w : op.Write | w.rval = OK
}

fact ReadsReturnValuesOrUndef {
    all r : op.Read | r.rval in (Value + Undef)
}

fact ReadLastVisibleWrite {
    all r : op.Read | 
        some (op.Write & vis.r) => r.rval=lastVisibleWrite[r].op.value else r.rval=Undef
}

fun lastVisibleWrite(e: E): lone E {
    {w : op.Write | w->e in vis and no ww : op.Write | ww->e in vis and w->ww in ar}
}

fact AllOpsAreAssociatedWithEvents {
    all o : Operation | some op.o
}

fact OnlyOneWriter {
    all w1,w2: op.Write | w1->w2 in ss
}

pred RegularRegisterValidity[] {
// A read that is not concurrent with a write returns the last value written
all r : op.Read | 
    (no w : op.Write | areConcurrent[r,w]) => r.rval = lastValueWritten[r]


//  a read that is concurrent with a write returns the last value written or the value currently written.
all r : op.Read |
    (some w : op.Write | areConcurrent[r,w]) =>
        r.rval = lastValueWritten[r] or r.rval = {w:op.Write | areConcurrent[r,w]}.op.value
}

// helpers

fun lastValueWrittenWRONG[e : E] : Value { // This is actually wrong, we'll see later
    {w : op.Write | (w->e in rb) and (no w2 : op.Write | w2->e in rb and w->w2 in rb)}.op.value
}

pred areConcurrent[e1,e2 : E] {
    e1->e2 not in rb
    e2->e1 not in rb
}

assert IsRegularRegister {
    RegularRegisterValidity[]
}


fun lastValueWritten[e : E] : Value {
    let mostRecentWrite = {w : op.Write | (w->e in rb) and (no w2 : op.Write | w2->e in rb and w->w2 in rb)} |
        some mostRecentWrite=>mostRecentWrite.op.value else Undef
}

fact WritesFromTheFutureAreNeverVisible {
    no r,w : E | r in op.Read and w in op.Write and r->w in rb and w->r in vis
}

fact WritesThatReturnBeforeReadsAreVisible {
    all r : op.Read | all w : op.Write | w->r in rb => w->r in vis
}

fact ArbitrationConsistentWithReturnsBefore {
    rb in ar
}

fact NoConcurrencyInSameSession {
    // For any two events, if they are in the samee session, one must return before the other

    all e1,e2: E | e1->e2 in ss => e1->e2 in (rb + ~rb)
}
*/
