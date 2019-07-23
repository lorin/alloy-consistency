let id[A] = A<:iden

// events
sig E {
    eo: set E,
    tr: Tr,
    role: R,
    del : E,
}

// Transition
abstract sig Tr {
}

sig init extends Tr {
    post : State,
    M : set Message
}

sig call extends Tr {
    op : Op,
    pre: State,
    post: State,
    M : set Message
}

sig rcv extends Tr {
    m : Message,
    pre: State,
    post: State,
    M : set Message
}

sig step extends Tr {
    p : P,
    pre: State,
    post: State,
    M: set Message
}

sig callret extends Tr {
    op : Op,
    pre: State,
    post: State,
    M : set Message,
    v : V
}

sig rcvret extends Tr {
    m : Message,
    pre: State,
    post: State,
    M : set Message,
    v : V
}

sig stepret extends Tr {
    p : P,
    pre: State,
    post: State,
    M: set Message,
    v : V
}



// values
sig V {}

// processes
sig P {}

// operations
sig Op {}

// roles
sig R {}

// messages
sig Message {}

sig State {}

fact eoIsEnumeration { 
     // enumeration is total order and natural
     // alloy models are finite so we just need to check for total order


     // Total orders are partial orders which are also total
     // partial ordres are irreflexive and transitive


    // irreflexive
    no id[E] & eo

    // transitive
    eo.eo in eo

    // total
     eo + ~eo + id[E] = E->E
}


pred isTrajectory[es : set E, eo : E->E, tr: E->Tr] {
}

fact eventsForEachRoleAreTrajectories { 
    all r : R | isTrajectory[role.r, eo, tr]
}

fact delConstraints {
    // injective
    no disj e1,e2 : E | e1.del=e2.del


    // ∀s,r∈E: s−→r ⇒ s−→r ∧ rcv(r)∈snd(s)

    // We can't define this until we define snd and rcv
    // all s,r : E | s->r in del => {s->r in eo  rcv(r) in snd(s)

}

run {}
