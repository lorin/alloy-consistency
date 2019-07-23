let id[A] = A<:iden

// events
sig E {
    eo: set E,
    tr: Tr,
    role: R,
    del : E,
}

// Transition
sig Tr {}


// roles
sig R {}

// messages
sig M {}

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
