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
    op: Op+Bottom,
    rcv: Message+Bottom,
    proc: P+Bottom,
    pre: State+Bottom,
    post: State,
    snd: set Message,
    rval: V+Bottom
}

sig init extends Tr {
    σ': State,
    M : set Message
}

sig call extends Tr {
    o : Op,
    σ: State,
    σ': State,
    M : set Message
}

sig rcv extends Tr {
    m : Message,
    σ: State,
    σ': State,
    M : set Message
}

sig step extends Tr {
    p : P,
    σ: State,
    σ': State,
    M: set Message
}

sig callret extends Tr {
    o : Op,
    σ: State,
    σ': State,
    M : set Message,
    v : V
}

sig rcvret extends Tr {
    m : Message,
    σ: State,
    σ': State,
    M : set Message,
    v : V
}

sig stepret extends Tr {
    p : P,
    σ: State,
    σ': State,
    M: set Message,
    v : V
}


// ⊥
sig Bottom {}



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


pred isEnumeration[es: E, r:E->E] {
     // enumeration is total order and natural
     // alloy models are finite so we just need to check for total order


     // Total orders are partial orders which are also total
     // partial ordres are irreflexive and transitive


    // irreflexive
    no id[es] & r

    // transitive
    r.r in r

    // total
     es->es in r + ~r + id[es] 
}

fact eoIsEnumeration { 
    isEnumeration[E,eo]
}


// predecessor
fun prd[E': set E, r:E->E, e: E] : E+Bottom {
    let es = r.e |
        (some es) =>
            {e' : es | no f: es |  e'->f in r}
            else Bottom
}

fun calls[E' : set E] : set E {
    {e: E' | e.tr.op != Bottom}
}

fun returns[E' : set E] : set E {
    {e : E' | e.tr.rval != Bottom}
}

pred isTrajectory[E' : set E, eo' : E->E, tr': E->Tr] {
    // (t1) eo is an enumeration of E.
    isEnumeration[E', eo']

    // (t3) The first (and only the first) transition is an initialization
    // transition, and the pre-state of each transition matches the
    // post-state of the previous transition:
    // ∀e ∈ E : 􏰁 pre(e) = ⊥ = pred(E,eo,e)
    // ∨ pre(e) = post(pred(E, eo, e)) 􏰂
    all e : E' | {
        e.tr'.pre = Bottom
        prd[E',eo,e] = Bottom
    } or e.tr'.pre = prd[E',eo',e].tr.post


    // (t4) A call transition may not follow another call transition unless there is a return transition in between them:
    // ∀c1, c2 ∈ calls(E) : c1 <eo c2 ⇒
    // ∃r ∈ returns(E) : c1 ≤eo r <eo c2
    all disj c1,c2 : calls[E'] | c1->c2 in eo' => some r : returns[E'] | {c1->r in eo'  r->c2 in eo'}
}

// TODO: implement this and check that all trajectories are well-formed
//pred isWellFormed[E': set E, eo':E->E, tr': E->Tr] {
//}

fact eventsForEachRoleAreTrajectories { 
    all r : R | let E'=role.r |
        isTrajectory[E', E'<:eo:>E', E'<:tr]
}

fact delConstraints {
    // injective
    no disj e1,e2 : E | e1.del=e2.del


    // ∀s,r∈E: s−→r ⇒ s−→r ∧ rcv(r)∈snd(s)

    // We can't define this until we define snd and rcv
    // all s,r : E | s->r in del => {s->r in eo  rcv(r) in snd(s)

}

run {}
