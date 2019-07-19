# Ordering guarantees

Chapter 5 of PoEC expresses ordering guarantees as predicates on abstract executions. Here's a few of them,
with the notation from PoEC in the comments.

```alloy
assert ReadMyWrites {
    // (so ⊆ vis)
    so[] in vis
}

assert MonoticReads {
    // (vis ; so) ⊆ vis
    vis.so[] in vis
}

assert ConsistentPrefix {
    // (ar ; (vis ∩ ¬ss)) ⊆ vis def
    ar.(vis-ss) in vis
}

assert NoCircularCausality {
    let so = rb & ss | 
    let hb = ^(so + vis) |
     no (id[E] & ^hb)   
}

assert CausalVisibility {
    hb[] in vis
}

assert CausalArbitration {
    hb[] in ar
}

assert RealTime {
    rb in ar
}

//
// convenience functions
//

// session order
fun so[]: E->E {
    rb & ss
}

// happens before
fun hb[]: E->E {
    ^(so[] + vis)
}
```

Unfortuantely, we can't check the *single order* guarantee with Alloy because that guarantee is
expressed in higher-order logic, and Alloy only supports expressions in first-order logic.

However, if we constrain our traces so that all operations complete, then we can define single order:

```alloy
fact AllOperationsComplete {
    no E.rval & NeverReturns
}

assert SingleOrder {
    vis = ar
}
```

## Checking for violations

We can use Alloy to check if these properties can be violated given the constraints we've put on our model:

```alloy
check NoCircularCausality
```

And, indeed, we get a counterexample:

![circular causality](circular-causality.png).

The problem is:
* (E1,E0) is in *rb*, which means that E1 returned before E0
* (E0,E1) is in *vis*, which means that E0 is visible to E1
