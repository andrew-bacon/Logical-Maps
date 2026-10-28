# Exact versus at-least finite cardinalities (28 October 2026)

The individual cardinality quantifiers have type ν=(et)t. The *exact* zero
`ZeroCard e` is the property true of precisely empty properties; the
*at-least* zero `AtLeastZero e` is the universal property of properties.
Both use the same `SucCard` operator.

We define a binary relation `ExactLowerPair` as the least relation containing
the pair of zeros and closed under simultaneous successor. Using impredicative
induction, Lean proves that its projections cover **both** inductively
specified finite-cardinality carriers, without any Peano assumptions.

The theorem `exactLowerBijection_of_peano` proves that this relation is a
bijection when both carriers satisfy zero/non-successor and successor-injectivity.
The stronger-to-use corollary `exactLowerBijection_of_draft_box_infinity` takes
exact Peano and the *boxed* at-least Peano premise of the CH proof. The map-side
analogue is `Classicism.ExactLower.exactLowerBijection_of_necessary_lower_peano`.

**Important limitation:** This is NOT yet a proof that *at-least Peano alone*
entails the exact Peano conditions, or of an unconditional bijection in arbitrary
models. The extra exact-Peano hypothesis is made explicit. No new axiom has been
postulated in the Lean libraries: these are theorems **from** supplied hypotheses.

The map claim is currently `status: proved` from the mathematical induction,
but `lean: none` until the map's own statement-and-axiom check confirms it.
The local `.lean` files contain no `sorry` or new axiom declarations.
