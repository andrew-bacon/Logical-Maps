# Exact versus at-least finite cardinalities (28 October 2026)

The individual cardinality quantifiers have type nu=(et)t. Exact zero
`ZeroCard e` holds precisely of empty properties; at-least zero
`AtLeastZero e` holds of every property. Both use `SucCard`.

## The extra exact-Peano assumption has been eliminated

`ExactLowerPeanoTransfer.lean`, in both the native and checkpoint projects,
proves the following, uniformly in every admissible type sigma:

- `exactPeano_of_lowerPeano`: LowerPeano sigma -> ExactPeano sigma.
- `exactLowerBijection_of_lowerPeano`: LowerPeano sigma -> ExactLowerBijection sigma.
- `necessaryExactPeano_of_box_lowerPeano`: box LowerPeano sigma -> box ExactPeano sigma.
- `exactLowerBijection_of_box_lowerPeano`: box LowerPeano sigma -> ExactLowerBijection sigma.
- `necessaryExactLowerBijection_of_box_lowerPeano`: box LowerPeano sigma -> box ExactLowerBijection sigma.

The boxed premise is definitionally `DraftBoxInfinity sigma` in the checkpoint
and `NecessaryLowerPeano sigma` in the native comparison module. No independent
ExactPeano premise is needed. The original two-premise correspondence theorem
is retained unchanged as a weaker result.

## Proof

Let R be the least binary relation containing the pair of zeros and closed
under simultaneous successor (`ExactLowerPair`). Its projections cover both
inductively specified finite-cardinality carriers, without Peano assumptions.
Define the upward closure of an exact count by

    UpwardCount(q)(X) := exists Y, (forall u, Y(u) -> X(u)) and q(Y).

Induction on R proves that R(q,l) implies, for every X,
`l(X) iff UpwardCount(q)(X)`. The forward successor step adds the selected
individual back to an exact subproperty; the reverse step removes it. Exact
finite cardinalities respect current coextension, as proved in Cardinality.lean.

A second induction proves persistence: R(q,l) implies box R(q,l). The base
and step use necessitations of closed pairing-introduction theorems, never
necessitation of an open hypothesis.

If R(q,l) and R(q,l'), their upward-closure characterizations give current
coextension. Persistence of both pairings and the necessitated coextension
theorem give NECESSARY coextension, so Intensionality gives l=l'. This proves
right uniqueness without any Peano premise and without unrestricted extensionality.

Exact zero is not a successor: evaluate both quantifiers on the empty property.
For finite exact m,n with Suc(m)=Suc(n), choose lower partners l,k. Right uniqueness
at the successors gives Suc(l)=Suc(k). LowerPeano yields l=k, and the earlier
left-uniqueness theorem yields m=n. Thus LowerPeano implies ExactPeano.
The earlier two-premise bijection theorem now applies. K and Necessitation give
the boxed corollaries.

The graph relates the two zeros and is closed under simultaneous successor,
in addition to being total and one-to-one in both directions. No primitive
natural-number index, function choice, RC, IC or BF premise is introduced.

## Verification boundary

The modules invoke both `#classicism_check` and `#classicism_types` on every
new lemma. CI run 40752908468 is the first targeted run of the new transfer
modules; the checkpoint job successfully compiled them and passed both audits.
Consult that run for the final native-job status. Source dependencies may use
build caches; this is not a claim to rebuild the entire checkpoint from scratch.

The map records remain `lean: none`. Compiling these proofs and passing the
Classicism gate/type audits is not the separate object-language derivation and
map-generated-statement certification required by `pmap lean-check`.

## Not asserted

This result does not by itself derive strong rigidity of LowerNat, produce a
single rigid graph valid everywhere, transport every arithmetic operation, or
construct a real-number structure. The boxed conclusion says necessarily a
bijection exists. No converse ExactPeano -> LowerPeano is claimed here.
