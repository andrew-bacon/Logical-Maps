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

## Verification completed for the three map arrows

CI run 40752908468 passed both targeted Lean builds and the Classicism
admissibility/type audits for the transfer proof. Native object-language
certification then passed in run 40756304227: all three fixed-e map implications
have C-minus derivations and schema entailments, using only `propext` and
`Quot.sound` in their Lean axiom reports.

The final native map audit passed in fork run 40756833756. It ran the unchanged
command `python3 scripts/pmap.py lean-check classicism --update`, checked the
certificates against the statements generated from the actual map records,
and published the resulting metadata in commit
`7d69e1cee3fbc09d5f56ec8434a7a01b5750a399`. The three results now have
`certificate.lean: verified`:

- `necessary-lower-peano-implies-exact-peano-e`
- `necessary-lower-peano-implies-cardinality-bijection-e`
- `exact-peano-and-necessary-lower-peano-imply-cardinality-bijection-e`.

The native files `Classicism/Certified/ExactLower.lean` and
`Classicism/MapExactLower.lean` contain the object-language and exact
map-statement certificates respectively. The machine-written evidence is
`../lean/map/exact-lower-audit.json`; the native map index includes all three
certificate references and source locations. This is not a claim that the
entire standalone checkpoint was rebuilt from scratch.

These records are eligible for the site's Lean badge when the source is
merged and the website rebuilt. No generated website exports are committed.

## Not asserted

This result does not by itself derive strong rigidity of LowerNat, produce a
single rigid graph valid everywhere, transport every arithmetic operation, or
construct a real-number structure. The boxed conclusion says necessarily a
bijection exists. No converse ExactPeano -> LowerPeano is claimed here.
The full CH-contingency map arrow is not certified by this arithmetic audit.
