# Bounded forcing and necessary Peano conditions imply cardinal CH contingency

Andrew Bacon's CH-contingency development; formalization and native integration by
OpenAI Codex, prompted by Andrew Bacon, 29 October 2026. The arithmetic rigidity
argument is due to Zachary Goodsell, *Arithmetic is Determinate* and
*Arithmetic is Necessary* (especially the latter's Lemmas 3 and 8).

## Statement and scope

Let $N$ be the inductively defined property of at-least finite-cardinality
quantifiers at type $e$, and let $S=\operatorname{RigidPower}(N)$.
Write $C_N=\operatorname{CardinalCH}(N,S)$ for the cardinal CH statement in
[[cardinal-continuum-hypothesis]]. The result is

$$
\text{Bounded CH forcing setup}\;\land\;\text{Necessary lower-Peano}
\quad\Longrightarrow\quad \Diamond C_N\land\Diamond\neg C_N.
$$

The setup is [[bounded-ch-forcing-setup]], not Forcing Possibilism alone.
It asserts a common strongly inaccessible well-order $(K,L)$, the two
specified forcing-possibilism instances, the finite boxed RC bundles
`NaturalPositiveRC` and `NaturalNegativeRC`, the boxed Cohen-completion RC
instance, and the three unboxed IC instances `NaturalCHChoice`.
The type of $K$ is a schema parameter. The statement does not quantify over
types in the object language.

[[necessary-lower-peano-e]] asserts necessarily that lower zero is not a
successor and that successor is injective on the lower-natural carrier.
It is not identified here with an axiom asserting infinitely many individuals.
The conclusion is cardinal CH contingency. A bridge to structural CH about
real-number structures remains a separate conjecture.

## Proof

**1. Derive rigidity from the existing RC package.**
Take the `rcFreeze` conjunct of `NaturalPositiveRC`. The theorem
`naturalPositiveRC_box_countable` derives boxed countable Boolean completeness
at the property type required by the lower-natural carrier. Goodsell's
singleton-supremum argument, formalized as `lowerNat_rigid_of_box_countable`,
then yields $\operatorname{Rigid}(N)$. Thus the setup already implies
[[rigid-lower-nat-e]]; neither the necessary Peano premise nor an additional
rigidity premise is used in this step.

**2. Supply the Hartogs bounds and Boolean completions.**
The carrier-relative development constructs the inductive Hartogs carriers
and proves the closed-segment embedding bounds required at $N$ and at its
Hartogs carrier. The regular-open construction supplies the completions of
the two forcing orders. These are derived lemmas, not additional premises
in the displayed result. The construction and size bounds use the explicit
RC, IC, Peano and inaccessible-witness assumptions in the setup.

**3. Obtain the two possibilities.**
The countable-bit forcing instance yields a possibility satisfying the
order-type form of CH; the carrier comparison gives $\Diamond C_N$.
The Cohen forcing instance on the double-Hartogs coordinates yields the
injection obstructions establishing $\Diamond\neg C_N$. Both arguments use
the same $N$ and $S$, and both forcing instances use the same $(K,L)$.
`natural_CH_contingency_closedBounds` assembles these conclusions under the
rigidity premise supplied in step 1.

**4. Assemble the map implication.**
`natural_CH_contingency_from_principles` performs that substitution and gives
`NaturalCHContingency`, a conjunction of order-type and cardinal contingency.
The map proof unpacks the existential setup and projects the cardinal conjunct.

## Native proof locations

- `lean/Classicism/Principles/MathematicalContingency.lean`: map definitions.
- `lean/Classicism/Results/MathematicalContingency/`: arithmetic, Hartogs,
  regular-open and forcing proofs, culminating in `GoodsellCH.lean`.
- `lean/Classicism/Results/Records/MathematicalContingency.lean`: exact map arrows.
- `lean/Classicism/Certified/MathematicalContingency/`: object-language derivations,
  including the checkpoint-142 endpoint `GoodsellCH03.lean`.


The old three-premise arrow
[[bounded-forcing-and-rigid-naturals-imply-cardinal-ch-contingency]] is retained
with its original identifier. This result removes its redundant rigidity premise.
The map's Lean status is assigned only by its normal certificate audit; historical
checkpoint logs are not a substitute for that audit.

The source theorem and the three exact shallow map wrappers pass the native
Classicism gate and type-system checks. Native schema reflection for the large
forcing setup exceeded the available memory, so these arrows retain
`lean: none`: a certificate at the generated map statement type is still pending.
