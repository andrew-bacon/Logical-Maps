# Modalized domains: Cohen cloud

Source: [*Modalized Domains on Possibility Frames*](https://andrew-bacon.github.io/techdoc/modalized-domains.pdf), Andrew Bacon and Claude Opus 5.5 (Anthropic), draft of 20 October 2026; §4, Theorem 4.4 and Corollary 4.5. Transcribed by OpenAI Codex on 21 October 2026. No independent checker or Lean verification is claimed.

## Construction

Work in ZFC. Use the one-element family consisting of the Cohen algebra RO(Fn(ω,2)). Take the disjoint union of the nonzero parts of these complete Boolean algebras, with refinement given by their Boolean orders, and adjoin a refinement-isolated root r. The root sees every point and each cloud point sees its refinements. Use the full modalized-domain model of Definitions 2.1–2.10 and 4.1, with constant individual domain ω and literal individual identity. At t use all regular-open propositions; at function types use the full underlying function sets with the partial equivalence relations of Definition 2.2. Quantification uses existing entities at all refinements, as in §2.3. Evaluate at r. Interpret any relational signature constants as top; no signature verdict is recorded.

## Verified properties (paper proofs)

### Holds: necessary-rigid-comprehension-r

The frame is a world–cloud frame. At transparent cloud points every relation is rigid. At the isolated root, the check-closure of an actual extension is a coextensive rigid relation (Definition 3.11 and Theorem 3.12). Thus RC holds at every point, and each boxed instance is valid. Source: Theorem 3.12, pp. 17–18; Theorem 4.4(b), p. 21.

### Holds: necessary-intensional-choice-r

Theorem 3.14 selects witnesses on a maximal antichain of decided cloud pieces and mixes their identity profiles. At a world, choose one actual witness; the world part and the cloud mixture together form a necessarily uniquely instantiated subrelation of the given necessarily instantiated relation. Hence IC and its necessitation are valid. The proof uses ZFC. Source: Theorem 3.14, pp. 18–19; Theorem 4.4(b), p. 21.

### Holds: necessary-barcan-r

Lemma 4.3 proves no new entities at any type: at a cloud point x a relation can be cut down to the regular-open closure of the principal downset of x, yielding an entity existing at the root and identical to the original at x. Proposition 3.16 therefore gives BF and □BF at every type. This uses the paper’s variable-domain quantifiers, not a fixed-domain meet calculation. Source: Lemma 4.3 and Theorem 4.4(b), pp. 20–21.

### Fails: atomicity-t

The component proposition for an atomless factor is nonzero. At the root, propositional identity is literal and entailment is inclusion, so its lower interval is the atomless factor algebra. It therefore has no propositional atom below it. Source: Theorem 4.4(d), p. 21.

### Fails: distinctness-necessary-t

The top proposition S and the cloud S minus {r} are distinct at the root, but identical at every cloud point. They witness failure of ND at type t. Source: Theorem 4.4(c), p. 21.

## Scope

Theorem A. This is the full modalized-domain model of the paper, with world-indexed existence and identity. The construction and its proofs are source-reported mathematical evidence, not Lean verification.

## Supporting results

Propositions 1.4 and 1.6 provide the regular-open Boolean algebra and modal operator. Proposition 2.11 supplies full models; Theorem 3.4 supplies soundness for Classicism. Theorems 3.12 and 3.14 provide the comprehension and choice arguments, and Proposition 3.16 provides the no-new-entities criterion for BF. These are construction-level results, recorded as proof dependencies rather than new object-language principle nodes. Section 5 additionally uses the rooted-sum transfer theorem 5.6. Section 6 uses the cardinal arithmetic and extensional-fullness lemmas 6.1–6.7. The E-dependent results of §7 are outside this contribution.

## Paper references

- **Proof: [Modalized Domains on Possibility Frames](https://andrew-bacon.github.io/techdoc/modalized-domains.pdf).** Andrew Bacon and Claude Opus 5.5 (Anthropic), Modalized Domains on Possibility Frames, draft of 20 October 2026. — Theorem A; Corollary 4.5, p. 21
