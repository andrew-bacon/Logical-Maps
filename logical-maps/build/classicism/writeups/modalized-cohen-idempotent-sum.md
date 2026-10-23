# Modalized domains: Cohen–idempotent rooted sum

Source: [*Modalized Domains on Possibility Frames*](https://andrew-bacon.github.io/techdoc/modalized-domains.pdf), Andrew Bacon and Claude Opus 5.5 (Anthropic), draft of 20 October 2026; §5, Theorem 5.8. Transcribed by OpenAI Codex on 21 October 2026. No independent checker or Lean verification is claimed.

## Construction

Work in ZFC. Form M_C ⊕ M_k by Definition 5.2. M_C is the full modalized-domain model on the forcing frame of the Cohen algebra RO(Fn(ω,2)), with constant individuals ω. M_k is the rooted Kripke modalized-domain model obtained by unravelling the full one-object action model on the monoid {1,k}, k²=k, with a single individual, as in §5.3. The new refinement-isolated root sees both components and itself. Actual individuals are a disjoint copy of ω, mapping identically into M_C and constantly to the sole individual of M_k. Underlying domains, component projections and root partial identities are those of Definition 5.2, not the full function-space construction. Evaluate at the new root. Interpret any relational signature constants as top; no signature verdict is asserted.

## Verified properties (paper proofs)

### Holds: necessary-rigid-comprehension-r, necessary-intensional-choice-r

The Cohen component is rigidifiable and admits global choice by Lemma 5.5(a). The idempotent action model validates □RC, is extensionally full at its root, and validates □IC by the natural selector constructed in Lemma 5.7. Its unravelled modalized-domain model therefore satisfies Lemma 5.5(b). The transfer theorem 5.6(b,c) gives RC and IC at the new root and throughout both components, hence □RC and □IC. Source: Lemmas 5.5 and 5.7; Theorems 5.6(b,c) and 5.8, pp. 24–27.

### Fails: barcan-t

In the full action model on {1,k}, k sends every proposition to top or bottom while four propositions remain available at the target. Thus its action at t is not surjective and BF_t fails (Lemma 5.7(c)). Unravelling preserves the relevant truth at its minimal root. Theorem 5.6(d) lifts a witnessing predicate to the rooted sum, using top in the other component and an everywhere-true root extension. All actual propositions satisfy it necessarily, while universal instantiation fails in the idempotent component. Source: Theorem 5.6(d), Lemma 5.7(c), and Theorem 5.8, pp. 25–27.

### Fails: atomicity-t

The everywhere-existing propositions of the Cohen component form its atomless complete Boolean algebra. Extend its top to be false at the new root and in the other component. It is a nonzero actual proposition with no atom below it, by Theorem 5.6(f). Source: Theorems 5.6(f) and 5.8, pp. 25–27.

### Fails: distinctness-necessary-t

S and S minus the new root exist there and are distinct, but have identical component projections and hence are identical throughout both components. Theorem 5.6(e) gives failure of ND_t. Source: Theorems 5.6(e) and 5.8, pp. 25–27.

## Scope

Theorem B. The chain description in §5.3 is intuition for the unravelling, not a replacement for the source’s action-model construction. No propositionally full world–cloud model is claimed here: Proposition 5.1 explains why that simpler construction cannot refute BF_t. Mathematical evidence is supplied by the cited paper; no independent checker or Lean certificate is asserted.

## Supporting results

Propositions 1.4 and 1.6 provide the regular-open Boolean algebra and modal operator. Proposition 2.11 supplies full models; Theorem 3.4 supplies soundness for Classicism. Theorems 3.12 and 3.14 provide the comprehension and choice arguments, and Proposition 3.16 provides the no-new-entities criterion for BF. These are construction-level results, recorded as proof dependencies rather than new object-language principle nodes. Section 5 additionally uses the rooted-sum transfer theorem 5.6. Section 6 uses the cardinal arithmetic and extensional-fullness lemmas 6.1–6.7. The E-dependent results of §7 are outside this contribution.

## Paper references

- **Proof: [Modalized Domains on Possibility Frames](https://andrew-bacon.github.io/techdoc/modalized-domains.pdf).** Andrew Bacon and Claude Opus 5.5 (Anthropic), Modalized Domains on Possibility Frames, draft of 20 October 2026. — Theorem B; Theorem 5.8, p. 27
