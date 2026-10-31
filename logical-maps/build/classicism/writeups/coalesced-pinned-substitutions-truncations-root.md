# Coalesced sum: substitution arrows over the truncations model

<p class='cert'>Model — Source: Misc.; produced by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts, 29 October 2026 (a variant of Cian Dorr's coalesced-pinned-substitutions-root with one chosen component); recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 29 October 2026.</p>

## Package

- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **□Self-atoms are atoms.** Necessarily, at each relational type, every self-atom is an atom.
- **□Self-atoms are strong atoms.** Necessarily, at each relational type, every self-atom is a strong atom: it necessarily entails every entity of the type or its negation.
- **¬ □Atomlessness.** Necessarily, every possible proposition has a possible proposition strictly below it.
- **¬ Self-Atomicity (type t).** Every possible proposition is entailed by a self-atom: a possible proposition that necessarily, if true, is an atom, that is, one that entails that it is the actual world.

## Definition

As in coalesced-pinned-substitutions-root, with a single component in place of a family complete for C($\Sigma$): the one-object model finite-support-truncations, with object $V$. The root $W_0$ has an arrow $\langle V,I\rangle$ for each interpretation $I$ of $\Sigma^+$ at $V$ and an arrow to itself for each type-preserving map of the constants of $\Sigma^+$. Evaluation point: $W_0$, at its identity arrow. Interpretation of Σ as there. The write-up's argument that the root is a model of C uses only that each component is an action model of C.

As for interpretation arrows, and the root has besides an arrow to itself for every type-preserving map of the signature's constants to themselves, acting on the root's individuals and composing with the interpretation arrows by precomposition.

As in coalesced-pinned-substitutions-root, intensions over the arrows out of $W_0$ pinned down by a finite set of constants of $\Sigma^+$, whose transports along the arrows into $V$ land in its domains.

*A member of the group Coalesced sums at a new root, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Atomlessness. Fails □Atomlessness.

Atomlessness holds at $W_0$ by the argument atomlessness of coalesced-pinned-substitutions-root, which needs of the component only that $\top\ne\bot$ there. It fails at $V$, where Atomicity (type t) holds, the singletons $\{g_n\}$ being atoms, and $V$ is reachable; so $\Box$Atomlessness fails.

*Address: `coalesced-pinned-substitutions-truncations-root#atomlessness`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; checked by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*

### Holds □Self-atoms are atoms, □Self-atoms are strong atoms. Fails Self-Atomicity (type t).

A self-atom of any relational type at an object $W$ is instantiated at some arrow $k$ out of $W$, and its transport along $k$ is an atom at $k$’s target instantiated at the identity there. The existential projection of an atom $I$ of a relational type, the proposition $\exists\bar x\, .\,I\bar x$, is an atom of type $t$: it is in the domain, it is not bottom, and for any proposition $p$ the entity $I\land\lambda\bar x\, .\,p$ lies below the atom $I$, so is $I$ or bottom, which puts $p$ above the projection or disjoint from it. So the projection is a true atom at $k$’s target, which the condition excludes. Hence no reachable object has a self-atom, and Self-atoms are atoms and Self-atoms are strong atoms hold vacuously at every type and every reachable object, while Self-Atomicity (type t) fails at the evaluation point, the top proposition having no self-atom below it.

*General argument `arguments/no-actuality-no-self-atoms`. It requires that Actuality fails at the identity of every object reachable from the evaluation point: no atom of the domain of propositions there contains that identity. In a one-object model this is the failure of Actuality at the evaluation point, Actuality being a closed sentence. Here: The objects reachable from $W_0$ are $W_0$ and $V$. Actuality fails at $V$, as recorded for finite-support-truncations, and at $W_0$, where Atomlessness holds (argument atomlessness), there being no atom at all. By Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 25 October 2026.*


## Notes

Proposed on 29 October 2026 in a trawl for the open questions created by □Atomlessness, to show that Atomlessness with the bridge principles for self-atoms, boxed or not, does not give □Atomlessness: with no Actuality anywhere there are no self-atoms, by the argument no-actuality-no-self-atoms. Checked by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr; it inherits the model-of-C argument of coalesced-pinned-substitutions-root, which has not had a second reader. No Lean verification is claimed.

## Sources

- **Dorr 19 Oct** — Cian Dorr, construction of 19 October 2026 (coalesced-pinned-substitutions-root), with Claude Opus 5.5 (Anthropic); the choice of component here by Claude Opus 5.5 (Anthropic), 29 October 2026.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Proposition D.5, part 6, pp. 74, 78; Appendix E, Definition E.2, pp. 80–83.

<p class='cert'>Record: <code>topics/classicism/models/coalesced-pinned-substitutions-truncations-root.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–78; Appendix E, pp. 80–83
