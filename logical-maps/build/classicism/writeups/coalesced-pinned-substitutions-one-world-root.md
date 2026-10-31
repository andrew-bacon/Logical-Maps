# Coalesced sum: substitution arrows over a one-world component

<p class='cert'>Model — Source: Misc.; produced by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts, 29 October 2026 (a variant of Cian Dorr's coalesced-pinned-substitutions-root with one chosen component); recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 29 October 2026.</p>

## Package

- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **□Atoms are strong atoms.** Necessarily, at each relational type, every atom is a strong atom: it necessarily entails every entity of the type or its negation.
- **¬ Self-atoms are atoms (type t).** Every self-atom is an atom.

## Definition

As in coalesced-pinned-substitutions-root, with a single component in place of a family complete for C($\Sigma$): the one-object action model $V$ with only its identity arrow, one individual, and the full extensional type hierarchy over it, so that $V$ has exactly two propositions. The root $W_0$ has an arrow $\langle V,I\rangle$ for each interpretation $I$ of $\Sigma^+$ at $V$ and an arrow to itself for each type-preserving map of the constants of $\Sigma^+$. Evaluation point: $W_0$, at its identity arrow. Interpretation of Σ as there. The write-up's argument that the root is a model of C uses only that each component is an action model of C.

As for interpretation arrows, and the root has besides an arrow to itself for every type-preserving map of the signature's constants to themselves, acting on the root's individuals and composing with the interpretation arrows by precomposition.

As in coalesced-pinned-substitutions-root, intensions over the arrows out of $W_0$ pinned down by a finite set of constants of $\Sigma^+$; every transport lands, the component's domains being full.

*A member of the group Coalesced sums at a new root, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Atomlessness, □Atoms are strong atoms. Fails Self-atoms are atoms (type t).

Atomlessness holds at $W_0$ by the argument atomlessness of coalesced-pinned-substitutions-root, which needs of the component only that $\top\ne\bot$ there; so $W_0$ has no atom of type $t$, and by existential projection (as in no-actuality-no-self-atoms) no atom of any relational type, and the bridge principles for atoms hold vacuously there. At $V$, which sees only itself, $\Box$ is idle and $\top$ is an atom, so Atomlessness fails there and $\Box$Atomlessness fails at $W_0$; and at $V$ an atom, being non-bottom and below every entity of its type or its negation, is a strong atom and a self-atom, the boxes being idle. So both necessitated bridge principles for atoms hold at every type. Self-atoms are atoms (type t) fails at $W_0$: the proposition $P$ true exactly at the arrows into $V$ is pinned down by $\emptyset$, with transport $\top$ along every $\langle V,I\rangle$, so it lands; it is possible, and wherever it is true it is $\top$ at $V$, an atom, so it is a self-atom, but not an atom at the atomless $W_0$.

*Address: `coalesced-pinned-substitutions-one-world-root#bridges`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; checked by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*


## Notes

Proposed on 29 October 2026 in a trawl for the open questions created by □Atomlessness, to show that Atomlessness with the necessitated bridge principles for atoms does not give □Atomlessness. Checked by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr; it inherits the model-of-C argument of coalesced-pinned-substitutions-root, which has not had a second reader. No Lean verification is claimed.

## Sources

- **Dorr 19 Oct** — Cian Dorr, construction of 19 October 2026 (coalesced-pinned-substitutions-root), with Claude Opus 5.5 (Anthropic); the choice of component here by Claude Opus 5.5 (Anthropic), 29 October 2026.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, pp. 73–74; Appendix E, Definition E.2, pp. 80–83.

<p class='cert'>Record: <code>topics/classicism/models/coalesced-pinned-substitutions-one-world-root.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–74; Appendix E, pp. 80–83
