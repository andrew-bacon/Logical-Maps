# Coalesced sum: substitution arrows over two atomless components disagreeing about CH

<p class='cert'>Model — Source: Misc.; produced by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts, 29 October 2026 (a variant of Cian Dorr's coalesced-pinned-substitutions-root with chosen components); recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 29 October 2026.</p>

## Package

- **□Atomlessness.** Necessarily, every possible proposition has a possible proposition strictly below it.
- **¬ Non-contingency of the Continuum Hypothesis.** Either necessarily every real number structure satisfies the continuum hypothesis, or necessarily every real number structure falsifies it: that every subproperty of the continuum either injects into the natural numbers or is in bijection with the continuum. One sentence for each type $\sigma$.

## Definition

Assume $\operatorname{Con}(\mathrm{ZFC})$ in the metatheory, as for coalesced-two-extensional-ch-models-root, so that there are models $N_+\models\mathrm{ZFC}+\mathrm{CH}$ and $N_-\models\mathrm{ZFC}+\neg\mathrm{CH}$. In each $N\in\{N_+,N_-\}$, carry out the construction of coalesced-pinned-substitutions-root with a single component, finite-support-monotone-maps as built in $N$, giving an action model $M_N$ with root object $R_N$. Being an action model, and the truth of a formula at a world, are computed by recursion inside $N$, so $M_N$ is an action model of C in the metatheory, with the same truths. The components are $M_{N_+}$ and $M_{N_-}$, and the root $W_0$ is built over them as in coalesced-pinned-substitutions-root. Evaluation point: $W_0$, at its identity arrow. Interpretation of Σ as there.

As for interpretation arrows, and the root has besides an arrow to itself for every type-preserving map of the signature's constants to themselves, acting on the root's individuals and composing with the interpretation arrows by precomposition.

As in coalesced-pinned-substitutions-root, intensions over the arrows out of $W_0$ pinned down by a finite set of constants of $\Sigma^+$, whose transports along the arrows into a component land in its domains.

*A member of the group Coalesced sums at a new root, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds □Atomlessness. Fails Non-contingency of the Continuum Hypothesis.

□Atomlessness: $W_0$ is atomless by the argument atomlessness of coalesced-pinned-substitutions-root, which needs of the components only that $\top\ne\bot$ in them; each $R_N$ is atomless by the same argument, carried out in $N$; and finite-support-monotone-maps is atomless. So Atomlessness holds at every world. CH, at type $et$: at $R_N$ the entity with value $E$ at every map of the constants and empty at the arrows into the component is pinned down by $\varnothing$ and lands, with extension $E$ at the identity, for any set $E$ of tuples in $N$. So quantifiers over relations at $R_N$ range over all such sets, there are continuum many (in $N$) entities of type $et$ there, and the real number structures at $et$ there are $N$'s complete ordered fields on sets of them, CH holding of them iff $N\models\mathrm{CH}$. A closed pure sentence holds at an arrow $\langle R_N,I\rangle$ iff it holds at $R_N$, so at $W_0$ the arrows into $R_{N_-}$ refute $\Box\forall\mathfrak R\,.\,\operatorname{Real}_{et}(\mathfrak R)\to\operatorname{CH}(\mathfrak R)$ and those into $R_{N_+}$ its counterpart with $\neg\operatorname{CH}$.

*Address: `coalesced-pinned-substitutions-ch-root#atomlessness-and-ch`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; checked by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*


## Notes

Proposed on 29 October 2026 in a trawl for the open questions created by □Atomlessness: □Atomlessness does not give Non-contingency of CH. It assumes Con(ZFC) in the metatheory. Checked by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr; it inherits the model-of-C argument of coalesced-pinned-substitutions-root, which has not had a second reader. No Lean verification is claimed.

## Sources

- **Dorr 19 Oct** — Cian Dorr, construction of 19 October 2026 (coalesced-pinned-substitutions-root), with Claude Opus 5.5 (Anthropic); the choice of components here by Claude Opus 5.5 (Anthropic), 29 October 2026, following coalesced-two-extensional-ch-models-root.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, pp. 73–77; Appendix E, Definition E.2, pp. 80–83.

<p class='cert'>Record: <code>topics/classicism/models/coalesced-pinned-substitutions-ch-root.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–77; Appendix E, pp. 80–83
