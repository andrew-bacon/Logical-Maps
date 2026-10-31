# Coalesced sum: substitution arrows over an atomless component with nonstandard arithmetic

<p class='cert'>Model — Source: Misc.; produced by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts, 29 October 2026 (a variant of Cian Dorr's coalesced-pinned-substitutions-root with one chosen component); recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 29 October 2026.</p>

## Package

- **□Atomlessness.** Necessarily, every possible proposition has a possible proposition strictly below it.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Two-hat necessities are ND-necessary.** Whatever is two-hat necessary is ND-necessary: the distinctness-preserving modality agrees with its hat.
- **5-necessities are two-hat necessary.** Whatever is 5-necessary is two-hat necessary.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ Necessity of Arithmetic.** Every arithmetical sentence is either necessarily true or necessarily false, given that possibly zero is not a successor and successor is injective on numbers, where the numbers are the finite cardinalities of properties of a type $\sigma$. One sentence for each type $\sigma$ and each arithmetical sentence at $\sigma$.
- **¬ Necessity of Analysis.** Every first-order analytical sentence is either true in every real number structure in every possible world or false in every real number structure in every possible world. One sentence for each type $\sigma$ and each first-order analytical sentence.
- **¬ Arithmetic Necessitism.** Given that necessarily zero is not a successor and successor is injective on numbers, the numbers at $\sigma$ form a rigid property with necessarily distinct instances. One sentence for each type $\sigma$.
- **¬ □BF (type t).** Necessarily, if every proposition necessarily has a property, then necessarily every proposition has it.
- **¬ Vicinity.** There is a true proposition that entails the possibility of each true proposition.
- **¬ Weakly Inextensible Comprehension.** Every relation, including a proposition, is coextensive with a weakly inextensible one.
- **¬ Boolean Completeness (type t).** Every property of propositions has a greatest lower bound.
- **¬ Truths are 5-necessary.** Every truth is 5-necessary: necessary under every S5 operator.

## Definition

Let $T$ be C together with $\Box$Atomlessness, $\Box I^*_e$ and the negation of BF at type $t$, a recursively axiomatized theory. $T$ holds in finite-support-monotone-maps, which is atomless, fails BF at type $t$, and has infinitely many individuals and the standard numerals as its numbers at $e$ (the property of being a numeral is pinned down by $\emptyset$); it has one object, so its boxes are idle. So $T$ is consistent, by soundness. $T$ proves $I^*_e$, and so the Peano axioms for its numbers at $e$, so by Gödel's second incompleteness theorem $T+\neg\operatorname{Con}(T)$ is consistent, and by the completeness of action models for C (Classicism, Theorem 3.23: every formula consistent with C holds at some world of some action model) it holds at an object $V_2$ of some action model. The single component is that model cut down to the objects reachable from $V_2$, so that every closed sentence keeps its truth value at each object. The root $W_0$ is built over it exactly as in coalesced-pinned-substitutions-root: an arrow $\langle V,I\rangle$ into each object $V$ of the component for each interpretation $I$ of $\Sigma^+$ there, and an arrow from $W_0$ to itself for each type-preserving map of the constants of $\Sigma^+$. Evaluation point: $W_0$, at its identity arrow. Interpretation of Σ as there. The write-up's argument that the root is a model of C does not use the completeness of the family of components, only that each is an action model of C.

As for interpretation arrows, and the root has besides an arrow to itself for every type-preserving map of the signature's constants to themselves, acting on the root's individuals and composing with the interpretation arrows by precomposition.

As in coalesced-pinned-substitutions-root, intensions over the arrows out of $W_0$ pinned down by a finite set of constants of $\Sigma^+$, whose transports along the arrows into the component land in its domains.

*A member of the group Coalesced sums at a new root, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds □Atomlessness, BF.

The arrows out of $W_0$ end at $W_0$ (the maps of the constants) or at objects of the component, and a closed sentence holds at an arrow iff it holds at the identity of its target. At every object of the component Atomlessness holds, by $\Box$Atomlessness at $V_2$, the component being generated from $V_2$. At $W_0$ it holds by the argument atomlessness of coalesced-pinned-substitutions-root, which uses of the components only that $\top\ne\bot$ at each of their objects: a possible $p$ pinned down by $S$ that contains a map is split by a fresh individual constant, and one that contains only arrows into the component by a fresh propositional constant sent to $\top$ or to $\bot$. So $\Box$Atomlessness holds. BF holds at every type by the argument barcan of that model, which uses only fresh constants.

*Address: `coalesced-pinned-substitutions-nonstandard-root#atomlessness`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; audited by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*

### Holds Axiom of Infinity (type e). Fails Necessity of Arithmetic, Necessity of Analysis, Arithmetic Necessitism.

At type $e$. $W_0$ is extensionally full at its identity: any set of tuples there is the extension of the entity with that value at every map of the constants and $\bot$ at every arrow into the component, pinned down by $\emptyset$ and landing. So the property with the numerals as its extension is an inductive property at $W_0$, the numbers there are the standard numerals, and Sum and Prod are standard on them (a relation refuting a false instance is in the domain). The individuals at $W_0$ are the infinitely many individual constants, so distinct numerals are distinct there and $I^*_e$ holds at $W_0$, and it holds throughout the component by $\Box I^*_e$ at $V_2$; so $\Box I^*_e$ holds at $W_0$. With $A:=\operatorname{Con}(T)$, an arithmetical sentence, $A$ holds at $W_0$, whose arithmetic is standard, and fails at $V_2$; so neither $\Box(I\to A)$ nor $\Box(I\to\neg A)$ holds at $W_0$, and the Necessity of Arithmetic fails. The Necessity of Analysis fails as in coalesced-two-extensional-arithmetics-root, with $W_0$ and $V_2$ for the two components: the Dedekind cuts over the numbers form a real number structure at each, every real number structure at a world is isomorphic to it, and $\exists n\in N\,.\,\operatorname{Proof}_T(n,\bot)$ is false in those at $W_0$ and true in those at $V_2$. Arithmetic Necessitism fails by the inextensibility of $\mathbb N_e$: let $X:=\lambda x\, .\,\mathbb N x\land\neg\exists m\in\mathbb N\, .\,m<x\land \operatorname{Proof}_T(m,\bot)$, a closed pure term. Each number at $W_0$ is a numeral $\mathbf n$, and at every world $X\mathbf n$ holds, since under $I^*_e$ the numbers below $\mathbf n$ are the numerals below it and each $\neg\operatorname{Proof}_T(\mathbf m,\bot)$ is a true bounded sentence, $T$ being consistent. But at $V_2$ some number $m$ codes a proof of $\bot$ from $T$, and $\operatorname{Suc}m$ is a number lacking $X$; so $\mathbb N_e\le X$ fails. The Axiom of Infinity (type e) holds at $W_0$: its finite cardinalities are the numerals, and none holds of the universal property, which has infinitely many instances there.

*Address: `coalesced-pinned-substitutions-nonstandard-root#arithmetic`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; audited by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*

### Fails □BF (type t).

BF at type $t$ is a closed pure sentence false at $V_2$, an object reachable from $W_0$. With BF at $W_0$, the recorded result that Tame Rigidity and BF (type t) give $\Box$BF (type t) makes Tame Rigidity fail at the root.

*Address: `coalesced-pinned-substitutions-nonstandard-root#bf-component`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; audited by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*

### Holds Two-hat necessities are ND-necessary, 5-necessities are two-hat necessary. Fails Vicinity, Weakly Inextensible Comprehension, Boolean Completeness (type t), Truths are 5-necessary.

The arguments as-in-all-maps and collapse-at-root of coalesced-pinned-substitutions-root apply unchanged. They use the maps of the constants and propositions and properties containing no arrow into a component, whose transports there are $\bot$ and land, together with the fact that no composite of an arrow into a component with anything is a map; none of this depends on which action models the components are. For Vicinity, the worlds seen from a map $f$ collapsing two individual constants $c,d$ are the maps $g\circ f$ and the arrows $\langle V,I\circ f\rangle$, all of which identify them.

*Address: `coalesced-pinned-substitutions-nonstandard-root#as-in-pinned-substitutions`. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; audited by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*

### Holds Transversal Choice.

As in coalesced-pinned-substitutions-root, by the general argument transversal-choice-extensionally-full applied at the root alone: any set of tuples at the identity is the extension there of the entity with that value at every map of the constants and empty at every arrow into the component, pinned down by $\emptyset$ and landing.

*By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in a trawl for cheaply settled verdicts; audited by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-29.*


## Notes

A variant of coalesced-pinned-substitutions-root proposed on 29 October 2026 in a trawl for the open questions created by □Atomlessness: the substitution arrows keep the root atomless, and the one component is atomless at every object but disagrees with the root about arithmetic and about BF. Audited by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 29 October 2026; it inherits the model-of-C argument of coalesced-pinned-substitutions-root, which has not had a second reader. No Lean verification is claimed.

## Sources

- **Dorr 19 Oct** — Cian Dorr, construction of 19 October 2026 (coalesced-pinned-substitutions-root), with Claude Opus 5.5 (Anthropic); the choice of component here by Claude Opus 5.5 (Anthropic), 29 October 2026.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Theorem 3.23, §3.4, p. 57; Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74; Appendix E, Definition E.2, pp. 80–83.

<p class='cert'>Record: <code>topics/classicism/models/coalesced-pinned-substitutions-nonstandard-root.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Theorem 3.23, §3.4, p. 57; Appendix D, pp. 73–74; Appendix E, pp. 80–83. Soundness and completeness of action models for C (Theorem 3.23) supply the consistency of T and the component; the root is pinned down by finite sets of constants as in coalesced-pinned-substitutions-root.
