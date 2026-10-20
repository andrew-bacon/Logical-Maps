# Coalesced sum of two extensional models disagreeing about arithmetic

<p class='cert'>Model — Source: Misc.; produced by Cian Dorr, 19 October 2026 (the construction), with Claude Opus 5.5 (Anthropic), who wrote the verification; recorded by Claude Opus 5.5 (Anthropic), 19 October 2026.</p>

## Package

- **□Strong Leibniz Biconditionals.** Necessarily, at each relational type, every possible entity (one distinct from bottom) is entailed by a strong world: a possible entity that necessarily entails every entity of the type or its negation.
- **□Strong Leibniz Biconditionals (type t).** Necessarily, every possible proposition is entailed by a strong world proposition, one that is possible and necessarily entails every proposition or its negation.
- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **Possible Infinity (type e).** Possibly there are not finitely many individuals: the Axiom of Infinity at this type, under a diamond.
- **Boolean Completeness (type t).** Every property of propositions has a greatest lower bound.
- **□Boolean Completeness (type t).** Necessarily, every property of propositions has a greatest lower bound.
- **□Truth implies ND-necessity.** Necessarily, every truth is ND-necessary. In C this is the identity $\Box_{\ne}=\lambda p\, .\,p$.
- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.
- **□Tame Rigidity.** Necessarily, every weakly rigid relation, including a proposition, is rigid.
- **□Intensional Choice.** Necessarily, if a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.
- **Modal Well-Ordering.** Every type, including e, has a relation that is necessarily a well-order of it.
- **□Well-Ordering.** Necessarily, every type, including e, is well-ordered by some relation.
- **Relational Choice.** Every serial binary relation has a functional subrelation.
- **Actuality.** There is a true proposition that entails every true proposition.
- **Truth implies ND-necessity.** Every truth is ND-necessary, that is, necessary under the distinctness-preserving modality.
- **¬ Necessity of Arithmetic.** Every arithmetical sentence is either necessarily true or necessarily false, given that possibly zero is not a successor and successor is injective on numbers, where the numbers are the finite cardinalities of properties of a type $\sigma$. One sentence for each type $\sigma$ and each arithmetical sentence at $\sigma$.
- **¬ B for pure sentences.** The B instance for every closed sentence in the pure language.
- **¬ Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Possible Infinity (type t).** Possibly there are not finitely many propositions: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

Let $T$ be C with Extensionality, Well-Ordering at every type and $I^*$ (zero is not a successor and successor is injective on the finite cardinalities of individuals). $T$ holds in the full standard model on $\mathbb N$, by choice in the metatheory, so $T+\operatorname{Con}(T)$ is consistent, and by Gödel's second incompleteness theorem so is $T+\neg\operatorname{Con}(T)$. Take one-world Henkin models $M_1$ of $T+\operatorname{Con}(T)$ and $M_2$ of $T+\neg\operatorname{Con}(T)$, as action models with one object and only its identity arrow, and coalesce them at a new root as in Definition E.2. The root's individuals are the pairs of an individual of $M_1$ and one of $M_2$. Evaluation point: the root. Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

The root has one distinguished arrow to the root of each component, and every arrow from the root into a component factors through it.

Root domains are as full as compatibility allows: a root proposition is a choice, for each component, of a proposition of that component’s root domain, together with a truth value at the root’s identity arrow, and a root entity of a relational type is likewise a family of component entities with a root component that is an arbitrary function of the root arguments.

*A member of the group Coalesced sums at a new root, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Fails Necessity of Arithmetic.

At type $e$. The root sees three worlds: itself and the two component worlds, each of which sees only itself. $I^*$ holds in both components, so $I$ holds at both component worlds and at the root. The arithmetical sentence $A:=\operatorname{Con}(T)$ holds at the world of $M_1$ and fails at that of $M_2$, so neither $\Box(I\to A)$ nor $\Box(I\to\neg A)$ holds at the root.

*Address: `coalesced-two-extensional-arithmetics-root#arithmetic`. By Cian Dorr, recorded by Claude Opus 5.5 (Anthropic), 2026-10-19.*

### Holds □Strong Leibniz Biconditionals, □Strong Leibniz Biconditionals (type t), □BF.

At every relational type the root domain contains, for each world and each tuple there, the entity true of that tuple at that world and of nothing else: the root component is free, and each component contains the singleton of each of its tuples, definable from them. Such an entity lies below every entity or below its negation, and necessarily so, since its transport to a component world is that singleton or $\bot$; so it is a strong world, and every nonzero entity has one below it. In the one-world components the same holds trivially. For BF, the root individuals are pairs, so each component individual is the image of a root individual, and likewise at every type, root entities being families of component entities; the components, with one world each, satisfy BF.

*Address: `coalesced-two-extensional-arithmetics-root#strong-leibniz`. By Cian Dorr, recorded by Claude Opus 5.5 (Anthropic), 2026-10-19.*

### Fails B for pure sentences.

The closed pure sentence $\exists p\, .\,p\land\Diamond\neg p$ is true at the root, where the proposition true only at the root is contingent, and false at each component world, which sees only itself; so it is not possible there, and B for it fails at the root.

*Address: `coalesced-two-extensional-arithmetics-root#pure-b`. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-19.*

### Holds Infinity Schema (type e), Possible Infinity (type e). Fails Axiom of Infinity (type t), Infinity Schema (type t), Possible Infinity (type t).

Each component is one-world and extensional, so it has exactly two propositions, and the root, whose propositions are a truth value at the root with one of each component's, has eight; so there are finitely many propositions at every world. The root individuals are the pairs from two infinite domains, with literal identity, so any number of them are distinct. $T$ proves the Axiom of Infinity at type $e$: if a finite cardinality $n$ held of the universal property, $\operatorname{Suc}n$ and $\operatorname{Suc}\operatorname{Suc}n$ would both be the empty cardinality, by Extensionality, while $n\ne\operatorname{Suc}n$, against $I^*$; so it holds at the component worlds and is possible at the root.

*Address: `coalesced-two-extensional-arithmetics-root#infinity`. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-19.*

### Holds Boolean Completeness (type t), □Boolean Completeness (type t).

The propositions form a finite Boolean algebra at every world, so every family has a greatest lower bound.

*Address: `coalesced-two-extensional-arithmetics-root#boolean-completeness-t`. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-19.*

### Holds □Truth implies ND-necessity, Tame Rigidity, □Tame Rigidity, □Intensional Choice.

At a one-world component $\Box$ is idle. Every truth is ND-necessary there, with $\top$ as witness; every relation is weakly persistent and weakly inextensible, so Tame Rigidity holds there trivially; and Intensional Choice holds, the singleton of a chosen instance being definable. At the root, a weakly rigid relation is rigid, since Rigid is weak rigidity at every world and the other worlds are the components; and Truth implies ND-necessity holds there already.

*Address: `coalesced-two-extensional-arithmetics-root#one-world-components`. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-19.*

### Holds Modal Well-Ordering, □Well-Ordering.

Each component satisfies Well-Ordering, being a model of $T$. For a type $\sigma$, let $R$ have as root part a well-ordering of the root's entities of type $\sigma$, chosen in the metatheory, and as component parts well-orderings in the components; the root domains being fullest, $R$ is in the domain, and it well-orders the type at every world, every root property of type $\sigma t$ having a root part that is a subset of the root's entities.

*Address: `coalesced-two-extensional-arithmetics-root#well-ordering`. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-19.*

### Holds Relational Choice.

The functionality of a subrelation is evaluated at the root’s identity arrow only, while the subrelation condition is boxed; so for a serial root relation take the subrelation whose root component is a functional choice from the root component, by choice in the metatheory, and whose component parts are empty. Where some component refutes Relational Choice at its root, as when the components are complete for C, its necessitation fails.

*From the group *Coalesced sums at a new root*, shared argument `coalesced-sums#relational-choice-free-root`. It requires that A root entity of a relational type has a root component that is an arbitrary function of the root arguments. Here: The root domains are as full as compatibility allows. By Cian Dorr, recorded by Claude Fable 5.1 (Anthropic), 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The three complete members' copies stated once; "Its necessitation fails, since some component refutes Relational Choice at its root" became conditional on that, since in the all-finite-domains member every component satisfies Relational Choice.

### Holds Actuality.

The singleton root proposition witnesses Actuality.

*Source: Classicism, Appendix E, p. 83. From the group *Coalesced sums at a new root*, shared argument `coalesced-sums#actuality-singleton-root`. It requires that The actual-world proposition $a$ is in the domain and entails every truth, and no world outside $a$ sees a world in $a$. Here: The singleton root proposition, true at the root's identity arrow and nowhere in a component, is in the domain and entails every truth; the components have no arrows back to the root (Classicism, Appendix E, p. 83, on the distinctness-preserving collapse). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The three members' versions stated once.

### Holds Truth implies ND-necessity.

For a true $p$, $a\le p$, since $a$ entails every truth. Take $q:=a$ in the definition of $\Box_{\ne}p$: at a world in $a$, $p$ holds; at a world outside $a$, $\Diamond a$ fails. So every truth is $\Box_{\ne}$-necessary.

*General argument `arguments/dpc-isolated-actual-world`. It requires that The actual-world proposition $a$ is in the domain and entails every truth, and no world outside $a$ sees a world in $a$. Here: The singleton root proposition, true at the root's identity arrow and nowhere in a component, is in the domain and entails every truth; the components have no arrows back to the root (Classicism, Appendix E, p. 83, on the distinctness-preserving collapse). By Claude Fable 5.1 (Anthropic), 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support, symmetric and full action models' copies (eight records) stated once for the topic; what varied, why no world outside the actual world sees back into it, is each record's reason for meeting actual-world-isolated.

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation the construction fixes. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.


## Notes

Suggested by Cian Dorr on 19 October 2026 as a small model of the boxed Strong Leibniz Biconditionals and □BF without the Necessity of Arithmetic. The root has three atoms, the singletons of its three worlds, all strong worlds. The components are one-world extensional Henkin models, and they satisfy Well-Ordering at every type, so that the choice principles hold at every world. No Lean verification is claimed.

## Sources

- **Dorr 19 Oct** — Cian Dorr, construction of 19 October 2026, with Claude Opus 5.5 (Anthropic).
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix E, Definition E.2, pp. 80–83.

<p class='cert'>Record: <code>topics/classicism/models/coalesced-two-extensional-arithmetics-root.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix E, Definition E.2, pp. 80–83. The coalesced sum, here of two components.
