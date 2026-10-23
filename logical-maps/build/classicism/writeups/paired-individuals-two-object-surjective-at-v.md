# Paired-individuals two-object model: surjective block-respecting maps, evaluated at the second object

<p class='cert'>Model — Source: Misc.; produced by Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 14 October 2026; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026.</p>

## Package

- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **□Intensional Choice.** Necessarily, if a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **□Transversal Choice.** Necessarily, every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ Two-hat necessity implies ND-necessity.** Whatever is two-hat necessary is ND-necessary: the distinctness-preserving modality agrees with its hat.
- **¬ Truth implies 5-necessity.** Every truth is 5-necessary: necessary under every S5 operator.
- **¬ Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable relative to a type $\sigma$ when it injects into the finite cardinalities of properties of type $\sigma$; one instance for each $\sigma$.
- **¬ Boolean Completeness (type t).** Every property of propositions has a greatest lower bound.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

An ideally full action model in the sense of Classicism, Appendix D, over a category with two objects, each carrying the ideal of finite sets: a model of C by Proposition D.4. The member's construction and evaluation point follow.

A two-object ideally full action model. Fix a fixed-point-free involution $\pi$ on $\mathbb N$ (say $2k\leftrightarrow 2k+1$), which partitions $\mathbb N$ into two-element blocks. The objects are $W_0$, with individuals $\mathbb N$, and $V$, with individuals $\mathbb N\sqcup\{\star\}$ where $\star$ forms a block by itself. The arrows are all surjective block-respecting maps between these sets: $g(\pi c)\in\{g(c),\pi g(c)\}$ for every $c$, so a block maps into a block, either injectively or collapsed to a point, there are surjective arrows $W_0\to V$, obtained by collapsing one block onto $\star$ and mapping the remaining blocks onto all blocks; and the new individual $\star$ can be hit only by collapsing a block onto it. The pinning action is the identity on individuals, the ideal is the finite sets, and the individuals are the type-$e$ domains, so the model is ideally full in the sense of Classicism, Appendix D, and a model of C by its Proposition D.4. The evaluation point is the identity on $V$, the object with the new individual $\star$; every object is reachable from it, since there are surjective arrows $V\to W_0$ (send $\star$ anywhere).


Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Finitely pinned action models on two objects, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds □BF.

Every arrow is surjective on individuals, hence on finite sets of individuals, so Proposition D.6 of Classicism gives BF at every type with any object as the evaluation point.

*Address: `paired-individuals-two-object-surjective-at-v#necessary-barcan`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-10-14.*

### Fails Two-hat necessity implies ND-necessity.

At $V$ let $p:=\mathrm{fix}^{VV}_{\{\star\}}$, the true proposition that $\star$ is fixed. For any true $q$ at $V$, pinned by $N_q$, the surjection $u\colon V\to W_0$ that is the identity on $\mathbb N$ and sends $\star$ into a block $B$ disjoint from $N_q$ lies in $\Diamond q$ (a surjection fixing $N_q$ and collapsing $B$ onto $\star$ brings it back into $\mathrm{fix}^{VV}_{N_q}$) but not in $\hat\Diamond p$, since every $v$ with $vu\in p$ collapses $B$ onto $\star$ and so cannot return to $\mathrm{fix}^{00}_B$. So B fails for $\Box_{\ne}$ at $p$. By Proposition D11 of The Bounds of Possibility, $p\to\hat{\hat\Box}\hat\Diamond p$, so $\hat\Diamond p$ is two-hat necessary; it is not ND-necessary, which is what the failure of B says. Actuality fails: the true propositions $\mathrm{fix}^{VV}_N$ descend strictly.

*Address: `paired-individuals-two-object-surjective-at-v#nd-necessity-not-b`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-10-14.*

### Fails Truth implies 5-necessity.

As in the record evaluated at $W_0$, the three-hat operator $\hat{(3)}\Box$ is necessarily B in this model, so it is an S5 operator and $\Box_5\le\hat{(3)}\Box$; at $V$ its cluster on $\mathrm{fix}^{VV}_N$ is the set of surjective block-bijections of $V$ fixing $\star$ and block-injective on $N$, which contains arrows moving any given point of $\mathbb N$, so the truth $\mathrm{fix}^{VV}_N$ is not 5-necessary.

*Address: `paired-individuals-two-object-surjective-at-v#not-all-truths-five-necessary`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-10-14.*

### Fails Countable Boolean Completeness, Boolean Completeness (type t).

*Like `paired-individuals-two-object#countable-boolean-completeness-t`: The arrows are the surjective block-respecting maps, and the evaluation object is $V$; the family consists of arrows $V\to V$, the block $\{\star\}$ is sent to $\star$ in the witnesses, and every arrow used can be made surjective by mapping the infinitely many blocks after those named onto every block. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-16.*

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: The model is ideally full with the ideal of finite sets and no symmetry group, so every intension pinned down by the empty set, i.e. whose value at an arrow depends only on the codomain, is in the domain at every object (Classicism, Definition D.3). By Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, at Cian Dorr's suggestion, 2026-10-03.*

### Holds □Relational Choice, □Transversal Choice.

At any reachable object $W$, let $U$ be a serial relation in the domain there. Using the axiom of choice, pick for each $x$ a $y$ with $(x,y)$ in the extension of $U$ at the identity, and let $S$ be the intension whose value at every arrow $W\to W$ is the graph of this choice and whose value at arrows with any other codomain is empty; it depends only on the codomain, so the condition puts it in the domain, and at the identity it is a functional subrelation of $U$. Likewise a set of representatives of an equivalence relation at $W$, made into such an intension, is a transversal. Since $W$ was any reachable object, both principles hold at every world.

*General argument `arguments/necessary-relational-choice-codomain-intensions`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: The model is ideally full with the ideal of finite sets and no symmetry group, so every intension pinned down by the empty set, i.e. whose value at an arrow depends only on the codomain, is in the domain at every object (Classicism, Definition D.3). By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-10-14.*

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation the definition fixes. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds Transversal Choice.

For an equivalence relation at the evaluation point, a transversal of its extension there, chosen in the metatheory, is by extensional fullness the extension of an element of the domain; the equivalence and transversal conditions are unboxed.

*General argument `arguments/transversal-choice-extensionally-full`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: Ideally full action models are extensionally full (Classicism, p. 74). By Cian Dorr (observation); recorded by Claude Fable 5.1 (Anthropic), on a question of Zachary Goodsell, after an observation of Christopher Sun, 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The Relational Choice and Transversal Choice arguments merged into one, stated for every extensionally full model.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic. Its first sentence, deriving extensional fullness from ideal fullness, is now the group's reason for meeting extensionally-full.


## Notes

The surjective paired-individuals model with its other object as the evaluation point. Necessary BF holds at every type, yet Two-hat necessity implies ND-necessity fails here, so BF at no type, boxed or not, yields that collapse. Built in the conversation of 14 October 2026.

## Sources

- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74 (ideally full action models).

<p class='cert'>Record: <code>topics/classicism/models/paired-individuals-two-object-surjective-at-v.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–74
- **Background: The Bounds of Possibility.** Dorr, Cian, John Hawthorne, and Juhani Yli-Vakkuri (2021). The Bounds of Possibility. Oxford University Press. Appendix D, Narrower Modalities in Higher-Order S4, pp. 400–409; locators follow the OUP corrected proof dated 9 May 2024. Its background logic HS4 (a primitive S4 operator over higher-order logic) is read into C by interpreting the primitive box as $\lambda p\, .\,p=\top$, under which every theorem of HS4 is a theorem of C. — Appendix D
