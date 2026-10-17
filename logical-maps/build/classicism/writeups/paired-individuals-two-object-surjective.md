# Paired-individuals two-object model: surjective block-respecting maps

<p class='cert'>Model — Source: Misc.; produced by Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction; recorded by Claude Fable 5.1 (Anthropic), 14 October 2026.</p>

## Package

- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Two-hat necessity implies ND-necessity.** Whatever is two-hat necessary is ND-necessary: the distinctness-preserving modality agrees with its hat.
- **□Intensional Choice.** Every closed instance of Intensional Choice is necessary. Box the entire object-variable closure; retain the same type range and other schema side conditions.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **□Transversal Choice.** Necessarily, every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ 5-necessity implies two-hat necessity.** Whatever is 5-necessary is two-hat necessary.
- **¬ Truth implies 5-necessity.** Every truth is 5-necessary: necessary under every S5 operator.
- **¬ Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable relative to a type $\sigma$ when it injects into the finite cardinalities of properties of type $\sigma$; one instance for each $\sigma$.
- **¬ Boolean Completeness (type t).** Boolean Completeness (type t) in the displayed closed propositional formulation.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

An ideally full action model in the sense of Classicism, Appendix D, over a category with two objects, each carrying the ideal of finite sets: a model of C by Proposition D.4. The member's construction and evaluation point follow.

A two-object ideally full action model. Fix a fixed-point-free involution $\pi$ on $\mathbb N$ (say $2k\leftrightarrow 2k+1$), which partitions $\mathbb N$ into two-element blocks. The objects are $W_0$, with individuals $\mathbb N$, and $V$, with individuals $\mathbb N\sqcup\{\star\}$ where $\star$ forms a block by itself. The arrows are all surjective block-respecting maps between these sets: $g(\pi c)\in\{g(c),\pi g(c)\}$ for every $c$, so a block maps into a block, either injectively or collapsed to a point, there are surjective arrows $W_0\to V$, obtained by collapsing one block onto $\star$ and mapping the remaining blocks onto all blocks; and the new individual $\star$ can be hit only by collapsing a block onto it. The pinning action is the identity on individuals, the ideal is the finite sets, and the individuals are the type-$e$ domains, so the model is ideally full in the sense of Classicism, Appendix D, and a model of C by its Proposition D.4. The evaluation point is the identity on $W_0$.


Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Finitely pinned action models on two objects, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds □BF.

Every arrow is surjective on individuals, hence on finite sets of individuals, so Proposition D.6 of Classicism gives BF at every type with any object as the evaluation point.

*Address: `paired-individuals-two-object-surjective#necessary-barcan`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Holds Two-hat necessity implies ND-necessity.

Write $\mathrm{fix}^{WW}_N$ for the arrows $W\to W$ agreeing with the identity on the finite set $N$, the least true proposition at $W$ pinned by $N$. For a proposition $q$ at the evaluation object put $C_0(q):=\Diamond q$ and $C_{n+1}(q):=\{u : \text{for every } r \text{ true at } \mathrm{trg}(u) \text{ some } v \text{ has } vu\in q \text{ and } v\in C_n(r)\}$; then $\hat\Diamond q=C_1(q)$, $\hat{\hat\Diamond}q=C_2(q)$, and $\hat{(n+1)}\Box\,s$ holds at the identity iff $C_n(q)\subseteq s$ for some true $q$ (the game form of the hat tower, conversation of 14 October 2026). At $1_{W_0}$ both $C_0(\mathrm{fix}^{00}_N)$ and $C_1(\mathrm{fix}^{00}_N)$ are the arrows out of $W_0$ (to either object) that are injective and block-injective on $N$: such an arrow $u$ is undone on $N$ by a block-respecting $v$ into $W_0$, and $v$ can be chosen to be injective and block-injective on any finite set named at $\mathrm{trg}(u)$, sending $\star$ (if present) to a fresh block, so that a block-respecting $x$ with $xv$ fixing that set exists, collapsing that block onto $\star$ when needed. Hence $\Box_{\ne}$ and $\hat{\hat\Box}$ are coextensive at the evaluation point.

*Address: `paired-individuals-two-object-surjective#root-coextension`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails 5-necessity implies two-hat necessity.

Let $p_0$ be the proposition that the world is $W_0$, the set of arrows $W_0\to W_0$, true and pinned by $\emptyset$. It is not two-hat necessary: every $C_1(\mathrm{fix}^{00}_N)$ contains a surjective arrow $\iota\colon W_0\to V$ injective on $N$, collapsing a block outside $N$ onto $\star$ (given $r$ true at $V$ pinned by $N_1$, let $v\colon V\to W_0$ be the identity on $\mathbb N$ with $\star$ sent to a block $\{e,\pi e\}$ disjoint from $N_1$; then $v\iota=1_{W_0}$, and the map collapsing that block onto $\star$ and fixing everything else brings $v$ back into $\mathrm{fix}^{VV}_{N_1}$). It is 5-necessary: let $Y_k$, for an arrow $k$ out of $W_0$, be the set of propositions at $\mathrm{trg}(k)$ pinned by a finite set of individuals in the range of some arrow from $W_0$ (at $W_0$ all propositions, at $V$ those pinned by old individuals); $Y$ is pinned by $\emptyset$. For $z$ pinned by $S$ put $N_z:=S\cup\pi S$; an arrow injective on $N_z$ cannot collapse a block of $S$ onto $\star$, so $k^tz\in Y_k$ for every $k\in C_1(\mathrm{fix}^{00}_{N_z})$ and $\hat{\hat\Box}(Yz)$ holds for every $z$. Since $\hat{\hat\Box}\le\Box_5$ and $\Box_5$ satisfies BF at type $t$ (Theorem D16 and Corollary D6 of The Bounds of Possibility), $\Box_5\forall z\,Yz$ holds, and $\forall z\,Yz=p_0$ because at $V$ the proposition that $\star$ is fixed is pinned by no set of old individuals (the identity and a surjection sending $\star$ into $\mathbb N$ and collapsing a block away from that set onto $\star$ agree on it).

*Address: `paired-individuals-two-object-surjective#two-hat-not-five`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails Truth implies 5-necessity.

The three-hat operator $\hat{(3)}\Box$ is necessarily B here: at $W_0$, $C_2(\mathrm{fix}^{00}_N)=C_3(\mathrm{fix}^{00}_N)$ is the set of arrows $W_0\to W_0$ injective and block-injective on $N$ (arrows into $V$ drop out at $C_2$ by the argument for $p_0$, and block-bijections, which are surjective, are in every $C_n$), and at $V$ likewise $C_1=C_2$ on $\mathrm{fix}^{VV}_{N}$. So it is an S5 operator, and $\Box_5\le\hat{(3)}\Box$. But $\mathrm{fix}^{00}_N$ is true and not $\hat{(3)}\Box$-necessary, since a block-bijection moving a point of $N$ lies in every $C_2(\mathrm{fix}^{00}_{N^\prime})$. The argument for the non-surjective model carries over, every arrow used in it being surjective or replaceable by a surjective one that agrees with it on the finite set in question.

*Address: `paired-individuals-two-object-surjective#not-all-truths-five-necessary`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails Countable Boolean Completeness, Boolean Completeness (type t).

*Like `paired-individuals-two-object#countable-boolean-completeness-t`: The arrows are the surjective block-respecting maps; every arrow used, the witness to the shrinking included, can be made surjective by mapping the infinitely many blocks after those named onto every block. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-16.*

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: The model is ideally full with the ideal of finite sets and no symmetry group, so every intension pinned down by the empty set, i.e. whose value at an arrow depends only on the codomain, is in the domain at every object (Classicism, Definition D.3). By Claude Fable 5.1 (Anthropic), at Cian Dorr's suggestion, 2026-10-03.*

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

The surjective variant of the paired-individuals model: necessary BF holds at every type by Classicism, Proposition D.6, yet 5-necessity still fails to imply two-hat necessity at the evaluation point and $\Box_{\ne}\ne\hat{\hat\Box}$. Built in the conversation of 14 October 2026. The two operators $\Box_{\ne}$ and $\hat{\hat\Box}$ are coextensive at the evaluation point but differ at $V$: Let $p:=\mathrm{fix}^{VV}_{\{\star\}}$. For any true $q$ at $V$, pinned by $N_q$, let $u\colon V\to W_0$ be the identity on $\mathbb N$ with $\star\mapsto b$ for a block $B\ni b$ disjoint from $N_q$; then $u\in\Diamond q$, since the map fixing $N_q$ and collapsing $B$ onto $\star$ brings it back into $\mathrm{fix}^{VV}_{N_q}$. But $u\notin\hat\Diamond p$: any $v$ with $vu\in p$ sends the whole block $B$ to $\star$, so no arrow after $v$ fixes $B$, i.e. $v\notin\Diamond\,\mathrm{fix}^{00}_B$. So B fails for $\Box_{\ne}$ at $V$, and by Propositions D11 and D22 of The Bounds of Possibility $\hat{\hat\Box}\ne\Box_{\ne}$. These verdicts, with the failure of Actuality and of ND at type $e$ (the block of $0$ collapses onto $\star$), are derived by the engine from the recorded ones.

## Sources

- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74 (ideally full action models).

<p class='cert'>Record: <code>topics/classicism/models/paired-individuals-two-object-surjective.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–74
- **Background: The Bounds of Possibility.** Dorr, Cian, John Hawthorne, and Juhani Yli-Vakkuri (2021). The Bounds of Possibility. Oxford University Press. Appendix D, Narrower Modalities in Higher-Order S4, pp. 400–409; locators follow the OUP corrected proof dated 9 May 2024. Its background logic HS4 (a primitive S4 operator over higher-order logic) is read into C by interpreting the primitive box as $\lambda p\, .\,p=\top$, under which every theorem of HS4 is a theorem of C. — Appendix D
