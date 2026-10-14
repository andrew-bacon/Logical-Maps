# Paired-individuals two-object model: block-respecting maps

<p class='cert'>Model — Source: Misc.; produced by Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction; recorded by Claude Fable 5.1 (Anthropic), 14 October 2026.</p>

## Package

- **Two-hat necessity implies ND-necessity.** Whatever is two-hat necessary is ND-necessary: the distinctness-preserving modality agrees with its hat.
- **¬ 5-necessity implies two-hat necessity.** Whatever is 5-necessary is two-hat necessary.
- **¬ Truth implies 5-necessity.** Every truth is 5-necessary: necessary under every S5 operator.
- **¬ BF (type t).** BF (type t) in the displayed closed propositional formulation.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

A two-object ideally full action model. Fix a fixed-point-free involution $\pi$ on $\mathbb N$ (say $2k\leftrightarrow 2k+1$), which partitions $\mathbb N$ into two-element blocks. The objects are $W_0$, with individuals $\mathbb N$, and $V$, with individuals $\mathbb N\sqcup\{\star\}$ where $\star$ forms a block by itself. The arrows are all block-respecting maps between these sets: $g(\pi c)\in\{g(c),\pi g(c)\}$ for every $c$, so a block maps into a block, either injectively or collapsed to a point, and the new individual $\star$ can be hit only by collapsing a block onto it. The pinning action is the identity on individuals, the ideal is the finite sets, and the individuals are the type-$e$ domains, so the model is ideally full in the sense of Classicism, Appendix D, and a model of C by its Proposition D.4. The evaluation point is the identity on $W_0$.


Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

## Arguments

### Holds Two-hat necessity implies ND-necessity.

Write $\mathrm{fix}^{WW}_N$ for the arrows $W\to W$ agreeing with the identity on the finite set $N$, the least true proposition at $W$ pinned by $N$. For a proposition $q$ at the evaluation object put $C_0(q):=\Diamond q$ and $C_{n+1}(q):=\{u : \text{for every } r \text{ true at } \mathrm{trg}(u) \text{ some } v \text{ has } vu\in q \text{ and } v\in C_n(r)\}$; then $\hat\Diamond q=C_1(q)$, $\hat{\hat\Diamond}q=C_2(q)$, and $\hat{(n+1)}\Box\,s$ holds at the identity iff $C_n(q)\subseteq s$ for some true $q$ (the game form of the hat tower, conversation of 14 October 2026). At $1_{W_0}$ both $C_0(\mathrm{fix}^{00}_N)$ and $C_1(\mathrm{fix}^{00}_N)$ are the arrows out of $W_0$ (to either object) that are injective and block-injective on $N$: such an arrow $u$ is undone on $N$ by a block-respecting $v$ into $W_0$, and $v$ can be chosen to be injective and block-injective on any finite set named at $\mathrm{trg}(u)$, sending $\star$ (if present) to a fresh block, so that a block-respecting $x$ with $xv$ fixing that set exists, collapsing that block onto $\star$ when needed. Hence $\Box_{\ne}$ and $\hat{\hat\Box}$ are coextensive at the evaluation point.

*Address: `paired-individuals-two-object#root-coextension`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails 5-necessity implies two-hat necessity.

Let $p_0$ be the proposition that the world is $W_0$, the set of arrows $W_0\to W_0$, true and pinned by $\emptyset$. It is not two-hat necessary: every $C_1(\mathrm{fix}^{00}_N)$ contains the inclusion $\iota\colon W_0\to V$ (given $r$ true at $V$ pinned by $N_1$, let $v\colon V\to W_0$ be the identity on $\mathbb N$ with $\star$ sent to a block $\{e,\pi e\}$ disjoint from $N_1$; then $v\iota=1_{W_0}$, and the map collapsing that block onto $\star$ and fixing everything else brings $v$ back into $\mathrm{fix}^{VV}_{N_1}$). It is 5-necessary: let $Y_k$, for an arrow $k$ out of $W_0$, be the set of propositions at $\mathrm{trg}(k)$ pinned by a finite set of individuals in the range of some arrow from $W_0$ (at $W_0$ all propositions, at $V$ those pinned by old individuals); $Y$ is pinned by $\emptyset$. For $z$ pinned by $S$ put $N_z:=S\cup\pi S$; an arrow injective on $N_z$ cannot collapse a block of $S$ onto $\star$, so $k^tz\in Y_k$ for every $k\in C_1(\mathrm{fix}^{00}_{N_z})$ and $\hat{\hat\Box}(Yz)$ holds for every $z$. Since $\hat{\hat\Box}\le\Box_5$ and $\Box_5$ satisfies BF at type $t$ (Theorem D16 and Corollary D6 of The Bounds of Possibility), $\Box_5\forall z\,Yz$ holds, and $\forall z\,Yz=p_0$ because at $V$ the proposition that $\star$ is fixed is pinned by no set of old individuals (the identity and the map sending $\star$ to $0$ agree on every such set).

*Address: `paired-individuals-two-object#two-hat-not-five`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails Truth implies 5-necessity.

The three-hat operator $\hat{(3)}\Box$ is necessarily B here: at $W_0$, $C_2(\mathrm{fix}^{00}_N)=C_3(\mathrm{fix}^{00}_N)$ is the set of arrows $W_0\to W_0$ injective and block-injective on $N$ (arrows into $V$ drop out at $C_2$ by the argument for $p_0$, and block-bijections are in every $C_n$), and at $V$ likewise $C_1=C_2$ on $\mathrm{fix}^{VV}_{N}$. So it is an S5 operator, and $\Box_5\le\hat{(3)}\Box$. But $\mathrm{fix}^{00}_N$ is true and not $\hat{(3)}\Box$-necessary, since a block-bijection moving a point of $N$ lies in every $C_2(\mathrm{fix}^{00}_{N^\prime})$.

*Address: `paired-individuals-two-object#not-all-truths-five-necessary`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails BF (type t).

With $Y$ as in the argument for 5-necessity, $k^tz$ is pinned by $k(S)$, a set of individuals in the range of $k$, so $\Box(Yz)$ holds for every $z$, while $\Box\forall z\,Yz$ fails at the inclusion $\iota$, whose target has the proposition that $\star$ is fixed.

*Address: `paired-individuals-two-object#barcan-t-fails`. By Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction.*

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation the definition fixes. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.


## Notes

Built in the conversation of 14 October 2026 to settle the question left open on p. 407 of The Bounds of Possibility, Appendix D: whether $\Box_5$ is equivalent to $\hat{\hat\Box}$ without the rigidity axioms. Actuality fails here, and so do the collapse principles from 5-necessity down; the surjective variant adds necessary BF at every type and shows that BF does not help. The two operators $\Box_{\ne}$ and $\hat{\hat\Box}$ are coextensive at the evaluation point but differ at $V$: Let $p:=\mathrm{fix}^{VV}_{\{\star\}}$. For any true $q$ at $V$, pinned by $N_q$, let $u\colon V\to W_0$ be the identity on $\mathbb N$ with $\star\mapsto b$ for a block $B\ni b$ disjoint from $N_q$; then $u\in\Diamond q$, since the map fixing $N_q$ and collapsing $B$ onto $\star$ brings it back into $\mathrm{fix}^{VV}_{N_q}$. But $u\notin\hat\Diamond p$: any $v$ with $vu\in p$ sends the whole block $B$ to $\star$, so no arrow after $v$ fixes $B$, i.e. $v\notin\Diamond\,\mathrm{fix}^{00}_B$. So B fails for $\Box_{\ne}$ at $V$, and by Propositions D11 and D22 of The Bounds of Possibility $\hat{\hat\Box}\ne\Box_{\ne}$. These verdicts, with the failure of Actuality and of ND at type $e$ (the block of $0$ collapses onto $\star$), are derived by the engine from the recorded ones.

## Sources

- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74 (ideally full action models).

<p class='cert'>Record: <code>topics/classicism/models/paired-individuals-two-object.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–74
- **Background: The Bounds of Possibility.** Dorr, Cian, John Hawthorne, and Juhani Yli-Vakkuri (2021). The Bounds of Possibility. Oxford University Press. Appendix D, Narrower Modalities in Higher-Order S4, pp. 400–409; locators follow the OUP corrected proof dated 9 May 2024. Its background logic HS4 (a primitive S4 operator over higher-order logic) is read into C by interpreting the primitive box as $\lambda p\, .\,p=\top$, under which every theorem of HS4 is a theorem of C. — Appendix D
