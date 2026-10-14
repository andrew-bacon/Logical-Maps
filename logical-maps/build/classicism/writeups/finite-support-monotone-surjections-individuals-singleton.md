# Finite-support action model: monotone surjections of N [one individual]

<p class='cert'>Model — Source: Classicism (2024); produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), 17 September 2026.</p>

## Package

- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **Truth implies ND-necessity.** Every truth is ND-necessary, that is, necessary under the distinctness-preserving modality.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **□Intensional Choice.** Every closed instance of Intensional Choice is necessary. Box the entire object-variable closure; retain the same type range and other schema side conditions.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.
- **Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable when it injects into the natural numbers.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Boolean Completeness (type t).** Boolean Completeness (type t) in the displayed closed propositional formulation.
- **¬ Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Possible Infinity (type e).** Possibly there are not finitely many individuals: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

Proposition D.5, part 2 (pp. 76–77): the one-object category whose arrows are the monotone surjections of $\mathbb N$ (the source first considers all surjections, which gives the same package, and restricts to the monotone ones to make the failure of Boolean Completeness easier to exhibit). In every part, $W_0^\ddagger$ is the set of finite subsets of $\mathbb N$ and the model is ideally full: a proposition is a set of arrows whose membership depends only on the arrows’ values on some finite set of numbers (it is pinned down by that set), and an entity of a higher type is an applicative behaviour profile pinned down by a finite set in the same sense. There is a single individual, which every arrow fixes; the arrows still act on $\mathbb N$, which supplies the pinning sets. Propositions and properties are thus about finitely many numbers and indifferent to how the arrows treat the rest. Evaluation point: the sole object, at the identity arrow.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Finite-support action models on one object, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Atomlessness.

As in part 1.

*Source: Classicism, Proposition D.5(2), pp. 76–77. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Holds Truth implies ND-necessity.

For a true proposition $p$ pinned down by a finite set take as the witness $q$ the proposition that the arrow fixes $0,\ldots,N$ for $N$ beyond the pinning set. An arrow fixing $0,\ldots,N$ agrees with the identity on that set and so is in $p$. An arrow $h$ that does not, with least moved point $m\le N$, has $hm<m$ by monotone surjectivity and so collapses $m-1$ and $m$; then no $k\circ h$ can fix both, so $\Diamond q$ fails at $h$. Hence $\Box(\Diamond q\to p)$.

*By Claude Fable 5.1 (Anthropic), 2026-09-23.*

### Holds Axiom of Infinity (type t).

The propositions that a given number is fixed by the arrow, one for each number, are pairwise distinct and each has that number as finite support, so there are infinitely many propositions. The set of numerals at type $t$ is invariant under every arrow, hence has empty support and lies in the domain, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#axiom-of-infinity-t`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$t$ half of the old argument, "individual" becoming "number", so that it covers the one-individual variants.

### Fails Boolean Completeness (type t).

The source (n. 92) conjectures this but does not show it. Any set $F$ of propositions is the extension at the identity of an element of the domain at type $t\to t$, namely the profile $\langle h,p\rangle\mapsto\{i : i\cdot p\in F\}$: it is natural, independent of $h$ and so pinned down by the empty set, and each of its values is pinned down by the pinning set of $p$, since $i\cdot p$ depends only on the values of $i$ there. A least upper bound of $F$ under entailment is a least finitely pinned superset of $\bigcup F$, and it exists only if the least $S$-pinned superset of $\bigcup F$ stops shrinking as the finite set $S$ grows. So the family $F$ of the condition has no least upper bound, and, taking pointwise negations, the family of complements has no greatest lower bound.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#boolean-completeness-t`. It requires that Some family $F$ of propositions has no least finitely pinned superset of its union $\bigcup F$. Here: Let $F$ be the family of propositions $A_m$ ($m\ge1$), each pinned down by $\{2m-1,2m\}$, that the arrow sends $2m-1$ to $0$ and $2m$ to $1$, so that its first step is at the even position $2m$. The least superset of $\bigcup F$ pinned down by $\{0,\ldots,N\}$ consists of the arrows whose first step is at an even position or beyond $N$, and it strictly shrinks as $N$ grows. By Claude Fable 5.1 (Anthropic), 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The seven members' copies stated once, each member's family moved to the condition no-least-pinned-cover; the truncations' separate argument of 23 September, by Claude Fable 5.1 prompted by Cian Dorr, is now its witness, its own proof that the family is in the domain giving way to the profile above. The trawl's second arguments for the same verdict (25 September, DeepSeek, reviewed by OpenAI Codex) were dropped.

### Holds BF.

By Proposition D.6.

*Source: Classicism, Proposition D.6, p. 76. General argument `arguments/barcan-d6`. It requires that The model is an ideally full action model in which every arrow out of the evaluation object acts surjectively both on the individuals and on the pinning sets (Proposition D.6's hypothesis). Here: The arrows are the monotone surjections of $\mathbb N$. So each arrow acts surjectively on the pinning sets, the finite subsets of $\mathbb N$, and on the individuals, whether these are the natural numbers or a single one that every arrow fixes. By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support members' citations of Proposition D.6 stated once, then moved to the topic; each model's reason for meeting D.6's hypothesis is under its `meets`.

### Holds Axiom of Infinity (type t), Infinity Schema (type t).

As for individuals (the argument infinitely-many-individuals), at type $t$: the Infinity schema holds, and by extensional fullness the property of cardinalities that hold only of properties with finite extensions is in the domain, has every finite cardinality, and excludes those holding of the universal property of propositions, whose extension is infinite.

*General argument `arguments/infinitely-many-propositions`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. It requires that There are infinitely many propositions at the evaluation world. Here: The propositions that a given number is fixed by the arrow, one for each number, are pairwise distinct, each pinned down by that number (the shared argument axiom-of-infinity-t). By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-06.*

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: With one object such an intension is constant, so it is pinned down by $\emptyset$, and the domain holds every finitely pinned intension. By Claude Fable 5.1 (Anthropic), at Cian Dorr's suggestion, 2026-10-03.*

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: Each part of Proposition D.5 is a one-object category acting on $\mathbb N$ (Appendix D, Definitions D.1–D.3). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Axiom of Infinity (type e), Infinity Schema (type e), Possible Infinity (type e).

No two individuals are distinct, and the numeral $\operatorname{Suc}_e\mathbf{0}_e$ holds of the universal property at type $e$ at every world.

*General argument `arguments/one-individual`. It requires that There is exactly one individual, at every world. Here: The only individual is fixed by every arrow, at the sole object. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds Tame Rigidity.

Write $B_N(E)$ for the intension $k\mapsto\bigcup\{k^{\prime}\cdot E:k^{\prime}\text{ agrees with }k \text{ on }N\}$; it is pinned down by $N$, and symmetric when the model is, since the symmetry group consists of arrows and $(gk)\cdot E=g\cdot(k\cdot E)$, so it is in the domain. (1) A relation $Y$ pinned down by $S$, with extension $E$ at the identity, is weakly rigid iff $Y=B_S(E)=B_N(E)$ for every finite $N\supseteq S$: weak persistence gives $k\cdot E\subseteq Y_k$, and with pinning $B_S(E)\subseteq Y$; a domain element $X$ with $\Box X$ true of each member of $E$, pinned down by $N$, contains $B_N(E)$, so weak inextensibility says exactly that $Y\subseteq B_N(E)$ for every finite $N$, and $B_N(E)\subseteq B_S(E)$ for $N\supseteq S$. (2) Rigidity is (1) at every world: for each arrow $h$, $h\cdot Y$, with $(h\cdot Y)_k=Y_{kh}$, must satisfy $k\cdot Y_h\subseteq Y_{kh}\subseteq B_N(Y_h)_k$ for all $k$ and finite $N$. (3) Let $Y$ be weakly rigid. Persistence at $h$: $k\cdot Y_h=\bigcup\{(kk^{\prime\prime})\cdot E:k^{\prime\prime}\text{ agrees with }h\text{ on }S\}\subseteq B_S(E)_{kh}=Y_{kh}$. Inextensibility at $h$: given $N$, take $N^{\prime\prime}$ from the condition. By (1), $Y_{kh}=B_{N^{\prime\prime}}(E)_{kh}$, so a member of it is $k^{\prime}\cdot e$ with $e\in E$, pinned down by some finite $M$, and $k^{\prime}$ agreeing with $kh$ on $N^{\prime\prime}$. The condition gives $k^{\prime\prime}$ agreeing with $h$ on $N^{\prime\prime}$ and $j$ agreeing with $k$ on $N$ with $jk^{\prime\prime}$ agreeing with $k^{\prime}$ on $M$, so $k^{\prime}\cdot e=j\cdot(k^{\prime\prime}\cdot e)$, where $k^{\prime\prime}\cdot e\in B_{N^{\prime\prime}}(E)_h=Y_h$; hence $k^{\prime}\cdot e\in B_N(Y_h)_k$. So every weakly rigid relation, at every type, is rigid. With No Pure Contingency, which holds in one-object models, the map's results give $\Box$Tame Rigidity.

*General argument `arguments/tame-rigidity-factorizable`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: Each part of Proposition D.5 is a one-object category acting on $\mathbb N$ (Appendix D, Definitions D.1–D.3). It requires that Write an entity of relational type at the evaluation object as its intension $k\mapsto Y_k$ over the arrows $k$ out of it, so that $Y\bar a$ holds at $k$ iff $k\cdot\bar a\in Y_k$; $Y$ is pinned down by a finite set $N$ of the points the arrows act on when $Y_k=Y_{k^{\prime}}$ for any arrows $k,k^{\prime}$ agreeing on $N$. Every entity in a domain is pinned down by a finite set, in the sense that $k\cdot x=k^{\prime}\cdot x$ for arrows agreeing on it, and the domain of each relational type at the evaluation object holds every intension pinned down by a finite set (in a symmetric model, every symmetric one). Here: The model is ideally full: every entity is pinned down by a finite set of numbers, and every intension pinned down by one is in the domain (Definitions D.1–D.3). It requires that For every arrow $h$ out of the evaluation object and finite sets $N,S$ there is a finite $N^{\prime\prime}\supseteq S$ such that, whenever $k^{\prime}$ agrees with $k\circ h$ on $N^{\prime\prime}$, for every finite $M$ some arrows $k^{\prime\prime}$ agreeing with $h$ on $N^{\prime\prime}$ and $j$ agreeing with $k$ on $N$ have $j\circ k^{\prime\prime}$ agreeing with $k^{\prime}$ on $M$. Here: Given $h$, $N\subseteq[0,n]$ and $S\subseteq[0,s]$, take $N^{\prime\prime}:=[0,n^{\prime\prime}]$ with $n^{\prime\prime}\ge s$ and $h(n^{\prime\prime})\ge n$. For $k^{\prime}$ agreeing with $kh$ there and $M\subseteq[0,m]$, $m\ge n^{\prime\prime}$: let $k^{\prime\prime}$ be $h$ on $[0,n^{\prime\prime}]$ and then rise by one at each step, and let $j$ be $k$ on $[0,h(n^{\prime\prime})]$, send $h(n^{\prime\prime})+i$ to $k^{\prime}(n^{\prime\prime}+i)$ for $0<i\le m-n^{\prime\prime}$, and then rise by one. Both are monotone surjections, since the steps of $k^{\prime}$ are $0$ or $1$; $j$ agrees with $k$ on $N$; and $jk^{\prime\prime}$ agrees with $k^{\prime}$ on $[0,m]$, on $[0,n^{\prime\prime}]$ because $k^{\prime}$ agrees with $kh$ there. By Claude Opus 5.5 (Anthropic), on Cian Dorr's request to settle Tame Rigidity where it was open, 2026-10-09.*

### Holds Countable Boolean Completeness.

The natural numbers are the finite cardinalities at type $e$ (Background, after Goodsell), and with a single individual there are three: $\mathbf{0}_e$, true of the empty property; $\operatorname{Suc}_e\mathbf{0}_e$, true of the universal one; and the empty cardinality, which is $\operatorname{Suc}_e$ of the second and of itself. By extensional fullness the property of being one of these three is in the domain, so it bounds natural numberhood. A countable property therefore has at most three members in its extension, and their join is its least upper bound.

*General argument `arguments/three-numbers`. It requires that There is exactly one individual, at every world. Here: The only individual is fixed by every arrow, at the sole object. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. By Claude Opus 5.5 (Anthropic), on Cian Dorr's question whether the failure of Boolean Completeness at type $t$ refutes its countable form here, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Holds Transversal Choice.

For an equivalence relation at the evaluation point, a transversal of its extension there, chosen in the metatheory, is by extensional fullness the extension of an element of the domain; the equivalence and transversal conditions are unboxed.

*General argument `arguments/transversal-choice-extensionally-full`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. By Cian Dorr (observation); recorded by Claude Fable 5.1 (Anthropic), on a question of Zachary Goodsell, after an observation of Christopher Sun, 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The Relational Choice and Transversal Choice arguments merged into one, stated for every extensionally full model.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic. Its first sentence, deriving extensional fullness from ideal fullness, is now the group's reason for meeting extensionally-full.

### Holds No Contingency (signature Σ), B for sentences of Σ.

Each constant of Σ denotes what the closed pure term $\top_\tau$ of its type denotes, so a closed sentence of the language of Σ denotes what the pure sentence with $\top_\tau$ in place of each constant denotes; if true it is necessary by No Pure Contingency, which holds here. So No Contingency (signature Σ) holds, and B for sentences of Σ with it: a true Σ-sentence is necessary, hence necessarily possible.

*General argument `arguments/sigma-top-npc`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Cian Dorr (observation); recorded by Claude Opus 5.5 (Anthropic), 2026-10-02.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The argument sigma-single-top, for Σ a single constant of type $t$ denoting $\top$, stated for every interpretation of Σ by top elements, now that such interpretations have no individual constants. It replaces that argument and nc-sigma-homogeneous, which reached the same verdicts through an individual constant when the model's automorphisms carry every individual to every other. With an individual constant and no such automorphisms the verdicts were unknown in 19 models, and nowhere did the individual constants settle a verdict differently.


## Notes

The cited construction is a model of the map’s relational-type framework. The description identifies its evaluation point; construction and verification are given at the PDF locations in References. Everything that implies these fails with them.

## History

The record's revision log before it was written as arguments.

- **2026-09-27** (Claude Opus 5.5 (Anthropic), at Cian Dorr's request) — Recorded the failure of Vicinity; argument in the notes. Now violates: Vicinity.
- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added Transversal Choice, by the argument recorded for Relational Choice: the model is extensionally full at every object, so for an equivalence relation at the evaluation point a transversal of its extension there, chosen in the metatheory, is the extension of an element pinned down by the empty set; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun. Now satisfies: Transversal Choice.
- **2026-09-25** (OpenAI Codex (GPT-6)) — Confirmed the trawl's BC-t conclusion with a replacement proof: alternating differences of finite agreement classes have no least upper bound. The original missing-intersection argument is invalid. Used source extensional fullness for domain membership. Now violates: Boolean Completeness (type t).
- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added the failure of Boolean Completeness (type t) and of Inextensible Comprehension, with the arguments in the notes. Now violates: Boolean Completeness (type t), Inextensible Comprehension.
- **2026-09-25** (Claude Opus 5.5 (Anthropic)) — Merged the two sets of arguments recorded on 23 and 25 September into one, keeping the 23 September argument for Inextensible Comprehension, which already refutes the weak form. Now violates: Weakly Inextensible Comprehension.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Expanded the description from Appendix D, naming Proposition D.5 and its part; added the failure of Countable Boolean Completeness at type e→t; settled the Distinctness-preserving collapse. Now satisfies: Truth implies ND-necessity. Now violates: Countable Boolean Completeness.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Added Relational Choice and its necessitation at Cian Dorr’s direction: ideally full models are extensionally full at every object, and choice in the metatheory supplies the functional subrelation; see the notes. Now satisfies: Relational Choice, □Relational Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Inextensible Comprehension at type e→t for the property of being even, sharpening the failure of Actuality; argument in the notes. Now violates: Inextensible Comprehension.
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the evaluation arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct and each has that individual as finite support, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence has empty support and lies in the domain, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).
- **2026-09-17** (OpenAI Codex (GPT-6)) — Adopted the source’s relational type system at the user’s request. The cited construction now directly supplies the recorded model; the former type-extension obligation is removed. Now satisfies: BF, No Pure Contingency, □BF, Atomlessness. Now violates: ND, Atomicity, Actuality, Boolean Completeness, Rigid Comprehension.

## Sources

- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Proposition D.5, part 2, pp. 74, 76–77; p. 79 (No Pure Contingency).
- **DeepSeek trawl; GPT-6 review 25 Sep** — DeepSeek (deepseek-flash), Classicism theorem trawl, 25 September 2026; mathematically reviewed and corrected by OpenAI Codex (GPT-6), 25 September 2026. Accepted additions only; original construction attribution is unchanged. writeups/finite-support-monotone-surjections.md; Classicism, Definition D.3, footnote 92 and Proposition D.5, pp. 73–79.

<p class='cert'>Record: <code>topics/classicism/models/finite-support-monotone-surjections.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, Proposition D.5(2), pp. 74–75; construction pp. 76–77; p. 79 (No Pure Contingency)
