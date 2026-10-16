# Finite-support action model: permutations of N

<p class='cert'>Model — Source: Classicism (2024); produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), 17 September 2026.</p>

## Package

- **ND.** Distinct things of any type are necessarily distinct.
- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **□Intensional Choice.** Every closed instance of Intensional Choice is necessary. Box the entire object-variable closure; retain the same type range and other schema side conditions.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **□Transversal Choice.** Necessarily, every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Weakly Inextensible Comprehension.** Every relation, including a proposition, is coextensive with a weakly inextensible one.
- **¬ Boolean Completeness.** Every property of entities of a relational type has a greatest lower bound in that type.
- **¬ Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable relative to a type $\sigma$ when it injects into the finite cardinalities of properties of type $\sigma$; one instance for each $\sigma$.
- **¬ Boolean Completeness (type t).** Boolean Completeness (type t) in the displayed closed propositional formulation.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

Proposition D.5, part 1 (pp. 75–76): the one-object category whose arrows are all the permutations of $\mathbb N$, so that each arrow $h$ represents the possibility in which each individual $n$ plays the role actually played by $hn$, and the roles can be redistributed in any way. In every part, $W_0^\ddagger$ is the set of finite subsets of $\mathbb N$ and the model is ideally full: a proposition is a set of arrows whose membership depends only on the arrows’ values on some finite set of numbers (it is pinned down by that set), and an entity of a higher type is an applicative behaviour profile pinned down by a finite set in the same sense. The individuals are the natural numbers, acted on by the arrows themselves. Propositions and properties are thus about finitely many numbers and indifferent to how the arrows treat the rest. Evaluation point: the sole object, at the identity arrow.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Finite-support action models on one object, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds ND, Atomlessness.

Every arrow is invertible, so transport along it is injective at every type.

*Source: Classicism, Proposition D.5(1), pp. 75–76. By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The reason for No Distinctness Necessity's holding, added so that it visibly covers the variant with a single individual; Atomlessness concerns propositions only.

### Fails Weakly Inextensible Comprehension.

At type $t\to t$, for the family $E$ of propositions $p_n$ that $n$ is fixed: for $Y$ weakly inextensible with extension $E$ pinned down by $S$, pick $k\notin S$ and let $X$, pinned down by $S_X:=S\cup\{k\}$, hold at an arrow $h$ exactly of the propositions $\{i : i(m)=n\}$ with $n\notin S_X$ and of the propositions $\{i : i(h(n))=n\}$ with $n\in S_X$; $X$ is necessary of every $p_n$, but at a permutation $h$ fixing $S$ pointwise and moving $k$ its extension omits $p_k$, which the extension of $Y$ at $h$ contains. Inextensible Comprehension fails with it.

*By Claude Fable 5.1 (Anthropic), answering Cian Dorr’s question whether the failure of Actuality can be sharpened to a failure of Inextensible Comprehension, 2026-09-23.*

*Revised 2026-09-25 by Claude Opus 5.5 (Anthropic):* Merged the two sets of arguments recorded on 23 and 25 September into one: the simpler 25 September argument for Inextensible Comprehension, which also refutes the weak form, replaces the 23 September one.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Cut to its type $t\to t$ part; the type $e\to t$ part duplicated the group's shared argument weakly-inextensible-comprehension, which applies here.

### Holds Axiom of Infinity (type e).

The individuals are the natural numbers and identity at the evaluation arrow is literal, so no numeral counts them. The set of numerals at type $e$ is invariant under every arrow, hence has empty support and lies in the domain, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#axiom-of-infinity`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Split from the argument for both types; the type-$t$ half, which does not need infinitely many individuals, is axiom-of-infinity-t.

### Holds Axiom of Infinity (type t).

The propositions that a given number is fixed by the arrow, one for each number, are pairwise distinct and each has that number as finite support, so there are infinitely many propositions. The set of numerals at type $t$ is invariant under every arrow, hence has empty support and lies in the domain, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#axiom-of-infinity-t`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$t$ half of the old argument, "individual" becoming "number", so that it covers the one-individual variants.

### Fails Boolean Completeness.

At type $e\to t$. In the source's terms an upper bound of the haecceities of the members of $A$ is a persistent property whose extension contains $A$. A least one, pinned down by $\{0,\ldots,n\}$, would be the strongest such property pinned down by $\{0,\ldots,n\}$, and would also lie below the strongest pinned down by $\{0,\ldots,m\}$ for each $m>n$, which by the condition is strictly stronger. So the haecceities have no least upper bound.

*Source: Classicism, Proposition D.5, parts 1–8, pp. 75–79. From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#boolean-completeness`. It requires that For some set $A$ of individuals, the strongest persistent property whose extension contains $A$ and which is pinned down by $\{0,\ldots,n\}$ becomes strictly stronger as $n$ grows. Here: With $A$ the even numbers, the part 2 argument transfers: the strongest persistent property pinned down by a finite $X$ whose extension contains the even numbers has, at an arrow $h$, the extension $h(X\cap\text{evens})\cup(\mathbb N\setminus hX)$, which strictly shrinks as $X$ grows. By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Stated once for the group, with the step from "ever stronger" to the missing least upper bound spelled out; each member's strongest persistent properties moved to the condition unbounded-haecceities.

### Fails Countable Boolean Completeness.

At type $e\to t$: the property $E$ whose extension is the family of haecceities of the members of $A$, which has no least upper bound by the shared argument boolean-completeness, is countable, and the extensional fullness the source invokes to put $E$ in the domain also puts in the relation pairing the haecceity of the $k$-th member of $A$ with the numeral $k$, which injects $E$ into the numerals.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#countable-boolean-completeness`. It requires that For some set $A$ of individuals, the strongest persistent property whose extension contains $A$ and which is pinned down by $\{0,\ldots,n\}$ becomes strictly stronger as $n$ grows. Here: With $A$ the even numbers, the part 2 argument transfers: the strongest persistent property pinned down by a finite $X$ whose extension contains the even numbers has, at an arrow $h$, the extension $h(X\cap\text{evens})\cup(\mathbb N\setminus hX)$, which strictly shrinks as $X$ grows. By Claude Fable 5.1 (Anthropic), 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Now builds on the shared argument boolean-completeness instead of on each member's source argument; no change of substance.

*Revised 2026-10-16 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Refutes the instance of Countable Boolean Completeness counting at $e$, which the principle, now schematic in that type, includes.

### Fails Boolean Completeness (type t).

The source (n. 92) conjectures this but does not show it. Any set $F$ of propositions is the extension at the identity of an element of the domain at type $t\to t$, namely the profile $\langle h,p\rangle\mapsto\{i : i\cdot p\in F\}$: it is natural, independent of $h$ and so pinned down by the empty set, and each of its values is pinned down by the pinning set of $p$, since $i\cdot p$ depends only on the values of $i$ there. A least upper bound of $F$ under entailment is a least finitely pinned superset of $\bigcup F$, and it exists only if the least $S$-pinned superset of $\bigcup F$ stops shrinking as the finite set $S$ grows. So the family $F$ of the condition has no least upper bound, and, taking pointwise negations, the family of complements has no greatest lower bound.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#boolean-completeness-t`. It requires that Some family $F$ of propositions has no least finitely pinned superset of its union $\bigcup F$. Here: Let $F$ be the family of propositions $A_m$ ($m\ge1$), each pinned down by $\{0,m\}$, that the permutation swaps $0$ and $m$. A permutation $\pi$ belongs to the least superset of $\bigcup F$ pinned down by $S=\{0,\ldots,N\}$ iff either $\pi(0)\in S\setminus\{0\}$ and $\pi(\pi(0))=0$, or $\pi(0)\notin S$ and $0\notin\pi(S)$; the $3$-cycle $(0\ N{+}1\ N{+}2)$ satisfies the second clause for $S$ but neither clause for $\{0,\ldots,N+1\}$, so these supersets strictly shrink. By Claude Fable 5.1 (Anthropic), 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The seven members' copies stated once, each member's family moved to the condition no-least-pinned-cover; the truncations' separate argument of 23 September, by Claude Fable 5.1 prompted by Cian Dorr, is now its witness, its own proof that the family is in the domain giving way to the profile above. The trawl's second arguments for the same verdict (25 September, DeepSeek, reviewed by OpenAI Codex) were dropped.

### Fails Countable Boolean Completeness.

At $\sigma=\tau=t$: the family $F$ of the condition no-least-pinned-cover, which has no least upper bound by the shared argument boolean-completeness-t, is in every member a sequence of propositions $A_m$, and it is countable relative to $t$. The numerals at type $t$ are the finite cardinalities and are pairwise distinct (the shared argument axiom-of-infinity-t), and extensional fullness puts in the domain the relation pairing each $A_m$ with the $m$-th numeral, which injects $F$ into them. This needs no infinity of individuals, so it covers the members with a single individual.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#countable-boolean-completeness-t`. It requires that Some family $F$ of propositions has no least finitely pinned superset of its union $\bigcup F$. Here: Let $F$ be the family of propositions $A_m$ ($m\ge1$), each pinned down by $\{0,m\}$, that the permutation swaps $0$ and $m$. A permutation $\pi$ belongs to the least superset of $\bigcup F$ pinned down by $S=\{0,\ldots,N\}$ iff either $\pi(0)\in S\setminus\{0\}$ and $\pi(\pi(0))=0$, or $\pi(0)\notin S$ and $0\notin\pi(S)$; the $3$-cycle $(0\ N{+}1\ N{+}2)$ satisfies the second clause for $S$ but neither clause for $\{0,\ldots,N+1\}$, so these supersets strictly shrink. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-16.*

### Fails Weakly Inextensible Comprehension.

At type $e\to t$, for the property of being even, which is in the domain as the constant intension $\{\langle b,h\rangle : b\text{ even}\}$, pinned down by $\emptyset$. Unpacking $\operatorname{Inextensible}$ as in the left-to-right half of Dorr’s rigidity criterion (draft, Lemma 14, p. 7, with Lemma 13): even the unboxed matrix, evaluated at the identity, says that $Y$ is contained in every persistent (transport-closed) $B$ in the domain whose extension includes $Y$’s. For a finite $N^{\prime}$, the smallest such $B$ pinned down by $N^{\prime}$ is $B_{N^{\prime}}:=\{\langle b^{\prime\prime},i^{\prime}\rangle : i^{\prime\prime}(b)=b^{\prime\prime}\text{ for some even }b\text{ and some arrow }i^{\prime\prime}\text{ agreeing with }i^{\prime}\text{ on }N^{\prime}\}$, which is transport-closed and pinned down by $N^{\prime}$. Now let $Y$ be coextensive with evenness and pinned down by a finite $N_0$; then $\langle b,i\rangle\in Y$ for every even $b$ and every arrow $i$ fixing $N_0$ pointwise. Take the arrow $i$, the even $b$ and the finite $N^{\prime}$ that the condition provides for $N_0$: no arrow agreeing with $i$ on $N^{\prime}$ sends an even number to $b$. So $\langle b,i\rangle\in Y\setminus B_{N^{\prime}}$, and $Y$ is not even weakly inextensible.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#weakly-inextensible-comprehension`. It requires that For every finite $N_0\subseteq\mathbb N$ there are an arrow $i$ fixing $N_0$ pointwise, an even $b$, and a finite $N^{\prime}$ such that no arrow agreeing with $i$ on $N^{\prime}$ sends an even number to $b$. Here: Let $i$ swap an even $b$ and an odd $o$, both outside $N_0$, and let $N^{\prime}:=\{o\}$: an arrow agreeing with $i$ on $\{o\}$ sends $o$ to $b$, so, being injective, it sends no even number to $b$. By Claude Fable 5.1 (Anthropic), answering Cian Dorr’s question whether the failure of Actuality can be sharpened to a failure of Inextensible Comprehension, 2026-09-23.*

*Revised 2026-09-25 by Claude Opus 5.5 (Anthropic):* Merged with the 25 September version; the argument already refutes the weak form, which was added.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Stated once for the group, the witness moving to the condition evens-avoidable.

### Holds Axiom of Infinity (type e), Infinity Schema (type e).

The Infinity schema holds, there being $n$ distinct individuals for every $n$. For the Axiom: by extensional fullness the domain has a property of cardinalities true of $Z$ exactly when every property $Z$ holds of has a finite extension. It holds of $\mathbf{0}_e$, which holds only of empty properties, and passes from $Y$ to $\operatorname{Suc}_e Y$, which holds of $F$ only if $Y$ holds of $F$ less one of its instances. So every finite cardinality has it, and none holds of the universal property, whose extension is infinite.

*General argument `arguments/infinitely-many-individuals`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. It requires that There are infinitely many individuals at the evaluation world. Here: The individuals are the natural numbers. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-06.*

### Holds Axiom of Infinity (type t), Infinity Schema (type t).

As for individuals (the argument infinitely-many-individuals), at type $t$: the Infinity schema holds, and by extensional fullness the property of cardinalities that hold only of properties with finite extensions is in the domain, has every finite cardinality, and excludes those holding of the universal property of propositions, whose extension is infinite.

*General argument `arguments/infinitely-many-propositions`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. It requires that There are infinitely many propositions at the evaluation world. Here: The propositions that a given number is fixed by the arrow, one for each number, are pairwise distinct, each pinned down by that number (the shared argument axiom-of-infinity-t). By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-06.*

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: With one object such an intension is constant, so it is pinned down by $\emptyset$, and the domain holds every finitely pinned intension. By Claude Fable 5.1 (Anthropic), at Cian Dorr's suggestion, 2026-10-03.*

### Holds □Relational Choice, □Transversal Choice.

At any reachable object $W$, let $U$ be a serial relation in the domain there. Using the axiom of choice, pick for each $x$ a $y$ with $(x,y)$ in the extension of $U$ at the identity, and let $S$ be the intension whose value at every arrow $W\to W$ is the graph of this choice and whose value at arrows with any other codomain is empty; it depends only on the codomain, so the condition puts it in the domain, and at the identity it is a functional subrelation of $U$. Likewise a set of representatives of an equivalence relation at $W$, made into such an intension, is a transversal. Since $W$ was any reachable object, both principles hold at every world.

*General argument `arguments/necessary-relational-choice-codomain-intensions`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: With one object such an intension is constant, so it is pinned down by $\emptyset$, and the domain holds every finitely pinned intension. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-10-14.*

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: Each part of Proposition D.5 is a one-object category acting on $\mathbb N$ (Appendix D, Definitions D.1–D.3). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

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

The cited construction is a model of the map’s relational-type framework. The description identifies its evaluation point; construction and verification are given at the PDF locations in References. The source derives the failure of Boolean Completeness through C5 and the failure of Actuality (Propositions 2.5–2.6), which gives nothing about countable families.

## History

The record's revision log before it was written as arguments.

- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added Transversal Choice, by the argument recorded for Relational Choice: the model is extensionally full at every object, so for an equivalence relation at the evaluation point a transversal of its extension there, chosen in the metatheory, is the extension of an element pinned down by the empty set; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun. Now satisfies: Transversal Choice.
- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added the failure of Boolean Completeness (type t) and of Inextensible Comprehension, with the arguments in the notes. Now violates: Boolean Completeness (type t), Inextensible Comprehension.
- **2026-09-25** (Claude Opus 5.5 (Anthropic)) — Merged the two sets of arguments recorded on 23 and 25 September into one: the simpler 25 September argument for Inextensible Comprehension, which also refutes the weak form, replaces the 23 September one. Now violates: Weakly Inextensible Comprehension.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Expanded the description from Appendix D, naming Proposition D.5 and its part; added the failure of Countable Boolean Completeness at type e→t; settled the Distinctness-preserving collapse. Now violates: Countable Boolean Completeness, Truth implies ND-necessity.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes. Now satisfies: No Contingency (signature Σ), B for sentences of Σ.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Added Relational Choice and its necessitation at Cian Dorr’s direction: ideally full models are extensionally full at every object, and choice in the metatheory supplies the functional subrelation; see the notes. Now satisfies: Relational Choice, □Relational Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Inextensible Comprehension at type e→t for the property of being even, sharpening the failure of Actuality; argument in the notes. Now violates: Inextensible Comprehension.
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the evaluation arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct and each has that individual as finite support, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence has empty support and lies in the domain, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).
- **2026-09-17** (OpenAI Codex (GPT-6)) — Adopted the source’s relational type system at the user’s request. The cited construction now directly supplies the recorded model; the former type-extension obligation is removed. Now satisfies: ND, BF, No Pure Contingency, □ND, □BF, Atomlessness. Now violates: Atomicity, Actuality, Boolean Completeness, Rigid Comprehension.

## Sources

- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Proposition D.5, part 1, pp. 74–76; p. 79 (No Pure Contingency).

<p class='cert'>Record: <code>topics/classicism/models/finite-support-permutations.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, Proposition D.5(1), pp. 74–75; construction pp. 75–76; p. 79 (No Pure Contingency)
