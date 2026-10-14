# Symmetric ideally-full model: arrows omitting or reserving a fixed individual [one individual]

<p class='cert'>Model — Source: BC does not imply RC (draft); produced by Cian Dorr; recorded by Claude Opus 5 (Anthropic), 19 September 2026.</p>

## Package

- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **Inextensible Comprehension.** Every relation, including a proposition, is coextensive with a inextensible one.
- **Rigid Power.** If a relation is rigid, so is the property of being a rigid relation that entails it.
- **Boolean Completeness.** Every property of entities of a relational type has a greatest lower bound in that type.
- **Truth implies ND-necessity.** Every truth is ND-necessary, that is, necessary under the distinctness-preserving modality.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ BF (type t).** BF (type t) in the displayed closed propositional formulation.
- **¬ Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Possible Infinity (type e).** Possibly there are not finitely many individuals: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

A symmetric ideally-full intensional action model over one object, the set of natural numbers. Its arrows are of two disjoint kinds: the surjections for which the distinguished individual is its own only preimage, and the functions that omit the distinguished individual from their range. Its symmetry group is the permutations fixing that individual, which is now a proper subset of the first kind. An arrow's value at the distinguished individual still tells the two kinds apart, but no finite set separates any arrow. The evaluation point is the identity arrow.

Individuals, fixed for this record: there is a single individual at every object. The arrows still act on the base as the construction says, and the base still supplies the pinning sets and the symmetry groups.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Symmetric ideally-full models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Atomlessness.

The first class of arrows contains non-injective ones, which restores the arguments used for the all-surjections model: given a true proposition pinned down by a finite set containing the distinguished individual and one other, the proposition that a fresh individual is not collapsed with that set is a strictly stronger truth; and the same splitting applied to an arbitrary nonzero proposition rather than a true one gives Atomlessness.

*By Cian Dorr, 2026-09-19.*

### Holds Inextensible Comprehension.

At every relational type, by an adaptation of the argument recorded for the all-surjections model (symmetric-all-surjections), whose facts (1)–(3) and transversal lemma are used here. Write $0$ for the distinguished individual, $A$ for the first class of arrows (surjections with $0$ as its own only preimage) and $B$ for the second (arrows omitting $0$ from their range). $B$ is absorbing: if $h\in B$ then $i\circ h$ omits $0$, since $i0=0$ only when $i\in A$ and then $i$ sends nothing else to $0$. So the proposition $\alpha:=\{k : k0=0\}$, the class $A$, is true at $1$, pinned down by $\{0\}$, symmetric, and once false stays false.
Given $X$ pinned down by $S_X$, put $S:=S_X\cup\{0\}$ and $Y:=\lambda\bar z\, .\,\alpha\land\delta_S\land X\bar z$, with $\delta_S$ the proposition that no two members of $S$ are collapsed. $Y$ is symmetric, pinned down by $S$ and coextensive with $X$. At a world in $B$, or one collapsing $S$, $Y$ is empty there and at every world it sees. A world $i\in A$ injective on $S$ can be relabelled by a permutation fixing $0$, hence in the symmetry group, so that it fixes $S$ pointwise. For such $i$ the transversal lemma holds: $i$ is surjective, preimages of points outside $S$ lie outside $S$, the permutation $\tau$ of $\mathbb N\setminus S$ fixes $0$ and so lies in the symmetry group, which keeps the extension of $X$ at $1$ closed under $\tau\cdot$, and $i\circ\tau\in A$ fixes the pinning set of $r$. The rest of the argument, including the leading box, goes through verbatim. BF fails here, so the surjectivity used in the lemma is available only at the worlds in $A$; the conjunct $\alpha$ removes the others.

*By Claude Opus 5.5 (Anthropic), at Cian Dorr's request, 2026-09-27.*

### Holds Rigid Power.

The argument rigid-power-surjections, adapted. Let $d$ be the distinguished individual and $B$ the others; the kind-$A$ arrows are the surjections with $d$ its own only preimage, the kind-$K$ arrows the maps into $B$; an arrow's kind is its value at $d$. Put $d$ in every pinning set below; Tame Rigidity holds at every type (tame-rigidity-factorizable).
Stable sets: if a set of tuples is closed under the kind-$A$ arrows fixing $P$, its $B_P$ is weakly rigid. In the proof take $u$ of kind $A$ fixing $P$, sending $M\setminus P$ to fresh points of $B$ outside $Q$, and $r$ of the kind of $l$; every prescribed value other than at $d$ lies in $B$, so $r$ extends to an arrow of that kind.
Exact images: call $j$ regular when it maps $B$ onto $B$; every kind-$A$ arrow is regular. For weakly rigid $F$ with extension $E$, $F_j=jE$ for every regular $j$, taking the $u$ of the exact-image step of kind $A$ fixing $S$; the values prescribed off $S$ lie in $B$ and regularity supplies preimages in $B$.
Lifting: extend $k|_N$ to a regular $j$ of $k$'s kind with finitely many non-singleton fibres, all finite, put them inside $P$, and take $T\setminus\{d\}\subseteq jP$. For $u$ of kind $A$ fixing $P$, define $v$ by $vj=ju$ on the range of $j$, and, when $j$ has kind $K$ (range $B$), $v(d):=d$. Then $v$ maps $B$ onto $B$, has no preimage of $d$ in $B$, and fixes $T$: it is a kind-$A$ arrow fixing $T$. So $\{a\in E:ja\in D\}$ is closed under the kind-$A$ arrows fixing $P$, and the rest is as before: Rigid Power at every type, for either choice of individuals.

*Address: `symmetric-range-gap-without-actuality-individuals-singleton#rigid-power`. By GPT-6 Astra (OpenAI), at Cian Dorr's request; checked and recorded by Claude Opus 5.5 (Anthropic), 2026-10-11.*

### Holds Boolean Completeness.

At every relational type: a property $F$ of type-$\tau$ entities has a least upper bound, the union of the hulls of its instances. Let $F$ be pinned down by $N\supseteq M_0$. For each instance $u$ of $F$ at the identity, its hull is the closure of $u$ under the arrows that $N$ does not separate from the identity, transported along the arrows agreeing with the identity on $N$; it is symmetric, pinned down by $N$ (by (B1), which splices an arrow agreeing with $h'$ on the instance's pinning set with $h$ on $N$), and an upper bound of $u$. Every upper bound $z$ of all the instances, pinned down by $N'$, contains every hull: given a member of a hull, (B2) supplies a symmetry fixing $N$ and moving the instance's pinning set off $N'$, whose image is again an instance (by the orbit lemma, Lemma 35), lying under $z$; and $z$, pinned down by $N'$, cannot tell the moved instance's tuple from the original. The union of the hulls is pinned down by $N$ and symmetric, so it is in the domain, and it is the least upper bound.

*Source: Boolean Completeness does not imply Rigid Comprehension, Theorem 36, p. 18; Corollary 37, p. 19. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#boolean-completeness`. It requires that There is a finite set $M_0$ of individuals at the evaluation object such that: (B1) for every finite $M\supseteq M_0$ and every arrow $h$ from the evaluation object to itself that $M$ does not separate (some arrow $k\notin G$ agrees with $h$ on $M$, or $h\in G$), every arrow $h'$ agreeing with $h$ on $M$, and finite $P,Q$ with $P\cap Q\subseteq M$, some arrow agrees with $h'$ on $P$ and with $h$ on $Q$; and (B2) for finite $N\supseteq M_0$ and finite $P,Q$, some member of the symmetry group fixes $N$ pointwise and moves every member of $P$ outside $N$ off $Q$. The arrows in (B1) go from the evaluation object to any one object, and $M$ separates $h$ when every arrow agreeing with $h$ on $M$ is a member of the symmetry group of the evaluation object. These are the hypotheses of Dorr's main theorem (draft, Definitions 28–30, Theorem 36). Here: With $M_0=\{0\}$, the distinguished individual (the draft's argument for this model). Two arrows agreeing there lie in the same one of the two classes, and a prescription taken from the two of them extends within that class, by nonzero values in the second case and by surjective nonzero values in the first; points are moved off a finite set by a permutation fixing $0$. By Cian Dorr, 2026-09-19.*

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The draft's main theorem, which the all-surjections and collapse-pair models each applied in an argument of their own, stated once; what each member does to meet its hypotheses is its reason for meeting hull-conditions. Proved in Lean (SymBase.lub_of_hull).

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* No longer requires one-object-action-model: as the draft notes (proof of Proposition 40), nothing in the theorem uses a single object, pinning, separation, amalgamability and hulls all quantifying over arrows with a fixed target; the condition hull-conditions now says so.

### Fails BF (type t).

In a one-object finitely pinned model, BF (type t) fails as soon as there are a finite $N$, an arrow $i$ and a proposition $q$ in the domain that is the transport $i^{\prime}\cdot p=\{k : k\circ i^{\prime}\in p\}$ of no proposition $p$ along any arrow $i^{\prime}$ agreeing with $i$ on $N$: the intension $X:=\{\langle r,j\rangle : r\ne q\text{ or }j\text{ disagrees with }i\text{ on }N\}$, which the condition puts in the domain, contains $\langle i^{\prime}\cdot p,i^{\prime}\rangle$ for every $p$ and $i^{\prime}$, so $\forall p\, .\,\Box Xp$ holds at the identity, and omits $\langle q,i\rangle$, so $\Box\forall p\, .\,Xp$ fails there. Since membership of $k$ in $i^{\prime}\cdot p$ depends only on $k$ restricted to the range of $i^{\prime}$, it suffices that $q$ separate two arrows agreeing on every such range, as the condition provides.

*General argument `arguments/barcan-t-transport`. It requires that The model is a one-object action model whose entities are finitely pinned, and there are a finite set $N$, an arrow $i$ and a proposition $q$ in the domain such that $q$ separates two arrows that agree on the range of every arrow agreeing with $i$ on $N$, and the intension $\{\langle r,j\rangle : r\ne q\text{ or }j\text{ disagrees with }i\text{ on }N\}$ is in the domain. Here: Take $N=\{0\}$, $i$ any arrow with $i0\ne0$, so that every arrow agreeing with it on $N$ omits $0$ from its range, and $q:=\{k : k0=0\}$, the first class of arrows, pinned down by $\{0\}$ and symmetric: an arrow $k$ of the first class and the arrow $k^{\prime}$ agreeing with it off $0$ but sending $0$ elsewhere, which omits $0$ from its range since $0$ is $k$’s only preimage of $0$, are separated by $q$. The intension the argument uses is pinned down by $N$, and symmetric, since $g\cdot q=q$ for $g$ fixing $0$ and $(g\circ j)0=0$ iff $j0=0$, so it lies in the domain. By Claude Fable 5.1 (Anthropic), answering Cian Dorr’s question whether the failure of BF sharpens to type $t$, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support group's argument and the symmetric range-gap models' copies stated once for the topic; that $X$ is in the domain (pinned down by $N$, and in a symmetric model symmetric) is now part of each record's reason for meeting transport-gap.

### Holds Truth implies ND-necessity.

Let $p$ be true, pinned by $N$ (and symmetric, when there is a symmetry group), and let $N^\prime$ be as in the condition. Let $q$ be the set of arrows that some arrow composes to agree with the identity on $N^\prime$; it is true, pinned by $N^\prime$, symmetric, and $\Diamond q=q$. By the condition every member of $q$ agrees on $N$ with a symmetry (or the identity), so lies in $p$ together with the identity. Hence $\Box(\Diamond q\to p)$ with $q$ true, i.e. $\Box_{\ne}p$.

*General argument `arguments/dpc-retractable-actual-pattern`. It requires that For every finite set $N$ of individuals at the evaluation object there is a finite $N^\prime\supseteq N$ such that every arrow $u$ out of that object for which some arrow $x$ makes $x\circ u$ agree with the identity on $N^\prime$ agrees on $N$ with a member of the symmetry group (with the identity, when the model has no symmetry group). Here: With $N^\prime=N\cup\{0\}$: if $x\circ u$ is the identity on $N^\prime$ then $u$ fixes $0$, so is of the first kind, and is injective on $N^\prime$; it therefore agrees on $N$ with a permutation fixing $0$, a member of the symmetry group. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-10-14.*

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: It has one object (Dorr, draft, §3.1: closed pure terms denote entities fixed by every arrow). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Axiom of Infinity (type e), Infinity Schema (type e), Possible Infinity (type e).

No two individuals are distinct, and the numeral $\operatorname{Suc}_e\mathbf{0}_e$ holds of the universal property at type $e$ at every world.

*General argument `arguments/one-individual`. It requires that There is exactly one individual, at every world. Here: There is a single individual at every object. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds Tame Rigidity.

Write $B_N(E)$ for the intension $k\mapsto\bigcup\{k^{\prime}\cdot E:k^{\prime}\text{ agrees with }k \text{ on }N\}$; it is pinned down by $N$, and symmetric when the model is, since the symmetry group consists of arrows and $(gk)\cdot E=g\cdot(k\cdot E)$, so it is in the domain. (1) A relation $Y$ pinned down by $S$, with extension $E$ at the identity, is weakly rigid iff $Y=B_S(E)=B_N(E)$ for every finite $N\supseteq S$: weak persistence gives $k\cdot E\subseteq Y_k$, and with pinning $B_S(E)\subseteq Y$; a domain element $X$ with $\Box X$ true of each member of $E$, pinned down by $N$, contains $B_N(E)$, so weak inextensibility says exactly that $Y\subseteq B_N(E)$ for every finite $N$, and $B_N(E)\subseteq B_S(E)$ for $N\supseteq S$. (2) Rigidity is (1) at every world: for each arrow $h$, $h\cdot Y$, with $(h\cdot Y)_k=Y_{kh}$, must satisfy $k\cdot Y_h\subseteq Y_{kh}\subseteq B_N(Y_h)_k$ for all $k$ and finite $N$. (3) Let $Y$ be weakly rigid. Persistence at $h$: $k\cdot Y_h=\bigcup\{(kk^{\prime\prime})\cdot E:k^{\prime\prime}\text{ agrees with }h\text{ on }S\}\subseteq B_S(E)_{kh}=Y_{kh}$. Inextensibility at $h$: given $N$, take $N^{\prime\prime}$ from the condition. By (1), $Y_{kh}=B_{N^{\prime\prime}}(E)_{kh}$, so a member of it is $k^{\prime}\cdot e$ with $e\in E$, pinned down by some finite $M$, and $k^{\prime}$ agreeing with $kh$ on $N^{\prime\prime}$. The condition gives $k^{\prime\prime}$ agreeing with $h$ on $N^{\prime\prime}$ and $j$ agreeing with $k$ on $N$ with $jk^{\prime\prime}$ agreeing with $k^{\prime}$ on $M$, so $k^{\prime}\cdot e=j\cdot(k^{\prime\prime}\cdot e)$, where $k^{\prime\prime}\cdot e\in B_{N^{\prime\prime}}(E)_h=Y_h$; hence $k^{\prime}\cdot e\in B_N(Y_h)_k$. So every weakly rigid relation, at every type, is rigid. With No Pure Contingency, which holds in one-object models, the map's results give $\Box$Tame Rigidity.

*General argument `arguments/tame-rigidity-factorizable`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: It has one object (Dorr, draft, §3.1: closed pure terms denote entities fixed by every arrow). It requires that Write an entity of relational type at the evaluation object as its intension $k\mapsto Y_k$ over the arrows $k$ out of it, so that $Y\bar a$ holds at $k$ iff $k\cdot\bar a\in Y_k$; $Y$ is pinned down by a finite set $N$ of the points the arrows act on when $Y_k=Y_{k^{\prime}}$ for any arrows $k,k^{\prime}$ agreeing on $N$. Every entity in a domain is pinned down by a finite set, in the sense that $k\cdot x=k^{\prime}\cdot x$ for arrows agreeing on it, and the domain of each relational type at the evaluation object holds every intension pinned down by a finite set (in a symmetric model, every symmetric one). Here: A relational domain holds exactly the symmetric intensions pinned down by a finite set, and every individual $n$ is pinned down by $\{n\}$. It requires that For every arrow $h$ out of the evaluation object and finite sets $N,S$ there is a finite $N^{\prime\prime}\supseteq S$ such that, whenever $k^{\prime}$ agrees with $k\circ h$ on $N^{\prime\prime}$, for every finite $M$ some arrows $k^{\prime\prime}$ agreeing with $h$ on $N^{\prime\prime}$ and $j$ agreeing with $k$ on $N$ have $j\circ k^{\prime\prime}$ agreeing with $k^{\prime}$ on $M$. Here: As in symmetric-range-gap, with $d$ in $S$ and $N$ and the kinds told apart by the value at $d$, the first kind now being the surjections for which $d$ is its own only preimage. For $m\in M\setminus N^{\prime\prime}$ let $k^{\prime\prime}m$ be some $n\in N$ with $kn=k^{\prime}m$ when $k$ is of the first kind and there is one (then $n\ne d$, as $k^{\prime}m\ne d$), and otherwise a fresh point outside $N\cup\{d\}$, one for each value of $k^{\prime}$; let $j$ agree with $k$ on $N$ and send each fresh point to its value, never $d$. Arrows of the first kind need only be surjective with $d$ the only preimage of $d$, so $k^{\prime\prime}$ and $j$ extend to arrows of the kinds of $h$ and $k$, and $jk^{\prime\prime}$ agrees with $k^{\prime}$ on $M$. By Claude Opus 5.5 (Anthropic), on Cian Dorr's request to settle Tame Rigidity where it was open, 2026-10-09.*

### Holds No Contingency (signature Σ), B for sentences of Σ.

Each constant of Σ denotes what the closed pure term $\top_\tau$ of its type denotes, so a closed sentence of the language of Σ denotes what the pure sentence with $\top_\tau$ in place of each constant denotes; if true it is necessary by No Pure Contingency, which holds here. So No Contingency (signature Σ) holds, and B for sentences of Σ with it: a true Σ-sentence is necessary, hence necessarily possible.

*General argument `arguments/sigma-top-npc`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Cian Dorr (observation); recorded by Claude Opus 5.5 (Anthropic), 2026-10-02.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The argument sigma-single-top, for Σ a single constant of type $t$ denoting $\top$, stated for every interpretation of Σ by top elements, now that such interpretations have no individual constants. It replaces that argument and nc-sigma-homogeneous, which reached the same verdicts through an individual constant when the model's automorphisms carry every individual to every other. With an individual constant and no such automorphisms the verdicts were unknown in 19 models, and nowhere did the individual constants settle a verdict differently.


## Notes

The second of the draft's two variants in which BF fails, arranged so that the range deficiency no longer brings Actuality with it. Since Actuality fails, Weak Rigid Comprehension and Rigid Comprehension fail too, which are recorded as derived verdicts. Atomlessness is the Proposition 45 argument for Atomicity read for an arbitrary nonzero proposition, and the failure of ND at type e follows from the non-injective arrows; neither is displayed separately in the draft. The source is a work in progress. Everything that implies these fails with them.

## History

The record's revision log before it was written as arguments.

- **2026-09-27** (Claude Opus 5.5 (Anthropic), at Cian Dorr's request) — Recorded Inextensible Comprehension at every relational type, adapting the all-surjections argument: the witness also conjoins the proposition that the distinguished individual is fixed, which confines it to the surjective arrows. Replaces the note that left it unknown. Now satisfies: Inextensible Comprehension.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Relational Choice, at types (e→t) and e: a functional subrelation of the serial relation pairing each property with its members would be symmetric and finitely pinned, and a symmetry fixing its pinning set would carry its choice for the property of lying outside that set to a second choice. Cian Dorr’s observation that a choice cannot be finitely pinned; argument in the notes. Now violates: Relational Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Noted why Inextensible Comprehension is left unknown: its type-t and type-(e→t) instances hold here, so the failure of Actuality does not sharpen to it at those types.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of BF at type t, sharpening the failure of BF; argument in the notes. Now violates: BF (type t).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the identity arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct, symmetric and pinned by that individual, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence symmetric and pinned by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, §7.2, p. 22; Proposition 45, p. 22; Remark 38, p. 19.

<p class='cert'>Record: <code>topics/classicism/models/symmetric-range-gap-without-actuality.yaml</code></p>

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §7.2, p. 22; Proposition 45, p. 22; Remark 38, p. 19
