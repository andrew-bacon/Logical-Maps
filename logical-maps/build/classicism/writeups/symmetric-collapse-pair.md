# Symmetric ideally-full model: permutations and collapsers of a fixed pair (Base 2)

<p class='cert'>Model — Source: BC does not imply RC (draft); produced by Cian Dorr; recorded by Claude Opus 5 (Anthropic), prompted by Cian Dorr, 19 September 2026.</p>

## Package

- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Actuality.** There is a true proposition that entails every true proposition.
- **Boolean Completeness.** Every property of entities of a relational type has a greatest lower bound in that type.
- **Truth implies ND-necessity.** Every truth is ND-necessary, that is, necessary under the distinctness-preserving modality.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Atomicity (type t).** Every non-bottom proposition has an atom below it.
- **¬ Rigid Power.** If a relation is rigid, so is the property of being a rigid relation that entails it.
- **¬ Rigid Rigidity.** Being rigid is a rigid property of relations, including propositions.
- **¬ Relational Choice.** Every serial binary relation has a functional subrelation.
- **¬ Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

A symmetric ideally-full intensional action model over one object, the set of natural numbers. Its symmetry group is the permutations that preserve a fixed pair of individuals setwise, and its arrows are those permutations together with all the surjections that collapse the two members of that pair. Every arrow is therefore invertible or a collapser, and which it is can be read off from its behaviour on that pair. The evaluation point is the identity arrow.

Individuals, fixed for this record: the individuals at each object are the base the construction describes, and the arrows act on them as on the base.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Symmetric ideally-full models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Rigid Comprehension.

At every relational type. Given a relation with extension S pinned down by a finite set, take the least upper bound of the union of the haecceities of the members of S, computed with the fixed pair adjoined to the pinning set. Persistence is immediate, and the extension is exactly S because an arrow agreeing with the identity on a set containing the fixed pair is invertible. The rigidity criterion is then checked separately at invertible worlds, where leastness delivers it, and at collapsing worlds, where surjectivity supplies the preimages that persistence demands.

*By Cian Dorr, 2026-09-19.*

### Fails Atomicity (type t).

With the proposition that the two members of the fixed pair are identical as a nonzero proposition having no atom below it.

*By Cian Dorr, 2026-09-19.*

### Fails Rigid Power.

At type $e\to t$, with $F:=\top$: the argument of finite-support-pair-injections-or-collapses, whose witnesses are all symmetric, with the collapses kept surjective. Write $Z_k$ for the extension of a property $Z$ at the arrow $k$, so that $(h\cdot Z)_k=Z_{k\circ h}$. The step that needs care changes an arrow $j$ to hit a value $y$ at a point $x$ outside a finite $N\supseteq\{0,1\}$: for a collapse, put $j':=j\circ\tau$, where $\tau$ fixes $N$ pointwise, sends $x$ to a $j$-preimage $p$ of $y$, and maps the rest of $\mathbb N\setminus N$ onto $\mathbb N\setminus N$ (possible even if $p\in N$, $\tau$ not being required to be injective); then $j'$ is a surjective collapse agreeing with $j$ on $N$, with $j'x=y$. For a permutation and $y\notin j[N]$, put $j':=(y\ jx)\circ j$, a permutation preserving $\{0,1\}$ since $y,jx\notin\{0,1\}$.

(1) $\top$ is rigid: its inextensibility is $\Box$BF at type $e$, which holds.

(2) $Y$, with $Y_k:=\mathbb N\setminus\{k2\}$ at a permutation and $\mathbb N$ at a collapse, is in the domain (pinned down by $\{0,1,2\}$; symmetric, since $y\ne k2$ gives $gy\ne(g\circ k)2$) and rigid. It is persistent, every composite with a collapse being a collapse. It is inextensible at every world $w$: let $X$, pinned down by $N\supseteq\{0,1\}$, contain $\langle jx,j\rangle$ for every $x\in Y_w$ and arrow $j$, and let $y\in Y_{j\circ w}$. If $y=jn$ with $n\in N\cap Y_w$, then $\langle y,j\rangle\in X$. If $y=jn$ with $n\in N\setminus Y_w$, then $w$ is a permutation, $n=w2$, and $j\circ w$ is a collapse, so $j$ identifies $w0$ with $w1$ and is a collapse; if $y\notin j[N]$, $j$ is either. In both cases change $j$ as above at a fresh $x\notin N\cup\{w2\}$, so that $x\in Y_w$, $\langle y,j'\rangle\in X$, and by pinning $\langle y,j\rangle\in X$.

(3) Along a collapse a weakly rigid property $Z$, with extension $S$ and pinned down by $N\supseteq\{0,1\}$, has extension $\mathbb N$ or a finite one. If $S$ is infinite, then for any $b$ change the collapse $m$ as above at some $x\in S\setminus N$ to $m'x=b$; persistence gives $b\in Z_{m'}=Z_m$. If $S$ is finite, the symmetric property $k\mapsto k[S]$, pinned down by $S$, necessarily holds of each member of $S$, so $Z_m\subseteq m[S]$.

Let $R:=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le\top$, the value of a closed pure term, so that its extension at every arrow is the set of rigid properties. Let $\mathbf X$ hold of $W$ at $k$ iff $W=k'\cdot Z$ for some rigid $Z$ and some arrow $k'$ agreeing with $k$ on $\{0,1\}$: pinned down by $\{0,1\}$, and symmetric, since $g\cdot(k'\cdot Z)=(g\circ k')\cdot Z$ and the rigid properties are closed under transport along symmetries. It necessarily holds of every instance of $R$. At a collapse $c$, every $k'$ agreeing with $c$ on $\{0,1\}$ is a collapse, so by (3) every member of $\mathbf X$'s extension has extension $\mathbb N$ or a finite one, while $Y$, in $R$'s extension there by (2), has extension $\mathbb N\setminus\{2\}$. So $R\not\le\mathbf X$: $R$ is not even weakly inextensible, though $\top$ is rigid. With Rigid Comprehension holding, Rigid Comprehension (boxed, and with Actuality, BF and Boolean Completeness) does not imply Rigid Power.

*Address: `symmetric-collapse-pair#rigid-power`. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-08.*

*Revised 2026-10-08 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* First given on 8 October for symmetric-pair-injections-or-collapses, Cian Dorr's symmetric analogue of finite-support-pair-injections-or-collapses, which differs from this model only in not requiring the collapses to be surjective; that record was removed the same day, having the same verdicts as this one once this argument was recorded.

### Fails Rigid Rigidity.

Both arguments for the failure of Rigid Power (at type $e\to t$ when the individuals are the natural numbers, at type $(t\to t)\to t$ when there is one individual) take $F:=\top$. Their power property $\lambda X\, .\,\operatorname{Rigid}(X)\land X\le\top$ is $\lambda X\, .\,\operatorname{Rigid}(X)$, since $X\le\top$ is a theorem of C, and they show that it is not weakly inextensible. So Rigid Rigidity fails at the same type.

*Address: `symmetric-collapse-pair#rigid-rigidity`. By Claude Opus 5.5 (Anthropic), on Cian Dorr's request to settle Rigid Rigidity where it was open, 2026-10-10.*

### Fails Relational Choice.

At the types $(e\to t)$ and $e$. Let $U:=\lambda Xy\, .\,Xy\lor\neg\exists z\, .\,Xz$, a closed term, hence in the domain, and serial. A functional subrelation $S$ of $U$ would lie in the domain at the evaluation object, so it is symmetric and pinned down by a finite set $N$. Two facts about such an $S$ (Dorr, draft, Lemma 19(iv)): every $g\in G$ fixing $N$ pointwise satisfies $g^{[\sigma]}S=S$, and symmetry gives $\langle gA,gy,g\rangle\in S$ whenever $\langle A,y,1\rangle\in S$; together, $\langle gA,gy,1\rangle\in S$. Now let $A$ be the property the condition gives for $N$. Its extension is nonempty, so $S$ relates $A$ at the identity to some $y$ in its extension. The condition gives a member $g$ of the symmetry group that fixes $N$ pointwise, fixes $A$ and moves $y$ to some $gy\ne y$, so $S$ relates $A$ to $gy$ as well, and $S$ is not functional at the identity arrow. The well-ordering of the individuals that Cian Dorr had in mind is refuted by the same two facts, but the direct route needs no derivation of a well-ordering from Relational Choice in C.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#relational-choice`. It requires that For each finite set $N$ of individuals at the evaluation object, some property $A$ in the domain has a nonempty extension there, and each individual $y$ in that extension is moved by a member of the symmetry group that fixes $N$ pointwise and fixes $A$. Here: $M=\{0,1\}$, the fixed pair, and for $N$ the property of not belonging to $N\cup\{0,1\}$: the transposition of $y$ with another individual outside $N\cup\{0,1\}$ fixes $\{0,1\}$, so lies in the symmetry group. By Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, after Cian Dorr’s observation that a choice over the individuals cannot be finitely pinned down, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The members' seven copies, which differed in the property $A$ and the transposition, stated once; each member's $A$ and transposition moved to the condition transposable. The qualitative-contrast model's second argument (OpenAI Codex, 24 September) was dropped.

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The condition transposable no longer mentions the finite set $M$ or the pinning of $A$ by $N\cup M$: the argument uses only that $g$ fixes $N$, the set pinning down $S$, and that $A$ is in the domain. So $g$ is now said to fix $N$ pointwise. Proved in Lean.

### Holds Axiom of Infinity (type e).

There are infinitely many individuals, and identity at the identity arrow is literal, so no numeral counts them. The set of numerals at type $e$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-e`. It requires that There are infinitely many individuals at the evaluation world. Here: The base is infinite. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$e$ half of the members' argument, stated once; "the individuals are the natural numbers" became "there are infinitely many individuals", which also covers the qualitative links model. The type-$t$ half is axiom-of-infinity-t.

### Holds Axiom of Infinity (type t).

The propositions $C_{n,m}:=\{h : hn=hm\}$, that an arrow collapses $n$ and $m$, are symmetric, since relabelling the individuals of a world by a member of the symmetry group keeps identities among them, and each is pinned down by $\{n,m\}$; by the condition infinitely many of them are pairwise distinct, so there are infinitely many propositions. The set of numerals at type $t$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-t`. It requires that There are infinitely many pairs of individuals such that, for any two of these pairs, some arrow collapses the one and not the other. Here: The pairs $\{n,m\}$ with $n,m\ge2$: a surjection that collapses $0$ with $1$ and $n$ with $m$, and nothing else, is an arrow. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Replaces the members' argument of 20 September (Claude Fable 5.1), which used the propositions $\{h : hn=n\}$ that an arrow fixes a given individual. Those are not symmetric when the symmetry group moves $n$: symmetry asks that $h\in p$ imply $g\circ h\in p$, and $(g\circ h)n=gn$.

### Holds BF.

At every type. Let $B$ be an entity at the target of an arrow $i$, pinned down by the finite set $M$, and choose a finite set $P$ with a map $s:M\to P$ such that $i\circ s$ is the identity on $M$, possible because $i$ is surjective. Put $A:=\{\langle\bar x,j\rangle : \langle\bar x,k\rangle\in B$ for some arrow $k$ with $k|_M=j\circ s\}$. This is well defined because $B$ is pinned down by $M$. It is pinned down by $P$ and symmetric, since $B$ is. And $i\cdot A=B$: $\langle\bar x,k\rangle\in i\cdot A$ iff $\langle\bar x,k\circ i\rangle\in A$ iff $\langle\bar x,k'\rangle\in B$ for some $k'$ with $k'|_M=k|_M$, iff $\langle\bar x,k\rangle\in B$. So every entity at every world is the transport of an entity at the evaluation point, and a relation that is necessarily true of every entity is necessarily true of all of them.

*Source: Boolean Completeness does not imply Rigid Comprehension, §3.1, p. 9; Proposition 22, p. 11. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#barcan-surjective`. It requires that Every arrow is surjective. Here: The arrows are permutations and surjections. It requires that At every object, the domains hold the symmetric intensions pinned down by a finite set: every object carries the ideal of finite sets. Here: Every object carries the ideal of finite sets. By Claude Opus 5.5 (Anthropic), at Cian Dorr's request, 2026-09-27.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The qualitative links model's argument, which proves the draft's claim for the all-surjections model ("at every type because every arrow is surjective and a finitely pinned symmetric intension can be pulled back along an arrow"), stated once for every member whose arrows are surjective.

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Requires finite-pinning as well, which the argument uses (a finite preimage of the pinning set): stated when the group's Lean parameter admitted a per-object ideal, for the two-object model whose second object is unpinned. Every member meeting surjective-arrows meets it.

### Holds Actuality.

The symmetry group is the smallest symmetric set of arrows containing the identity, and by the condition it is pinned down by a finite set, so it is a proposition in the domain, and an atom entailing every truth.

*Source: Boolean Completeness does not imply Rigid Comprehension, Proposition 24, p. 13; §7.1, p. 21; §8, pp. 23–26. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#actuality`. It requires that The symmetry group, the smallest symmetric set of arrows containing the identity, is pinned down by a finite set. Here: Membership in the symmetry group is detected by the fixed pair: an arrow is in it iff it does not collapse the pair. By Cian Dorr, 2026-09-19.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The three members' versions stated once; what pins the group down is each member's reason for meeting symmetry-group-pinned.

### Holds Boolean Completeness.

At every relational type: a property $F$ of type-$\tau$ entities has a least upper bound, the union of the hulls of its instances. Let $F$ be pinned down by $N\supseteq M_0$. For each instance $u$ of $F$ at the identity, its hull is the closure of $u$ under the arrows that $N$ does not separate from the identity, transported along the arrows agreeing with the identity on $N$; it is symmetric, pinned down by $N$ (by (B1), which splices an arrow agreeing with $h'$ on the instance's pinning set with $h$ on $N$), and an upper bound of $u$. Every upper bound $z$ of all the instances, pinned down by $N'$, contains every hull: given a member of a hull, (B2) supplies a symmetry fixing $N$ and moving the instance's pinning set off $N'$, whose image is again an instance (by the orbit lemma, Lemma 35), lying under $z$; and $z$, pinned down by $N'$, cannot tell the moved instance's tuple from the original. The union of the hulls is pinned down by $N$ and symmetric, so it is in the domain, and it is the least upper bound.

*Source: Boolean Completeness does not imply Rigid Comprehension, Theorem 36, p. 18; Corollary 37, p. 19. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#boolean-completeness`. It requires that There is a finite set $M_0$ of individuals at the evaluation object such that: (B1) for every finite $M\supseteq M_0$ and every arrow $h$ from the evaluation object to itself that $M$ does not separate (some arrow $k\notin G$ agrees with $h$ on $M$, or $h\in G$), every arrow $h'$ agreeing with $h$ on $M$, and finite $P,Q$ with $P\cap Q\subseteq M$, some arrow agrees with $h'$ on $P$ and with $h$ on $Q$; and (B2) for finite $N\supseteq M_0$ and finite $P,Q$, some member of the symmetry group fixes $N$ pointwise and moves every member of $P$ outside $N$ off $Q$. The arrows in (B1) go from the evaluation object to any one object, and $M$ separates $h$ when every arrow agreeing with $h$ on $M$ is a member of the symmetry group of the evaluation object. These are the hypotheses of Dorr's main theorem (draft, Definitions 28–30, Theorem 36). Here: With $M_0$ the fixed pair (the draft's argument for this model): splicing fails at that pair, but the pair is exactly what certifies invertibility, and the separated arrows are handled by symmetry instead; a symmetry may move points freely outside the pair. By Cian Dorr, 2026-09-19.*

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The draft's main theorem, which the all-surjections and collapse-pair models each applied in an argument of their own, stated once; what each member does to meet its hypotheses is its reason for meeting hull-conditions. Proved in Lean (SymBase.lub_of_hull).

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* No longer requires one-object-action-model: as the draft notes (proof of Proposition 40), nothing in the theorem uses a single object, pinning, separation, amalgamability and hulls all quantifying over arrows with a fixed target; the condition hull-conditions now says so.

### Holds Truth implies ND-necessity.

For a true $p$, $a\le p$, since $a$ entails every truth. Take $q:=a$ in the definition of $\Box_{\ne}p$: at a world in $a$, $p$ holds; at a world outside $a$, $\Diamond a$ fails. So every truth is $\Box_{\ne}$-necessary.

*General argument `arguments/dpc-isolated-actual-world`. It requires that The actual-world proposition $a$ is in the domain and entails every truth, and no world outside $a$ sees a world in $a$. Here: The actual-world proposition is the symmetry group, the set of arrows that are permutations, pinned down by the fixed pair; no composite with a non-bijective arrow is a permutation. By Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support, symmetric and full action models' copies (eight records) stated once for the topic; what varied, why no world outside the actual world sees back into it, is each record's reason for meeting actual-world-isolated.

### Fails Intensional Choice.

At type $e$. Let $F$ and $a$ be as the condition gives them, and suppose $G\le F$ is necessarily uniquely instantiated. $G$ is in the domain, so it is symmetric and pinned down by a finite set, which we may take to contain $a$; call it $N$. Let $h$ be the arrow the condition gives for $N$. Then $G_h=\{y\}$ for some $y$ in $F_h$. If $\sigma$ in the symmetry group fixes $p$, then $\sigma\circ h$ agrees with $h$ on $N$, so $G_{\sigma\circ h}=G_h$ by pinning, while symmetry gives $G_{\sigma\circ h}=\{\sigma y\}$. So no symmetry fixing $p$ moves $y$, and by the condition $y=p$. Each model's witness takes $F$ with $p$ outside its extension at $h$, a contradiction. $\Box$Intensional Choice fails with it, by T.

*General argument `arguments/intensional-choice-collapse`. It requires that A group $G$ acts on the individuals at the evaluation object, and every element of a relational domain there is symmetric, meaning that $\langle\bar x,h\rangle\in D$ implies $\langle g\cdot\bar x,g\circ h\rangle\in D$ whenever $g\in G$ and $g\circ h$ is an arrow, and is pinned down by a finite set of individuals, its extension at an arrow depending only on the arrow's values there. Here: The relational domains hold exactly the symmetric intensions pinned down by a finite set (Dorr, draft, Definitions 15–18). It requires that The individuals at the evaluation object are those the construction acts on, and the arrows act on them as the construction says. Here: The individuals are the base, acted on as the construction says. It requires that There are an individual $a$ and a necessarily instantiated property $F$ in the domain such that, for every finite set $N$ of individuals at the evaluation object, some arrow $h$ sends $N\cup\{a\}$ to a single individual $p$, and every individual $y\ne p$ in $F$'s extension at $h$ is moved by a member $\sigma$ of the symmetry group that fixes $p$, with $\sigma\circ h$ again an arrow. Here: Take $F:=\lambda x\, .\,x\ne a$, so $p\notin F_h$. $h$ is a surjection sending $N\cup\{a\}$ and both members of the pair to one $p$ outside the pair. Swapping the pair, or transposing $y$ with a point outside the pair, fixes $p$. By Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 2026-10-03.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Recorded from the collapse lemma deferred in extraction.md on 3 October until the model records' new format landed (not yet checked by a human). It needs the individuals the construction gives. Not covered: the qualitative-links model, whose arrows preserve a ternary relation and so cannot send everything to one point, and the qualitative-contrast model, whose arrows are bijections and where Intensional Choice holds.

*Revised 2026-10-04 by Claude Fable 5.1 (Anthropic), at Cian Dorr's direction:* Moved from the group symmetric-ideally-full to the topic, so that the symmetry-constrained full models use it too: in those models every intension is pinned down by the finite set of all individuals, and the collapses are the constant maps. The group's `when: individuals: base` is now the condition construction-individuals, met by that parameter value.

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: It has one object (Dorr, draft, §3.1: closed pure terms denote entities fixed by every arrow). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds No Contingency (signature Σ), B for sentences of Σ.

Each constant of Σ denotes what the closed pure term $\top_\tau$ of its type denotes, so a closed sentence of the language of Σ denotes what the pure sentence with $\top_\tau$ in place of each constant denotes; if true it is necessary by No Pure Contingency, which holds here. So No Contingency (signature Σ) holds, and B for sentences of Σ with it: a true Σ-sentence is necessary, hence necessarily possible.

*General argument `arguments/sigma-top-npc`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Cian Dorr (observation); recorded by Claude Opus 5.5 (Anthropic), 2026-10-02.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The argument sigma-single-top, for Σ a single constant of type $t$ denoting $\top$, stated for every interpretation of Σ by top elements, now that such interpretations have no individual constants. It replaces that argument and nc-sigma-homogeneous, which reached the same verdicts through an individual constant when the model's automorphisms carry every individual to every other. With an individual constant and no such automorphisms the verdicts were unknown in 19 models, and nowhere did the individual constants settle a verdict differently.


## Notes

This model is not a second witness to the draft's main result but a counterweight to it. Rigid Comprehension holds, so the failure of Actuality in the all-surjections model is no accident. Because Atomicity fails here, the model settles a question left open in Classicism: Rigid Comprehension does not imply Atomicity. The boxed forms of Actuality and Rigid Comprehension use the draft's one-object observation, which it states for Boolean Completeness and applies in the same way in its final section. The source is a work in progress. Everything that implies these fails with them.

## History

The record's revision log before it was written as arguments.

- **2026-09-23** (Claude Fable 5.1 (Anthropic), prompted by Cian Dorr) — Recorded the Distinctness-preserving collapse; see the notes. Now satisfies: Truth implies ND-necessity.
- **2026-09-23** (Claude Fable 5.1 (Anthropic), prompted by Cian Dorr) — Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes. Now violates: No Contingency (signature Σ), B for sentences of Σ.
- **2026-09-23** (Claude Fable 5.1 (Anthropic), prompted by Cian Dorr) — Corrected the reason given for the failures of Independence (signature Σ) and Distinctness (signature Σ): the true atom is denoted by no closed pure term, since such terms denote entities fixed by every arrow; the failures come from the other relational constants, which denote top. No verdict changes.
- **2026-09-23** (Claude Fable 5.1 (Anthropic), prompted by Cian Dorr) — Recorded the failure of Relational Choice, at types (e→t) and e: a functional subrelation of the serial relation pairing each property with its members would be symmetric and finitely pinned, and a symmetry fixing its pinning set would carry its choice for the property of lying outside that set to a second choice. Cian Dorr’s observation that a choice cannot be finitely pinned; argument in the notes. Now violates: Relational Choice.
- **2026-09-22** (Claude Fable 5.1 (Anthropic), prompted by Cian Dorr) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic), prompted by Cian Dorr) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the identity arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct, symmetric and pinned by that individual, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence symmetric and pinned by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, §3.1, p. 9 (base); Lemma 21, p. 10; Proposition 22, p. 11; Proposition 24, p. 13; Corollary 37 and Remark 38, p. 19.

<p class='cert'>Record: <code>topics/classicism/models/symmetric-collapse-pair.yaml</code></p>

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §3.1, p. 9; Lemma 21, p. 10; Proposition 22, p. 11; Proposition 24, p. 13; Corollary 37 and Remark 38, p. 19
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.2, pp. 23–26; Appendix D, pp. 73–79. The open question whether Rigid Comprehension implies Atomicity, and the ideally-full models of which this is the symmetric variant.
