# C5 and □Rigid Comprehension imply Second-Order Analytic Necessitism

The connection from □Plenitude is Zachary Goodsell's (23 October 2026); the proof is by Claude Fable 5.1
(Anthropic), prompted by Zachary Goodsell, after the S5 part of Corollary 5.1 of Andrew Bacon, *Could
the truths of mathematics have been different?* (draft of 9 October 2025). Informal, not Lean-verified.

**Setting.** C5 is C with □ND at every relational type. On the map it gives B and 5, ND at every type
(Prior), and BF at every type (necessary-nd-implies-bf); the write-up of c5-implies-necessity-of-arithmetic
lists the Lean proofs. Assume also □Rigid Comprehension: at every world, every relation is coextensive
with a rigid one. Fix a type $\sigma$ and $n\ge1$, and suppose
$\Diamond\exists\mathfrak R\operatorname{Real}_\sigma\mathfrak R$: at some world $w$ there is a real number
structure $\mathfrak R=(X,\le,+,\times,0,1,N)$. Everything below uses the Background's definitions of
$\operatorname{Rigid}$ (persistent and inextensible, each with its leading box) and of real number
structures.

**Lemma 1 (rigidity travels).** If $Y$ is rigid at $w$, it is rigid at the actual world. Rigidity is
$\Box\operatorname{WeaklyRigid}(Y)$, so at the actual world $\Diamond\Box\operatorname{WeaklyRigid}(Y)$,
and $\Diamond\Box p\to\Box p$ holds under 5 (and $\Diamond\Box p\to p$ under B). The same transfers any
necessary fact between $w$ and the actual world, in either direction.

**Lemma 2 (first-order facts).** For rigid relations with necessarily distinct instances, every
first-order fact with parameters from the instances is necessary if true and impossible if false: this
is Lemma 2 of the write-up of analytic-necessitism-implies-necessity-of-analysis, which uses only
persistence, inextensibility, the necessity of identity and necessary distinctness. ND gives the
necessary distinctness of all instances at every type.

**The rigidified structure.** At $w$, Rigid Comprehension gives rigid $Y_X$, $Y_\le$, $Y_+$, $Y_\times$,
$Y_N$ coextensive there with $X$, $\le$, $+$, $\times$, $N$, the relations taken to hold only of tuples
of instances of $X$, which Rigid Comprehension preserves by restricting first. Write
$\mathfrak Y=(Y_X,Y_\le,Y_+,Y_\times,0,1,Y_N)$. By Lemma 1 its relations are rigid at the actual world,
and by ND its instances are necessarily distinct; so $\operatorname{RigidStr}(\mathfrak Y)$.

**$\mathfrak Y$ is necessarily a real number structure.** The axioms of an ordered field with $0$, $1$,
and the clauses that $+$, $\times$ are functional on $Y_X$ and that $Y_N$ is the least subproperty of
$Y_X$ containing $0$ and closed under adding $1$, except for the leastness, are first-order facts about
$\mathfrak Y$; they hold at $w$, where $\mathfrak Y$ agrees with $\mathfrak R$, so by Lemma 2 they are
necessary. Leastness of $Y_N$ and completeness quantify over subproperties, and are handled at an
arbitrary world $u$ (accessible from the actual world, hence, under 5, from $w$ and seeing $w$). Let $F$
be a subproperty of $Y_X$ at $u$ with an upper bound in $Y_X$; let $F'$ be a rigid relation coextensive
with it at $u$ (Rigid Comprehension at $u$). "$F'$ has an upper bound in $Y_X$" is a first-order fact
about rigid relations, true at $u$, hence true at $w$ by Lemma 2 and Lemma 1; at $w$, $F'$ is
coextensive with a bounded subproperty of $X$, so by the completeness of $\mathfrak R$ it has a least
upper bound $s$ in $X=Y_X$ there, and "$s$ is the least upper bound of $F'$ in $(Y_X,Y_\le)$" is again a
first-order fact, true at $w$, hence at $u$. So $F$ has a least upper bound at $u$. Leastness of $Y_N$ is
the same argument with the inductive subproperties: an inductive $F$ at $u$ has a rigid coextension,
inductiveness and "contains $Y_N$" are first-order facts about rigid relations, and the latter holds at
$w$. Hence $\Box\operatorname{Real}_\sigma(\mathfrak Y)$.

**Represented powers.** For $k\le n$ let $\mathcal P_k$ be the property of rigid $k$-ary relations
holding only of tuples of instances of $Y_X$. Its instances are rigid by definition. It is persistent,
since both conjuncts are necessary if true (rigidity carries a box, and $S$ holding only of $Y_X$-tuples
is a first-order fact about rigid $S$ and $Y_X$). It is inextensible: given $G$ with
$\forall S(\mathcal P_kS\to\Box GS)$ at a world $u$, for every $S$ at $u$ either $\mathcal P_kS$, so
$\Box GS$, or $\neg\mathcal P_kS$, and then $\Box\neg\mathcal P_kS$, rigidity being non-contingent under
5 by Lemma 1 and the other conjunct by Lemma 2; so $\forall S\,\Box(\mathcal P_kS\to GS)$, and BF at the
type of $S$ gives $\Box\forall S(\mathcal P_kS\to GS)$, which is $\mathcal P_k\le G$. And necessarily every
$k$-ary relation $R$ agrees on $Y_X$-tuples with an instance: at any world, Rigid Comprehension gives a
rigid relation coextensive with $\lambda\bar x\, .\,R\bar x\land\bigwedge_iY_Xx_i$, which lies in
$\mathcal P_k$. So the instance of Second-Order Analytic Necessitism at $\sigma$ and $n$ holds. $\square$

**Remarks.** Atomicity is not used. Bacon's Corollary 5.1 derives the sentence-level Necessity of
Second-Order Analysis from the same premises through Theorem 5.2, whose proof uses the Leibniz
Biconditionals to show that a rigid real number structure stays complete at every accessible world;
under S5 the world $w$ of the given structure stays accessible, and completeness is read off there. The
rigid coextensions exist by □Rigid Comprehension, and 5 and BF do the rest, so □Plenitude, which gives
C5 and □Rigid Comprehension on the map, gives the conclusion.

## Paper references

- **Related: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Corollary 5.1; Appendix C.2. Bacon derives the Necessity of Second-Order Analysis from 5 and □Rigid Comprehension through the rigidity of the canonical reals and of their power, using the Leibniz Biconditionals to carry completeness to other worlds. Under S5 the original world stays accessible, so completeness need not be carried, and the conclusion is the entity-level principle at every type.
