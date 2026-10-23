# Analytic Necessitism implies the Necessity of Analysis

Composed by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026, after Theorem 7 of Neil Barton and Zachary
Goodsell, *Continuum Contingency* (draft of 14 October 2026), and Lemmas C.1 and C.3 of Andrew Bacon,
*Could the truths of mathematics have been different?* (draft of 9 October 2025). Informal, not
Lean-verified.

**Setting.** Work in C at a type $\sigma$, with the definitions of the Background's paragraph on
analysis. Fix an instance of the Necessity of Analysis: a first-order analytical sentence $A$, and the
disjunction
$\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to A(\mathfrak R'))\lor
\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to\neg A(\mathfrak R'))$.
If $\neg\Diamond\exists\mathfrak R'\operatorname{Real}_\sigma\mathfrak R'$, both disjuncts hold
vacuously. Otherwise Analytic Necessitism supplies $\mathfrak R=(X,\le,+,\times,0,1,N)$ with $X$,
$\le$, $+$, $\times$ and $N$ rigid, $\forall x\,y\in X(x\ne y\to\Box x\ne y)$, and
$\Box\operatorname{Real}_\sigma(\mathfrak R)$. Recall that $\operatorname{Rigid}(Y)$ is
$\operatorname{Persistent}(Y)\land\operatorname{Inextensible}(Y)$, where
$\operatorname{Persistent}(Y)$ is $\Box\forall\bar y(Y\bar y\to\Box Y\bar y)$ and
$\operatorname{Inextensible}(Y)$ is $\Box\forall Z((\forall\bar y\, .\,Y\bar y\to\Box Z\bar y)\to
Y\le Z)$, with $Y\le Z$ the necessary pointwise implication. Both are used at the actual world by T.

**Lemma 1 (atomic facts).** Let $S$ be one of $\le$, $+$, $\times$, $N$ and $\bar x$ a tuple of
instances of $X$ of the right length. Then $S\bar x\to\Box S\bar x$ and
$\neg S\bar x\to\Box\neg S\bar x$. Likewise $x=y\to\Box x=y$ and $x\ne y\to\Box x\ne y$ for
$x,y$ instances of $X$.

*Proof.* The first claim is persistence of $S$. For the second, suppose $\neg S\bar x$, and let
$Z:=\lambda\bar y\, .\,\bar y\ne\bar x$, where $\bar y\ne\bar x$ is the disjunction of the coordinatewise
distinctnesses. Every $\bar y$ with $S\bar y$ is a tuple of instances of $X$ (the relations of a real
number structure hold only of such tuples) differing from $\bar x$ in some coordinate, so
$\Box(\bar y\ne\bar x)$ by necessary distinctness of the instances of $X$. Hence
$\forall\bar y(S\bar y\to\Box Z\bar y)$, and inextensibility of $S$ gives $S\le Z$, that is
$\Box\forall\bar y(S\bar y\to\bar y\ne\bar x)$, which is $\Box\neg S\bar x$. For identity, the first
claim is the necessity of identity, a theorem of C, and the second is necessary distinctness. $\square$

The terms $0$ and $1$ denote fixed entities, so the lemma covers every atomic formula of the
first-order analytical language at parameters from $X$.

**Lemma 2 (formulas with parameters).** For every first-order analytical formula $\varphi(\bar v)$
and every tuple $\bar x$ of instances of $X$: $\varphi(\bar x)\to\Box\varphi(\bar x)$ and
$\neg\varphi(\bar x)\to\Box\neg\varphi(\bar x)$.

*Proof.* By induction on $\varphi$. Atomic formulas: Lemma 1. Negation, conjunction and
disjunction: if $\varphi$ and $\psi$ are each necessary if true and impossible if false, so are
$\neg\varphi$, $\varphi\land\psi$ and $\varphi\lor\psi$, by K; these are the steps nc_neg, nc_conj and
nc_disj of the Lean proof of c5-implies-necessity-of-arithmetic, derived in C. Universal quantifier
$\forall v\in X\, .\,\psi(v,\bar x)$: if it holds, then by the induction hypothesis
$\forall v(Xv\to\Box\psi(v,\bar x))$, and inextensibility of $X$ at $Z:=\lambda v\, .\,\psi(v,\bar x)$
gives $X\le Z$, that is $\Box\forall v(Xv\to\psi(v,\bar x))$. If it fails, some $v$ with $Xv$ has
$\neg\psi(v,\bar x)$; the induction hypothesis gives $\Box\neg\psi(v,\bar x)$ and persistence of $X$
gives $\Box Xv$, so $\Box\exists v(Xv\land\neg\psi(v,\bar x))$ by K, which is
$\Box\neg\forall v\in X\, .\,\psi(v,\bar x)$. $\square$

**Lemma 3 (categoricity).** $\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to
(A(\mathfrak R')\leftrightarrow A(\mathfrak R)))$.

*Proof.* Any two real number structures at $\sigma$ are isomorphic, and isomorphic structures agree on
every analytical sentence; both are theorems of the non-modal fragment of C (Bacon's Lemma C.3, after
Huntington), so their necessitations hold. Combine with $\Box\operatorname{Real}_\sigma(\mathfrak R)$
by K. $\square$

**Proof of the implication.** By Lemma 2 at the sentence $A$, either $\Box A(\mathfrak R)$ or
$\Box\neg A(\mathfrak R)$. In the first case Lemma 3 and K give
$\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to A(\mathfrak R'))$; in the second,
the disjunct with $\neg A$. $\square$

**Remarks.** The argument uses K, T and 4 only, the last two through the boxes that persistence and
inextensibility carry; neither B, BF, Rigid Comprehension nor any choice principle. The rigidity of
the relations is needed and not only that of $X$: Lemma 1 for $\le$, $+$, $\times$ and $N$ is where it
enters, and a rigid domain alone could carry a differently threaded field structure at another world.
Barton and Goodsell's Theorem 7 is the case in which $X$ is the property of rigid properties of
natural numbers, under Rigid Comprehension and their axiom of Infinity; the quantifier case is the
same, with their rigid restrictor replaced by the given structure's domain. The second-order case,
with the represented powers, is the write-up of
second-order-analytic-necessitism-implies-necessity-of-second-order-analysis.

## Paper references

- **Proof: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — §5.9, Theorem 7. The induction on analytical formulas, there for the reals as rigid properties of naturals under Rigid Comprehension; here the quantifier restrictor is the given rigid structure's domain.
- **Proof: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Appendix C.2, Lemma C.3; Appendix C.1, Lemma C.1. Huntington's theorem with the invariance of analytical sentences under isomorphism, which turns the non-contingency of the given structure's truths into the schema over all real number structures.
