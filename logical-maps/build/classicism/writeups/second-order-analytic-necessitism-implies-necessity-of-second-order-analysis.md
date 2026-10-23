# Second-Order Analytic Necessitism implies the Necessity of Second-Order Analysis

Composed by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026, extending the write-up of
analytic-necessitism-implies-necessity-of-analysis, after Theorem 7 of Neil Barton and Zachary Goodsell,
*Continuum Contingency* (draft of 14 October 2026), with Proposition C.3 and Lemma C.3 of Andrew Bacon,
*Could the truths of mathematics have been different?* (draft of 9 October 2025). Informal, not
Lean-verified.

**Setting.** Work in C at a type $\sigma$. Fix a second-order analytical sentence $A$ and let $n$ be
the largest arity of a relation variable in it. If no real number structure at $\sigma$ is possible,
the instance holds vacuously. Otherwise the instance of Second-Order Analytic Necessitism for $n$
supplies a rigid real number structure $\mathfrak R=(X,\le,+,\times,0,1,N)$ with necessarily distinct
elements, $\Box\operatorname{Real}_\sigma(\mathfrak R)$, and for each $k\le n$ a represented power
$\mathcal P_k$: a rigid property of rigid $k$-ary relations holding only of tuples of instances of $X$,
such that $\Box\forall R\,\exists S(\mathcal P_kS\land\forall\bar x\in X(S\bar x\leftrightarrow R\bar x))$.

**Lemma 1′ (atomic facts).** Lemma 1 of the first-order write-up holds also for $S$ an instance of
some $\mathcal P_k$: $S\bar x\to\Box S\bar x$ and $\neg S\bar x\to\Box\neg S\bar x$ for $\bar x$ from
$X$. The proof is the same, $S$ being rigid and holding only of tuples of instances of $X$, which are
necessarily distinct from $\bar x$ when distinct from it.

**Lemma 2′ (formulas with parameters).** For every second-order analytical formula
$\varphi(\bar v,\bar V)$, every tuple $\bar x$ of instances of $X$ and every tuple $\bar S$ of
instances of the $\mathcal P_k$ of the arities of $\bar V$: $\varphi(\bar x,\bar S)\to
\Box\varphi(\bar x,\bar S)$ and $\neg\varphi(\bar x,\bar S)\to\Box\neg\varphi(\bar x,\bar S)$.

*Proof.* Induction on $\varphi$. The atomic, connective and first-order quantifier cases are those of
the first-order write-up, with Lemma 1′ for the atomic formulas $V\bar x$. For a relation quantifier
$\forall R\,\psi(R,\bar x,\bar S)$ of arity $k$, first note that necessarily
$\forall R\,\psi(R,\bar x,\bar S)\leftrightarrow\forall R(\mathcal P_kR\to\psi(R,\bar x,\bar S))$. The
left-to-right direction is trivial. For the converse, at any world, a relation $R$ agrees on tuples of
instances of $X$ with some instance $S$ of $\mathcal P_k$, by the representation clause, and
$\psi(S,\bar x,\bar S)\to\psi(R,\bar x,\bar S)$ because an analytical formula applies its relation
variables only to terms denoting instances of $X$ (its first-order variables are restricted to $X$ and
$0,1$ are instances of $X$), so it cannot distinguish relations agreeing on such tuples: this is
Bacon's Proposition C.3, Analytic Extensionality, a theorem schema of the non-modal fragment, whose
necessitation holds. It therefore suffices to show that
$\forall R(\mathcal P_kR\to\psi(R,\bar x,\bar S))$ is necessary if true and impossible if false, and this
is the first-order quantifier case with $\mathcal P_k$ as restrictor: if it holds, each instance $S$ of
$\mathcal P_k$ has $\psi(S,\bar x,\bar S)$, hence $\Box\psi(S,\bar x,\bar S)$ by the induction hypothesis
(the parameters $S,\bar S$ being instances of the $\mathcal P$'s), and inextensibility of $\mathcal P_k$
at $\lambda R\, .\,\psi(R,\bar x,\bar S)$ gives $\Box\forall R(\mathcal P_kR\to\psi(R,\bar x,\bar S))$;
if it fails, some instance $S$ has $\neg\psi(S,\bar x,\bar S)$, so $\Box\neg\psi(S,\bar x,\bar S)$ by the
induction hypothesis and $\Box\mathcal P_kS$ by persistence, whence the negation is necessary by K.
$\square$

**Lemma 3′ (categoricity).** $\Box\forall\mathfrak R'(\operatorname{Real}_\sigma\mathfrak R'\to
(A(\mathfrak R')\leftrightarrow A(\mathfrak R)))$: Huntington's theorem, and the invariance of
second-order analytical sentences under isomorphism, since an isomorphism between structures at the
same type transports relations by λ-abstraction (Bacon's Lemma C.3); both theorems of the non-modal
fragment, necessitated.

**Proof of the implication.** As in the first-order case: Lemma 2′ at $A$ gives $\Box A(\mathfrak R)$
or $\Box\neg A(\mathfrak R)$, and Lemma 3′ turns either into the corresponding disjunct of the
instance. $\square$

**Remarks.** The represented powers enter only through the relation quantifiers, where the
representation clause makes the restricted and unrestricted quantifiers necessarily equivalent and
the rigidity of $\mathcal P_k$ makes the restricted one non-contingent. Under Rigid Comprehension the
rigid relations holding only of $X$-tuples represent every relation, and Barton and Goodsell's
Second-Order Continuum Necessitism, that the property of rigid properties of reals is rigid, is the
arity-one represented power of the reals; relations of higher arity reduce to properties there by
pairing. The continuum hypothesis is a second-order analytical sentence, so the Non-contingency of the
Continuum Hypothesis follows (necessity-of-second-order-analysis-implies-non-contingency-of-ch).

## Paper references

- **Proof: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — §5.9, Theorem 7
- **Proof: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Appendix C.2, Proposition C.3 and Lemma C.3. Analytical formulas do not distinguish relations that agree on the structure's elements, which lets the represented powers stand in for all relations; and categoricity across structures.
