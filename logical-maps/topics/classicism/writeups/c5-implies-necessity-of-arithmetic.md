# C5 ⇒ Necessity of Arithmetic

Theorem 4.4 of Andrew Bacon, *Could the truths of mathematics have been different?* (draft of
9 October 2025, p. 19; proved as Theorem C.1 in Appendix C.1, pp. 10–11 of the separately paginated
appendix, through Proposition C.2 and Lemma C.1), transposed to the map's formulation of the
Necessity of Arithmetic, which follows Goodsell (Background). Transposition by Claude Fable 5.1
(Anthropic), 19 October 2026. Lean-verified the same day: the steps below are derived shallow
theorems (`lean/Classicism/Results/SentenceSchemas/Arithmetic.lean`), and the induction on
arithmetical sentences composes their derivations (`ArithmeticMeta.lean`,
`c5_entails_necessityOfArithmetic`; certificate `Classicism.Map.c5_implies_necessity_of_arithmetic`).

Bacon's logic $\mathrm H\Box.5$ is his background logic with T, 4 and B necessitated. C5, which is
C with □ND at every type, contains it: □ND gives □5, hence □B (recorded), BF at every type
(necessary-nd-implies-bf) and ND at every type. His theorem concerns first-order arithmetic over
natural-number structures of individuals, and its proof passes through the canonical structure of
numerical quantifiers, which he shows rigid in S5 (Proposition C.2) before an induction on
sentences (Lemma C.1). The map's arithmetical sentences are already about the canonical structure,
the finite cardinalities $\mathbb N_\sigma$ of properties of a type $\sigma$, with
$\operatorname{Sum}_\sigma$ and $\operatorname{Prod}_\sigma$ defined by recursion, so the argument
below runs his Proposition C.2 and Lemma C.1 directly on it. It proves more than the recorded
principle: in C5 every arithmetical sentence is necessary or impossible outright, with no
antecedent $I_\sigma$.

Fix $\sigma$ and drop the subscripts; write $n^+$ for $\operatorname{Suc}n$ and $\nu$ for
$(\sigma t)t$. A term is a variable of type $\nu$, $\mathbf 0$, or the successor of a term; when
the variables of a term take numbers as values so does the term, since
$\mathbb Nn\to\mathbb Nn^+$ is a theorem of C. Besides theorems of C (T, 4, K, NI, CBF), the
argument uses ND at type $\nu$, the dual of B ($\Diamond\Box p\to p$) and BF at type $\nu$, all at
the evaluation point, and all supplied by C5.

**Lemma 1 (numbers are necessarily numbers; C).** $\forall n\,.\,\mathbb Nn\to\Box\mathbb Nn$. By
the definition of $\mathbb N$ with the property $\lambda n\,.\,\Box\mathbb Nn$: $\Box\mathbb N\mathbf 0$
since $\mathbb N\mathbf 0$ is a theorem, and $\Box\mathbb Nn\to\Box\mathbb Nn^+$ by K from the
necessitated theorem $\mathbb Nn\to\mathbb Nn^+$. (Lemma 3 of the write-up for
countable-boolean-completeness-implies-necessity-of-arithmetic.)

**Lemma 2 (non-numbers are necessarily non-numbers; C5).**
$\forall n\,.\,\neg\mathbb Nn\to\Box\neg\mathbb Nn$. Contrapose: if $\Diamond\mathbb Nn$, then
$\Diamond\Box\mathbb Nn$ by the necessitation of Lemma 1 and K, so $\mathbb Nn$ by the dual of B.

**Lemma 3 (sums and products are necessary when true; C).** For numbers $m,n,o$:
$\operatorname{Sum}(m,n,o)\to\Box\operatorname{Sum}(m,n,o)$ and
$\operatorname{Prod}(m,n,o)\to\Box\operatorname{Prod}(m,n,o)$. For $\operatorname{Sum}$, instantiate
its definition at $R:=\lambda i\,j\,.\,\Box\operatorname{Sum}(m,i,j)$. $R\mathbf 0m$ holds, since
$\operatorname{Sum}(m,\mathbf 0,m)$ is a theorem of C (the consequent of its definition is its own
antecedent) and so necessary. $R$ is closed under the recursion on numbers: for numbers $i,j$,
$\operatorname{Sum}(m,i,j)\to\operatorname{Sum}(m,i^+,j^+)$ is a theorem of C, since any $R'$ with
$R'\mathbf 0m$ that is closed under the recursion has $R'ij$ and hence $R'i^+j^+$; necessitating
it and using Lemma 1 for $i$ and $j$, $\Box\operatorname{Sum}(m,i,j)\to\Box\operatorname{Sum}(m,i^+,j^+)$.
So $\operatorname{Sum}(m,n,o)$ gives $Rno$. For $\operatorname{Prod}$, instantiate at
$R:=\lambda i\,j\,.\,\Box\operatorname{Prod}(m,i,j)$: $R\mathbf 0\mathbf 0$ since
$\operatorname{Prod}(m,\mathbf 0,\mathbf 0)$ is a theorem; and for numbers $i,j,k$,
$\operatorname{Prod}(m,i,j)\to\operatorname{Sum}(m,j,k)\to\operatorname{Prod}(m,i^+,k)$ is a theorem,
so with Lemma 1 and the case of $\operatorname{Sum}$,
$\Box\operatorname{Prod}(m,i,j)\to\operatorname{Sum}(m,j,k)\to\Box\operatorname{Prod}(m,i^+,k)$, which
is the recursion clause for $R$.

**Lemma 4 (sums and products are impossible when false; C5).** For numbers $m,n,o$:
$\neg\operatorname{Sum}(m,n,o)\to\Box\neg\operatorname{Sum}(m,n,o)$, and likewise for
$\operatorname{Prod}$. Contrapose: $\Diamond\operatorname{Sum}(m,n,o)$ gives
$\Diamond\Box\operatorname{Sum}(m,n,o)$ by the necessitation of Lemma 3, whose hypotheses
$\mathbb Nm$, $\mathbb Nn$, $\mathbb No$ are necessary by Lemma 1, and then
$\operatorname{Sum}(m,n,o)$ by the dual of B.

**Lemma 5 (identities).** For any $m,n$ of type $\nu$: $m=n\to\Box\,m=n$ (NI) and
$m\ne n\to\Box\,m\ne n$ (ND at $\nu$).

**Lemma 6 (arithmetical formulas are non-contingent on numbers; C5).** For every arithmetical
formula $A$ with free variables $\bar v$:
$\forall\bar v\in\mathbb N\,.\,(A\to\Box A)\land(\neg A\to\Box\neg A)$. By induction on $A$, for all
values of $\bar v$ in $\mathbb N$ at once. Atomic formulas: $\mathbb N\mathbf t$ by Lemmas 1 and 2;
$\operatorname{Sum}(\mathbf m,\mathbf n,\mathbf o)$ and $\operatorname{Prod}(\mathbf m,\mathbf n,\mathbf o)$
by Lemmas 3 and 4, the values of the terms being numbers; and $\mathbf m=\mathbf n$ by Lemma 5.
Negation is immediate; for $A\land B$, $\Box A\land\Box B$ gives $\Box(A\land B)$, and $\Box\neg A$
or $\Box\neg B$ gives $\Box\neg(A\land B)$, by K; disjunction likewise. For
$\forall v\in\mathbb N\,.\,A$: if it holds, then for every $v$, either $\mathbb Nv$ and $\Box A$ by
the hypothesis, or $\neg\mathbb Nv$ and $\Box\neg\mathbb Nv$ by Lemma 2; either way
$\Box(\mathbb Nv\to A)$, so $\forall v\,.\,\Box(\mathbb Nv\to A)$, and BF at $\nu$ gives
$\Box\forall v\,.\,\mathbb Nv\to A$. If it fails, some number $v$ has $\neg A$, so $\Box\neg A$ by
the hypothesis and $\Box\mathbb Nv$ by Lemma 1, whence $\Box\exists v\,.\,\mathbb Nv\land\neg A$ by
K. The existential quantifier is the dual.

**Theorem.** For every arithmetical sentence $A$ at $\sigma$, $\Box A\lor\Box\neg A$ in C5, and so
$\Box(I_\sigma\to A)\lor\Box(I_\sigma\to\neg A)$. The first is Lemma 6 for a sentence; the second
follows by K. $\blacksquare$

## Remarks

- Beyond C the argument uses only the dual of B (Lemmas 2 and 4), ND at $\nu$ (Lemma 5) and BF at
  $\nu$ (the quantifier step), all at the evaluation point. Bacon states the theorem for
  $\mathrm H\Box.5$, without Intensionality; it is recorded with the preset C5, the map's name for
  that logic over C.
- Bacon's Theorem 4.3 shows that the result fails in second-order modal logic with S5, where the
  numerical quantifiers need not be rigid; the higher-order comprehension behind Lemma 1, the
  property $\lambda n\,.\,\Box\mathbb Nn$ of cardinalities, is what makes the difference.
