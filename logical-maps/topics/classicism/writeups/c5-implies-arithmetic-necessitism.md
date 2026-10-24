# C5 implies Arithmetic Necessitism

Proof by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 23 October 2026;
written out for the map by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr,
24 October 2026.

**Theorem.** In C, □ND (at every type) implies Arithmetic Necessitism at every
type $\sigma$, including $e$:

$$
\operatorname{Rigid}(\mathbb N_\sigma)\land\forall m\,n\in\mathbb N_\sigma\, .\,m\ne n\to\Box\,m\ne n .
$$

The antecedent $\Box I^*_\sigma$ of the principle is not needed. Write $\mathbb N$ for
$\mathbb N_\sigma$, $\mathbf 0$ for $\mathbf 0_\sigma$ and $\operatorname{Suc}$ for
$\operatorname{Suc}_\sigma$ (Background).

**Facts used.** ND at $t$ implies 5 and hence B,
$\forall p\, .\,p\to\Box\Diamond p$ (*Classicism*, Proposition 2.2), and □ND implies BF at
every type (*Classicism*, Proposition 2.3). Both conclusions are necessary, since □ND
is.

## Step 1: $\mathbb N$ is persistent

$\mathbb N\mathbf 0$ is a theorem of C, so $\Box\mathbb N\mathbf 0$. And
$\forall n\, .\,\mathbb Nn\to\mathbb N(\operatorname{Suc}n)$ is a theorem of C, so
$\forall n\, .\,\Box\mathbb Nn\to\Box\mathbb N(\operatorname{Suc}n)$. So
$\lambda n\, .\,\Box\mathbb Nn$ holds of $\mathbf 0$ and is closed under successor, and
since $\mathbb N$ is the least such property (the definition of
$\operatorname{FiniteCardinality}$),

$$
\forall n\, .\,\mathbb Nn\to\Box\mathbb Nn .
$$

This is a theorem of C, so it is necessary: $\mathbb N$ is persistent.

## Step 2: $\mathbb N$ is inextensible

By B and persistence, a non-number is necessarily a non-number:
$\neg\mathbb Nn\to\Box\neg\mathbb Nn$. For if $\Diamond\mathbb Nn$ then
$\Diamond\Box\mathbb Nn$, and B gives $\mathbb Nn$.

Now suppose $\forall n\, .\,\mathbb Nn\to\Box Xn$. Then

$$
\forall n\, .\,\Box(\mathbb Nn\to Xn),
$$

from $\Box Xn$ if $\mathbb Nn$, and from $\Box\neg\mathbb Nn$ otherwise. BF gives
$\Box\forall n\, .\,\mathbb Nn\to Xn$, that is, $\mathbb N\le X$. So $\mathbb N$ is weakly
inextensible. The argument uses only B, BF and Step 1, which hold necessarily, so it
can be carried out at every world: $\mathbb N$ is inextensible, and with Step 1, rigid.

## Step 3: necessary distinctness

ND at the type $(\sigma t)t$ of cardinalities gives $m\ne n\to\Box\,m\ne n$ for all
$m,n$, in particular for numbers. $\square$

Rigid Comprehension is not used. The recorded proof from □Rigid Comprehension
([□Rigid Comprehension implies Arithmetic Necessitism](necessary-rigid-comprehension-implies-arithmetic-necessitism.html),
Barton and Goodsell's Theorem 3) needs no ND.
