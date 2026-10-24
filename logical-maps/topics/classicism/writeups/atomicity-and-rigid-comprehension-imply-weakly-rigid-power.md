# Atomicity and Rigid Comprehension imply Weakly Rigid Power

Proof by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026;
rewritten for the map by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr,
24 October 2026. It adapts the atom pullback of
[Atomicity and Rigid Comprehension imply Rigid Power](atomicity-and-rigid-comprehension-imply-rigid-power.html)
(Bacon's Lemma C.6) to weakly rigid relations.

**Theorem.** Let $\tau=\bar\sigma t$ be a relational type. In C, Rigid
Comprehension at $\tau$ and Atomicity at $\tau t$ imply Weakly Rigid Power at
$\tau$: if $F^\tau$ is weakly rigid, so is

$$
P:=\lambda Y^\tau\, .\,\operatorname{WeaklyRigid}(Y)\land Y\le F .
$$

Both premises are unboxed; Rigid Comprehension at $\tau t$ and BF are not used.

Recall (Background) that $Y\le Z$ is $\Box\forall\bar x\, .\,Y[\bar x]\to Z[\bar x]$,
that a weakly rigid relation is persistent, that rigidity is necessary weak
rigidity, and that an atom $W$ of a relational type is non-bottom and, for each
$\mathcal Y$ of its type, satisfies $W\le\mathcal Y$ or $W\le\neg\mathcal Y$.

**Lemma (Sun).** Coextensive weakly rigid relations are identical. If $A$ and $B$
are weakly rigid and coextensive, each instance of $A$ is an instance of $B$, hence
necessarily one; weak inextensibility of $A$ gives $A\le B$, and likewise
$B\le A$.

So under Rigid Comprehension at $\tau$, every weakly rigid $Y^\tau$ is identical to
its rigid coextension, and is rigid.

## Step 1: $P$ is weakly persistent

Let $PY$. Then $Y$ is rigid, so $\Box\operatorname{WeaklyRigid}(Y)$; and $Y\le F$
is necessary. So $\Box PY$.

## Step 2: pulling back an atom below $P$

Let $W^{\tau t}$ be an atom with $W\le P$. We find $X$ with

$$
PX\qquad\text{and}\qquad\Box\forall Y\, .\,WY\to Y=X .
\tag{1}
$$

By Rigid Comprehension at $\tau$, let $X$ be rigid and coextensive with

$$
Q:=\lambda\bar x\, .\,F[\bar x]\land\Box\forall Y\, .\,WY\to Y[\bar x].
$$

*(a) $PX$.* Each instance of $X$ is an instance of $F$, so necessarily one; weak
inextensibility of $X$ gives $X\le F$. As $X$ is rigid, $PX$.

*(b)* Each instance $\bar x$ of $X$ has $\Box\forall Y\, .\,WY\to Y[\bar x]$, so weak
inextensibility of $X$ gives

$$
\Box\forall Y\, .\,WY\to\forall\bar x\, .\,X[\bar x]\to Y[\bar x].
\tag{2}
$$

*(c)* Let $\bar x$ be an instance of $F$. If $X[\bar x]$, then $\Box X[\bar x]$. If not,
then $\neg Q[\bar x]$, so $W\not\le\lambda Y\, .\,Y[\bar x]$, and as $W$ is an atom,
$W\le\lambda Y\, .\,\neg Y[\bar x]$. Either way,

$$
\Box\forall Y\, .\,WY\to(Y[\bar x]\to X[\bar x]).
$$

Weak inextensibility of $F$, applied to
$\lambda\bar x\, .\,\forall Y\, .\,WY\to(Y[\bar x]\to X[\bar x])$, gives

$$
\Box\forall\bar x\, .\,F[\bar x]\to\forall Y\, .\,WY\to(Y[\bar x]\to X[\bar x]).
$$

Since $W\le P$, necessarily every $Y$ with $WY$ has $Y\le F$. Hence

$$
\Box\forall Y\, .\,WY\to\forall\bar x\, .\,Y[\bar x]\to X[\bar x].
\tag{3}
$$

*(d)* At any world, let $WY$. Then $PY$ there, so $Y$ is weakly rigid there; $X$ is
weakly rigid there, being rigid; and by (2) and (3) they are coextensive there. By
the Lemma, $Y=X$. This is (1). $\square$

Only the weak rigidity of $Y$ at the later world is used in (d), not its rigidity.
This is what the Rigid Power argument lacks, and what lets the conclusion be about
weakly rigid subrelations.

## Step 3: $P$ is weakly inextensible

Suppose

$$
\forall Y\, .\,PY\to\Box ZY,
$$

and suppose for contradiction that $P\not\le Z$, that is,
$\lambda Y\, .\,PY\land\neg ZY\ne\bot$. By Atomicity at $\tau t$ there is an atom
$W\le\lambda Y\, .\,PY\land\neg ZY$. Step 2 gives $X$ with $PX$, so $\Box ZX$, and
$\Box\forall Y\, .\,WY\to Y=X$. As $W\ne\bot$, possibly some $Y$ has $WY$; at such
a world $Y=X$ and $\neg ZY$, contradicting $\Box ZX$. So $P\le Z$. $\square$

Steps 1 and 3 show that $P$ is weakly rigid.

## Remarks

1. The premises used are Rigid Comprehension at $\tau$ and Atomicity at $\tau t$,
   including $\tau=t$.
2. Weakly Rigid Power implies Rigid Power, so this subsumes
   [Atomicity and Rigid Comprehension imply Rigid Power](atomicity-and-rigid-comprehension-imply-rigid-power.html)
   at the level of the schemata. That recorded implication uses Weakly Rigid Power
   at $\tau t$ to get Rigid Power at $\tau$, so the typed versions differ.
