# Relational Choice and Boolean Completeness imply Actuality

Proof by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026;
rewritten for the map by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr,
24 October 2026.

**Theorem.** In C, Relational Choice from $t$ to $t$ together with Boolean
Completeness at $t$ and at $tt$ implies Actuality. All premises are unboxed.

Since Boolean Completeness at $tt$ implies it at $t$ (Remark 2), the instances
used are $\mathrm{RC}_{t,t}$ and $\mathrm{BC}_{tt}$. Nothing else is assumed:
no ND, BF, Plenitude, or necessitated premise.

**Overview.** If Actuality fails, the false propositions have join $\top$
(Lemma 3). Relational Choice refines them into a family of pairwise disjoint
false propositions with the same join $\top$ (Lemma 4). But Boolean
Completeness at $tt$ guarantees that a pairwise disjoint family whose join is
true has a true member (Lemma 2).

## Notation

Throughout, $\le$ is $\le_t$, and $p<q$ means $p\le q\land p\ne q$. For a property
$A^{tt}$ of propositions, $\bigvee A$ is its least upper bound at $t$, which
Boolean Completeness at $t$ provides. For a proposition $a$, its haecceity is

$$
H_a:=\lambda z^t\, .\,z=a\qquad(\text{type }tt),
$$

and two propositions are *same or disjoint* when

$$
\operatorname{SameOrDisjoint}(x,y):=x=y\lor x\land y=\bot.
$$

A property $A^{tt}$ is *pairwise disjoint* when
$\forall a\,b\, .\,Aa\land Ab\to\operatorname{SameOrDisjoint}(a,b)$.

Recall that $p\le q$ is equivalent to $\Box(p\to q)$, and $X\le_{tt}Y$ to
$\Box\forall z\, .\,Xz\to Yz$ (Background). In particular $p\le q$ gives $p\to q$.

## Lemma 1: evaluation preserves joins

For $X^{tt}$ and propositions $x,c$:

$$
X\le_{tt}\lambda z\, .\,(z=x\to c)\quad\text{iff}\quad Xx\le c.
$$

Indeed the left side is $\Box\forall z\, .\,Xz\to(z=x\to c)$, the right side
is $\Box(Xx\to c)$, and $\forall z\, .\,(Xz\to(z=x\to c))\leftrightarrow(Xx\to c)$
is a theorem of C, so its necessitation holds.

Consequently, if $J$ is the least upper bound at $tt$ of a property
$\mathcal A^{(tt)t}$, then for all $x,c$:

$$
Jx\le c\quad\text{iff}\quad\forall Y\, .\,\mathcal AY\to Yx\le c.
$$

For $Jx\le c$ iff $J\le_{tt}\lambda z\, .\,(z=x\to c)$ iff every $Y$ in $\mathcal A$
has $Y\le_{tt}\lambda z\, .\,(z=x\to c)$ iff every $Y$ in $\mathcal A$ has $Yx\le c$.

## Lemma 2: a pairwise disjoint family with a true join has a true member

*Assume Boolean Completeness at $t$ and $tt$.* Let $A^{tt}$ be pairwise
disjoint, with every member false. Then $\bigvee A$ is false.

*Proof.* Suppose $\bigvee A$ is true. Let $J$ be the least upper bound at $tt$ of
the haecceities of members of $A$,

$$
\mathcal A:=\lambda Y^{tt}\, .\,\exists a\, .\,Aa\land Y=H_a .
$$

**Step 1.** For all propositions $x,y$:

$$
Jx\land Jy\le\operatorname{SameOrDisjoint}(x,y). \tag{1}
$$

Let $a,b$ be members of $A$. Then $\operatorname{SameOrDisjoint}(a,b)$, and as a
disjunction of identities it is necessary. Since
$x=a\land y=b\land\operatorname{SameOrDisjoint}(a,b)\to\operatorname{SameOrDisjoint}(x,y)$
is a theorem of C, its necessitation gives the first line of

$$
\begin{aligned}
H_ax\land H_by&\le\operatorname{SameOrDisjoint}(x,y),\\
H_by&\le H_ax\to\operatorname{SameOrDisjoint}(x,y)&&\text{for all }b\text{ in }A,\\
Jy&\le H_ax\to\operatorname{SameOrDisjoint}(x,y)&&\text{by Lemma 1},\\
H_ax&\le Jy\to\operatorname{SameOrDisjoint}(x,y)&&\text{for all }a\text{ in }A,\\
Jx&\le Jy\to\operatorname{SameOrDisjoint}(x,y)&&\text{by Lemma 1},
\end{aligned}
$$

which is (1).

**Step 2.** For each member $a$ of $A$, $H_a\le_{tt}J$ and $H_aa=(a=a)=\top$, so
$Ja=\top$.

**Step 3.** Put $v:=\forall p\, .\,Jp\to\neg p$. For each member $a$ of $A$,

$$
v\le(Ja\to\neg a)=\neg a,\qquad\text{so}\qquad a\le\neg v .
$$

Hence $\bigvee A\le\neg v$. As $\bigvee A$ is true, $v$ is false, so there is a
proposition $q$ with

$$
Jq\land q .
$$

**Step 4.** Let $a$ be a member of $A$. Then $q\ne a$, since $q$ is true and $a$
is false. By (1) and Step 2, $\operatorname{SameOrDisjoint}(q,a)$, so
$q\land a=\bot$ and $a\le\neg q$. Hence $\bigvee A\le\neg q$, and $\bigvee A$ is
false since $q$ is true: a contradiction. $\square$

Equivalently, for any pairwise disjoint $A^{tt}$, $\bigvee A$ is true iff some
member of $A$ is true. Relational Choice is not used.

## Lemma 3: without Actuality, the false propositions have join $\top$

*Assume Boolean Completeness at $t$.* Let $k:=\bigvee\lambda p\, .\,\neg p$.

- If $k$ is false, then $\neg k$ witnesses Actuality: $\neg k$ is true, and for
  each true $q$, $\neg q$ is false, so $\neg q\le k$ and $\neg k\le q$.
- If $k$ is true, then $\neg k$ is false, so $\neg k\le k$, hence
  $\neg k=\neg k\land k=\bot$ and $k=\top$.

So if Actuality fails, $k=\top$.

## Lemma 4: disjoint refinement

*Assume Relational Choice from $t$ to $t$ and Boolean Completeness at $t$.* Let
$X^{tt}$ and $j:=\bigvee X$. There is a pairwise disjoint $\Delta^{tt}$ such that

- (i) each member of $\Delta$ lies below some member of $X$, and
- (ii) $\bigvee\Delta=j$.

*Proof.* Let $U^{ttt}$ be

$$
(Ub)x:=\bigl(b<j\to Xx\land x\not\le b\bigr)\land\bigl(\neg\,b<j\to x=\bot\bigr).
$$

$U$ is serial: if $b<j$, some member $x$ of $X$ has $x\not\le b$, since otherwise
$b$ would be an upper bound of $X$ and $j\le b$. By Relational Choice there is a
functional $S$ with $\forall b\,x\, .\,(Sb)x\to(Ub)x$; write $s(b)$ for the unique $x$ with $(Sb)x$, and let

$$
(Gb)c:=\exists x\, .\,(Sb)x\land c=b\lor x,\qquad g(b):=b\lor s(b).
$$

Apply the Bourbaki–Witt lemma (Background, *General lemmas*) at type $t$ with
the property $I:=\lambda b\, .\,b\le j$, the order $\le$, and the function $G$:

- $\le$ partially orders $I$;
- a chain $Z\subseteq I$ has supremum $\bigvee Z$ in $I$, because $j$ bounds $Z$;
- $g$ maps $I$ into $I$ and $b\le g(b)$: if $b<j$ then $s(b)$ is in $X$, so
  $s(b)\le j$; and $g(j)=j\lor\bot=j$.

Moreover $g(b)\ne b$ when $b<j$, since $s(b)\not\le b$. Let $M$ be the tower.
By the lemma, $M$ is a chain; if $b<c$ in $M$ then $g(b)\le c$; and the supremum
$m$ of $M$ is in $M$ with $g(m)=m$, so $m=j$ and $Mj$.

For $b$ in $M$ with $b<j$, the *increment* at $b$ is $g(b)\land\neg b$. Let

$$
\Delta:=\lambda d\, .\,\exists b\, .\,Mb\land b<j\land d=g(b)\land\neg b .
$$

*Pairwise disjoint.* Let $b<c$ be in $M$, both below $j$. Then

$$
(g(b)\land\neg b)\land(g(c)\land\neg c)\le g(b)\land\neg c\le c\land\neg c=\bot .
$$

Since $M$ is a chain, the increments at distinct members of $M$ are disjoint.

*(i).* $g(b)\land\neg b=(b\lor s(b))\land\neg b=s(b)\land\neg b\le s(b)$, and
$s(b)$ is in $X$.

*(ii).* Every increment is below $g(b)\le j$. Let $k$ be any upper bound of
$\Delta$. The property $\lambda b\, .\,Mb\land b\le k$ is closed:

- if $b<j$ and $b\le k$ then $g(b)=b\lor(g(b)\land\neg b)\le k$; and $g(j)=j$;
- the supremum of a chain of propositions below $k$ is below $k$.

So every member of $M$ is below $k$, in particular $j\le k$. Thus $j=\bigvee\Delta$.
$\square$

## Proof of the theorem

Suppose Actuality fails. By Lemma 3, $X:=\lambda p\, .\,\neg p$ has $\bigvee X=\top$.
Let $\Delta$ be as in Lemma 4. Each member of $\Delta$ lies below a false
proposition and so is false; $\Delta$ is pairwise disjoint; and
$\bigvee\Delta=\top$ is true. This contradicts Lemma 2. $\square$

## Remarks

1. **Transversal Choice.** With the recorded results that
   [Actuality implies Transversal](actuality-implies-transversal.html) and that
   [Transversal and Relational Choice imply Transversal Choice](transversal-and-relational-choice-imply-transversal-choice.html),
   this settles the conjecture that Relational Choice and
   Boolean Completeness imply Transversal Choice. Astra also gave a direct proof of
   that conjecture, adapting Bourbaki–Witt to partial transversals, which needs
   Relational Choice from $\sigma t$ to $\sigma$ and suprema of represented chains
   at $\sigma t$.

2. **Boolean Completeness at $tt$ gives it at $t$.** For $A^{tt}$, let $J$ be the
   least upper bound at $tt$ of the constant properties
   $\lambda z\, .\,p$ with $Ap$. By Lemma 1, $J\top\le c$ iff $p\le c$ for every
   member $p$ of $A$, so $J\top=\bigvee A$.

3. **Where the higher type is used.** Lemma 4 needs only Boolean Completeness at
   $t$. The type-$tt$ instance is used only in Lemma 2, for the join of the
   haecceities. The argument does not show that Relational Choice and Boolean
   Completeness at $t$ alone imply Actuality.

4. **The boxed form.** The theorem is a theorem of C with its premises discharged,
   so necessitating it gives □Relational Choice and □Boolean Completeness imply
   □Actuality. The unboxed premises do not give □Actuality: the model
   [Full Boolean-valued model: one atom and an atomless component](full-boolean-valued-atom-and-atomless.html)
   separates them.
