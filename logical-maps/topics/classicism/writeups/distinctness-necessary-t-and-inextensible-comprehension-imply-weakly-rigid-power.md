# ND (type t) and Inextensible Comprehension imply Weakly Rigid Power

Proof by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026;
rewritten for the map by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr,
24 October 2026.

**Theorem.** Let $\tau=\bar\sigma t$ be a relational type. In C, ND at $t$ and
Inextensible Comprehension at $\tau t$ imply Weakly Rigid Power at $\tau$: if
$F^\tau$ is weakly rigid, so is

$$
P_F:=\lambda Y^\tau\, .\,\operatorname{WeaklyRigid}(Y)\land Y\le F .
$$

Both premises are unboxed. BF, Atomicity, Boolean Completeness and Rigid
Comprehension are not used.

**Overview.** ND at $t$ makes weakly rigid relations *necessarily separated*:
instances that are distinct anywhere are necessarily distinct (Lemma 3). A separated
persistent relation with an inextensible coextension is rigid (Lemma 2). Using this,
$F$ is rigid, and so is $R_F:=\lambda Y\, .\,\operatorname{Rigid}(Y)\land Y\le F$
(Lemma 5). Finally, separation of $F$ makes every weakly rigid subrelation of $F$, at
any world, rigid there (Lemma 6), so $P_F=R_F$.

## Notation

Recall (Background) that $Y\le Z$ is $\Box\forall\bar x\, .\,Y[\bar x]\to Z[\bar x]$,
that $\operatorname{Inextensible}$ and $\operatorname{Rigid}$ are the necessitations of
weak inextensibility and weak rigidity, and that a weakly rigid relation is
persistent. Put

$$
\operatorname{NecSeparated}(A):=\Box\forall\bar a\,\bar b\, .\,
A[\bar a]\land A[\bar b]\land\bar a\ne\bar b\to\Box(\bar a\ne\bar b),
$$

and for a tuple $\bar a$ let $\delta_{\bar a}:=\lambda\bar b\, .\,\bar b=\bar a$ be its
haecceity. Haecceities are rigid in C.

## Lemma 1: two consequences of ND at $t$

*Assume ND at $t$.*

(a) For entities $a,b$ of any type, $a\ne b\to\Box(a\ne b)$. For if $a\ne b$, then
$(a=b)\ne\top$, so $\Box((a=b)\ne\top)$; and $a=b$ at some world would give
$\Box(a=b)$, that is $(a=b)=\top$, there.

(b) If $\Box(q\to\Box q)$ and $\neg q$, then $\Box\neg q$. For $q\ne\top$, so
$\Box(q\ne\top)$, that is $\Box\neg\Box q$; with $\Box(q\to\Box q)$ this gives
$\Box\neg q$.

## Lemma 2: separated persistent relations with an inextensible coextension are rigid

*Assume ND at $t$.* Let $A$ be persistent with $\operatorname{NecSeparated}(A)$, and
let $G$ be inextensible and coextensive with $A$. Then $A=G$, so $A$ is rigid.

*Proof.* Each instance of $G$ is an instance of $A$, hence necessarily one; weak
inextensibility of $G$ gives $G\le A$.

Let $q:=\exists\bar a\, .\,A[\bar a]\land\neg G[\bar a]$. We show
$\Box(q\to\Box q)$. At any world, let $A[\bar a]\land\neg G[\bar a]$. Each instance
$\bar b$ of $G$ there is an instance of $A$ with $\bar b\ne\bar a$, so
$\Box(\bar b\ne\bar a)$. Weak inextensibility of $G$ there gives
$G\le\lambda\bar b\, .\,\bar b\ne\bar a$, so $\Box\neg G[\bar a]$; and
$\Box A[\bar a]$ by persistence. So $\Box q$.

As $A$ and $G$ are coextensive, $\neg q$. By Lemma 1(b), $\Box\neg q$, which says
$A\le G$. $\square$

## Lemma 3: weakly rigid relations are necessarily separated

*Assume ND at $t$.* If $A$ is weakly rigid, then $\operatorname{NecSeparated}(A)$.

*Proof.* First, the product $K:=\lambda\bar a\,\bar b\, .\,A[\bar a]\land A[\bar b]$ is
weakly rigid. Weak persistence is clear. For weak inextensibility, suppose

$$
\forall\bar a\,\bar b\, .\,A[\bar a]\land A[\bar b]\to\Box Z[\bar a,\bar b].
$$

For each instance $\bar a$ of $A$, weak inextensibility of $A$ applied to
$\lambda\bar b\, .\,Z[\bar a,\bar b]$ gives
$\Box\forall\bar b\, .\,A[\bar b]\to Z[\bar a,\bar b]$. Weak inextensibility of $A$
applied to $\lambda\bar a\, .\,\forall\bar b\, .\,A[\bar b]\to Z[\bar a,\bar b]$ then gives
$K\le Z$.

Now let

$$
\operatorname{Settled}(\bar a,\bar b):=\Box(\bar a=\bar b)\lor\Box(\bar a\ne\bar b).
$$

Every pair of instances of $A$ satisfies it, by necessity of identity and Lemma 1(a),
and so necessarily satisfies it, by 4. Weak inextensibility of $K$ gives
$K\le\operatorname{Settled}$. At any world, distinct instances $\bar a,\bar b$ of $A$
therefore satisfy $\Box(\bar a\ne\bar b)$, since $\Box(\bar a=\bar b)$ would give
$\bar a=\bar b$. $\square$

## Lemma 4: Inextensible Comprehension descends

It is a theorem of C that Inextensible Comprehension at $\tau t$ implies it at $\tau$.

*Proof.* Let $X^\tau$. By Inextensible Comprehension at $\tau t$, let $G$ be
inextensible and coextensive with
$\lambda Y\, .\,\exists\bar a\, .\,X[\bar a]\land Y=\delta_{\bar a}$, and put

$$
U:=\lambda\bar a\, .\,\exists Y\, .\,GY\land Y[\bar a].
$$

$U$ is coextensive with $X$. Each instance of $G$ is a haecceity, so rigid, so
necessarily rigid; weak inextensibility of $G$ gives
$G\le\lambda Y\, .\,\operatorname{Rigid}(Y)$.

$U$ is inextensible. At any world, suppose
$\forall\bar a\, .\,U[\bar a]\to\Box Z[\bar a]$. For each $Y$ with $GY$, $Y$ is rigid
there and each instance of $Y$ is an instance of $U$, so weak inextensibility of $Y$
gives $Y\le Z$. Weak inextensibility of $G$, applied to
$\lambda Y\, .\,\forall\bar a\, .\,Y[\bar a]\to Z[\bar a]$, gives
$\Box\forall Y\, .\,GY\to\forall\bar a\, .\,(Y[\bar a]\to Z[\bar a])$, that is,
$U\le Z$. $\square$

**Corollary (Tame Rigidity at $\tau$).** Under ND at $t$ and Inextensible Comprehension
at $\tau t$, every weakly rigid $F^\tau$ is rigid: it is persistent, necessarily
separated by Lemma 3, and has an inextensible coextension by Lemma 4, so Lemma 2
applies.

## Lemma 5: the rigid subrelations of a rigid $F$ form a rigid property

*Assume ND at $t$ and Inextensible Comprehension at $\tau t$, and let $F^\tau$ be rigid.*
Then $R_F:=\lambda Y\, .\,\operatorname{Rigid}(Y)\land Y\le F$ is rigid.

*Proof.* $R_F$ is persistent, since both conjuncts are necessary when true. We show
$\operatorname{NecSeparated}(R_F)$; Inextensible Comprehension at $\tau t$ and Lemma 2
then make $R_F$ rigid.

At any world, let $X\ne Y$ both satisfy $R_F$. Being weakly rigid and distinct, they
are not coextensive (Sun's lemma: coextensive weakly rigid relations are identical),
say $X[\bar a]\land\neg Y[\bar a]$. Each instance $\bar b$ of $Y$ is an instance of $F$
with $\bar b\ne\bar a$, and $\bar a$ is an instance of $F$, so by
$\operatorname{NecSeparated}(F)$ (Lemma 3), $\Box(\bar b\ne\bar a)$. Weak
inextensibility of $Y$ gives $\Box\neg Y[\bar a]$, and persistence of $X$ gives
$\Box X[\bar a]$. So $\Box(X\ne Y)$. $\square$

## Lemma 6: weakly rigid subrelations of $F$ are rigid, at every world

*Let $F^\tau$ be rigid with $\operatorname{NecSeparated}(F)$.* Then

$$
\Box\forall X^\tau\, .\,\operatorname{WeaklyRigid}(X)\land X\le F\to\operatorname{Rigid}(X).
$$

*Proof.* At any world $v$, let $X$ be weakly rigid with $X\le F$. Put

$$
\operatorname{Settled}_X(\bar a):=\Box X[\bar a]\lor\Box\neg X[\bar a].
$$

Each instance $\bar a$ of $F$ at $v$ satisfies $\operatorname{Settled}_X$: if
$X[\bar a]$, by weak persistence of $X$; if not, each instance $\bar b$ of $X$ is an
instance of $F$ with $\bar b\ne\bar a$, so $\Box(\bar b\ne\bar a)$, and weak
inextensibility of $X$ gives $\Box\neg X[\bar a]$. By 4 this holds necessarily, so weak
inextensibility of $F$ gives

$$
F\le\operatorname{Settled}_X .
$$

Now let $u$ be any world accessible from $v$, and suppose
$\forall\bar a\, .\,X[\bar a]\to\Box Z[\bar a]$ at $u$. Each instance $\bar a$ of $F$ at
$u$ satisfies $\operatorname{Settled}_X$: if $\Box X[\bar a]$, then $X[\bar a]$ and
$\Box Z[\bar a]$; if $\Box\neg X[\bar a]$, trivially; either way
$\Box(X[\bar a]\to Z[\bar a])$. Weak inextensibility of $F$ at $u$ gives

$$
F\le\lambda\bar a\, .\,X[\bar a]\to Z[\bar a],
$$

and with $X\le F$, $X\le Z$. So $X$ is weakly inextensible at every world accessible
from $v$, and persistent, hence rigid at $v$. $\square$

## Proof of the theorem

Let $F^\tau$ be weakly rigid. By the Corollary it is rigid, and by Lemma 3 it is
necessarily separated. By Lemma 6 and T, necessarily
$P_FY\leftrightarrow R_FY$ for every $Y$, so $P_F=R_F$, which is rigid by Lemma 5 and
hence weakly rigid. $\square$

## Remarks

1. The premises used are ND at $t$ and Inextensible Comprehension at $\tau t$. The
   Corollary is Tame Rigidity at $\tau$ from the same premises, and Lemma 5 is Rigid
   Power at $\tau$.
2. Over ND and Boolean Completeness, the map already derives Inextensible
   Comprehension from Weakly Rigid Power, Tame Rigidity and Rigid Comprehension, and
   these from one another, except for the step to Weakly Rigid Power. With this result
   the four are equivalent over ND and Boolean Completeness.
