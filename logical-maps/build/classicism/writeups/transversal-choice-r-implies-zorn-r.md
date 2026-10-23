# Transversal Choice implies Zorn's Lemma

The proof follows Jonathan Lewin, "A Simple Proof of Zorn's Lemma",
*American Mathematical Monthly* 98 (1991), pp. 353–354. It is translated into
C and adapted to preorders by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 8 October 2026, at
Cian Dorr's suggestion. Lewin's sets become properties, unions become
existential quantifications, and his choice function becomes a functional
relation. The translation is faithful except at four points. At each of them
two properties are shown to be coextensive, and Lewin's $f$ is then assumed
to give them the same value. For sets this is automatic. For properties it
is not, and Transversal Choice is used to arrange it.

**Claim.** For each type $\sigma$, including $e$, Transversal Choice
(at the type $\sigma t$, and through Relational Choice at the types
$\sigma t$ and $\sigma$) implies Zorn's Lemma at $\sigma$.

Preorder, TotalOrder, WellFounded and WO are as in Background. Everything
is unboxed, and the whole argument takes place at the evaluation point.

## Notation

Fix a preorder $R^{\sigma\sigma t}$, and write $x\preccurlyeq y$ for $(Rx)y$.
Put
$$x\prec y:=x\preccurlyeq y\land\neg\,y\preccurlyeq x.$$
By transitivity, $x\preccurlyeq y\prec z$ and $x\prec y\preccurlyeq z$ each
give $x\prec z$, and $x\prec x$ never holds. On a property $A$ that $R$
totally orders, $x\prec y$ is equivalent to $x\preccurlyeq y\land x\ne y$,
by antisymmetry on $A$; and for $x,y$ in $A$, exactly one of $x\prec y$,
$x=y$, $y\prec x$ holds.

For properties $C,D$ of type $\sigma t$, $C\subseteq D$ means
$\forall y\, .\,Cy\to Dy$, and $C\equiv D$ means
$\forall y\, .\,Cy\leftrightarrow Dy$. Lewin's equations between sets become
$\equiv$, not $=$. The initial segment of $C$ below $x$ is the property
$$P(C,x):=\lambda y\, .\,Cy\land y\prec x.$$

When $R$ well-orders $A$, every instantiated property included in $A$ has an
$R$-minimal instance, which is its $R$-least instance since $R$ totally
orders $A$. "The least instance of $Y$" below always refers to such a
property $Y\subseteq A$.

Suppose that every property $R$ totally orders has an upper bound, and,
for reductio, that nothing is maximal: for every $m$ there is $y$ with
$m\prec y$.

## An extensional choice relation

Let
$$(UC)x:=\operatorname{TotalOrder}(R,C)\to\forall y\, .\,Cy\to y\prec x,$$
a relation of type $\sigma t\to\sigma\to t$. It is serial. If $R$ totally
orders $C$, take an upper bound $u$ of $C$ and then $v$ with $u\prec v$; every
instance $y$ of $C$ has $y\preccurlyeq u\prec v$, so $y\prec v$. Otherwise
every $x$ is a $U$-image of $C$. Whether $(UC)x$ holds depends only on the
extension of $C$.

Transversal Choice implies Relational Choice, by the recorded result, so
there is a functional $S\subseteq U$. Coextensiveness is an equivalence
relation on $\sigma t$, so Transversal Choice at $\sigma t$ also gives
$\mathcal T^{(\sigma t)t}$ with exactly one instance coextensive with each
property (this is Transversal at $\sigma$). Put
$$(FC)x:=\exists D\, .\,\mathcal TD\land D\equiv C\land(SD)x.$$
Then:
- $F$ is **functional**, since exactly one $D$ in $\mathcal T$ is coextensive
  with $C$, and $S$ is functional;
- $F\subseteq U$, since $(SD)x$ gives $(UD)x$, and $U$ depends only on
  extensions;
- $F$ is **extensional**: if $C\equiv C'$ then $(FC)x\to(FC')x$, because the
  same $D$ serves for both.

Lewin's proof uses extensionality of $f$ without comment, since for sets it
is automatic. The steps marked **(E)** below are the four places where it is
used. Everywhere else, $S$ in place of $F$ would serve, so the transversal is
needed only at those four steps.

## Conforming properties

Call $A^{\sigma t}$ **conforming** if
- (a) $\operatorname{WO}(R,A)$, and
- (b) $\forall x\, .\,Ax\to(F\,P(A,x))\,x$.

**Lemma 1.** Let $A$ and $B$ be conforming, and suppose $A\not\subseteq B$.
Let $x$ be the least instance of $\lambda w\, .\,Aw\land\neg Bw$. Then
$B\equiv P(A,x)$.

*Proof.* First, $P(A,x)\subseteq B$, by the leastness of $x$. Suppose for
contradiction that $B\not\subseteq P(A,x)$, and let $y$ be the least instance
of $\lambda w\, .\,Bw\land\neg P(A,x)w$. By leastness of $y$,
$$P(B,y)\subseteq P(A,x)\subseteq A. \tag{1}$$
The property $\lambda w\, .\,Aw\land\neg P(B,y)w$ is instantiated by $x$,
since $x$ is not an instance of $B$. Let $z$ be its least instance.

We show $P(A,z)\equiv P(B,y)$.
- $P(A,z)\subseteq P(B,y)$, by leastness of $z$.
- Let $w$ be in $P(B,y)$. By (1), $w$ is in $A$ and $w\prec x$. If not
  $w\prec z$, then $z\preccurlyeq w$, since $R$ totally orders $A$. Then
  $z\preccurlyeq w\prec x$ gives $z\prec x$, so $z$ is in $P(A,x)$ and so in $B$.
  And $z\preccurlyeq w\prec y$ gives $z\prec y$, so $z$ is in $P(B,y)$,
  contradicting the choice of $z$. So $w\prec z$, and $w$ is in $P(A,z)$.

By (b) for $A$ and for $B$, $(F\,P(A,z))\,z$ and $(F\,P(B,y))\,y$. Since
$P(A,z)\equiv P(B,y)$, extensionality gives $(F\,P(A,z))\,y$ **(E)**, and
functionality gives $y=z$. So $y$ is in $A$. It is not in $P(A,x)$, so
$x\preccurlyeq y$, and $y\ne x$ since $y$ is in $B$ and $x$ is not. Hence
$x\prec y=z$, so $x$ is in $P(A,z)\equiv P(B,y)\subseteq B$, contradicting
the choice of $x$. $\square$

**Lemma 2.** If $A$ and $B$ are conforming, then $A\subseteq B$ or
$B\subseteq A$. If $A\subseteq B$, then $A$ is downward closed in $B$: if
$Aa$, $Bb$ and $b\preccurlyeq a$, then $Ab$.

*Proof.* The first part is Lemma 1. For the second, if also $B\subseteq A$
there is nothing to show. Otherwise Lemma 1, with $A$ and $B$ exchanged,
gives $A\equiv P(B,x)$ for some $x$, and $b\preccurlyeq a\prec x$ gives
$b\prec x$. $\square$

## The union of the conforming properties

Let
$$U^*:=\lambda x\, .\,\exists A^{\sigma t}\, .\,\operatorname{Conf}(A)\land Ax,$$
where $\operatorname{Conf}(A)$ abbreviates (a) and (b).

**Lemma 3.** If $A$ is conforming, $Aa$, $U^*w$ and $w\preccurlyeq a$, then
$Aw$. Hence $P(U^*,a)\equiv P(A,a)$.

*Proof.* Let $w$ be in the conforming $B$. If $B\subseteq A$, done. Otherwise
$A\subseteq B$ by Lemma 2, and $Aw$ by downward closure. For the second
part, $P(A,a)\subseteq P(U^*,a)$ is clear, and the converse is the first
part. $\square$

**Lemma 4.** $U^*$ is conforming.

*Proof.* (a) Transitivity holds since $R$ is a preorder. Any two instances
of $U^*$ lie in conforming properties, one of which includes the other by
Lemma 2. So both lie in a single property that $R$ totally orders, which
gives totality and antisymmetry. For well-foundedness, let $Y\subseteq U^*$
have an instance $y$, lying in a conforming $A$. Let $m$ be the least
instance of $\lambda w\, .\,Yw\land Aw$. If $Yw$ and $w\preccurlyeq m$, then
$Aw$ by Lemma 3, so $w=m$. So $m$ is $R$-minimal in $Y$.

(b) Let $U^*x$, with $x$ in the conforming $A$. Then $(F\,P(A,x))\,x$, and
$P(U^*,x)\equiv P(A,x)$ by Lemma 3, so $(F\,P(U^*,x))\,x$ **(E)**. $\square$

## The contradiction

By (a), $R$ totally orders $U^*$. Since $F$ is functional, there is an $x$
with $(FU^*)x$. Then $(U U^*)x$, so every instance $y$ of $U^*$ has $y\prec x$.
Let
$$U':=\lambda w\, .\,U^*w\lor w=x.$$

**Lemma 5.** $U'$ is conforming.

*Proof.* (a) Transitivity holds since $R$ is a preorder. Totality: instances
of $U^*$ are comparable with one another and lie below $x$. Antisymmetry:
within $U^*$ it holds already, and for $U^*y$ we never have $x\preccurlyeq y$,
since $y\prec x$. Well-foundedness: let $Y\subseteq U'$ be instantiated. If
$\lambda w\, .\,Yw\land U^*w$ is instantiated, its $R$-minimal instance $m$
is $R$-minimal in $Y$, because $x\preccurlyeq m$ is impossible. Otherwise
$x$ is the only instance of $Y$.

(b) At $x$: $P(U',x)\equiv U^*$, since every instance of $U^*$ lies below $x$,
and $x\prec x$ fails. We have $(FU^*)x$, so $(F\,P(U',x))\,x$ **(E)**. At $u$
with $U^*u$: $u\prec x$, so $x\prec u$ fails, and $P(U',u)\equiv P(U^*,u)$.
By Lemma 4, $(F\,P(U^*,u))\,u$, so $(F\,P(U',u))\,u$ **(E)**. $\square$

By Lemma 5, $x$ is an instance of the conforming $U'$, so $U^*x$, and then
$x\prec x$, which is impossible. So some element is maximal: there is $m$
with $\forall y\, .\,m\preccurlyeq y\to y\preccurlyeq m$.

## Remarks

**Preorders.** The adaptation to preorders affects only the definitions of
$\prec$ and of conforming. Since chains must be antisymmetric, a conforming
property never contains two distinct $R$-equivalent elements.

**Coextension.** The four steps marked (E) are the only non-extensional
moves. In each, the two properties are generally distinct. For example,
$P(U',x)=\lambda w\, .\,(U^*w\lor w=x)\land w\prec x$ is coextensive with
$U^*$ but need not be necessarily coextensive with it. Without
extensionality of $F$, the argument establishes only coextension of the
relevant properties, and gives no information about their $F$-images.

**Relational Choice alone.** Zorn's Lemma implies Well-Ordering, which
implies Transversal Choice, by the recorded results. So a proof of Zorn's
Lemma from Relational Choice alone would settle the open question whether
Relational Choice implies Transversal Choice. Any such proof must avoid the
four steps marked (E). With Weak Rigid Comprehension in place of the
transversal, an extensional $F$ is still available: choose from the weakly
rigid property coextensive with $C$, which is unique by the recorded result
relational-choice-and-weak-rigid-comprehension-imply-transversal-choice.

## Paper references

- **Proof: [A Simple Proof of Zorn's Lemma](https://digitalcommons.kennesaw.edu/facpubs/1158/).** Lewin, Jonathan W. (1991). A Simple Proof of Zorn's Lemma. American Mathematical Monthly 98(4), pp. 353–354. — pp. 353–354. Lewin proves Zorn's Lemma for partial orders on sets from a choice function. The translation replaces sets by properties and the choice function by a functional relation, adapts the argument to preorders, and uses Transversal Choice to make the relation extensional, which Lewin uses at four steps without comment.
