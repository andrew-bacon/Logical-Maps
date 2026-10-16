## Framework

The fixed background is **Classicism (C)** of Andrew Bacon and Cian Dorr,
using the paper's **relational type system**. Its base types are $e$ and $t$.
Form $\sigma\tau$ from admitted types only when $\tau\ne e$: every
function type ends in $t$. Thus $et$, $tt$ and $(et)t$ are admitted,
while $ee$ and $(ee)t$ are not. Individuals of type $e$ remain available
as arguments and quantified objects.

Use the definition in *Classicism*, §1.3: C is the smallest H-theory containing
Logical Equivalence. This schema identifies $\lambda$-abstractions of formulas
equivalent in H. Its theoremhood side condition must be preserved when
reasoning from additional assumptions.

This is the type system called R in *Classicism*, §1.1. It is fixed
throughout the map, so principle names omit a type-system suffix.

## Notation

Types associate to the right: $\sigma\tau\rho$ means
$\sigma\to(\tau\to\rho)$. Application also associates to the right:
$fgx=f(gx)$. Write $(fx)y$ for curried application. A dot separates a
binder from its scope. The abbreviation $X[\bar x]$ means explicitly
left-nested application to the displayed tuple; it is $X$ for an empty tuple.
For a finite, possibly empty, tuple of types $\bar\sigma=\sigma_1\ldots\sigma_n$,
$\bar\sigma\rho$ is the type $\sigma_1\cdots\sigma_n\rho$ (so $\bar\sigma t$ is
$\sigma_1\cdots\sigma_n t$), and $\bar x^{\bar\sigma}$ gives $x_i$ the type $\sigma_i$.
A tuple quantifier $\forall\bar x$ or $\exists\bar x$ binds $x_1,\ldots,x_n$ one at a
time; $\bar x=\bar y$ is the conjunction of the identities $x_i=y_i$ (true for the empty
tuple), and $\bar x\ne\bar y$ is its negation. With tuples in place of single
arguments, the definitions below are read in the evident way; for instance
$\operatorname{Serial}(U):=\forall\bar x^{\bar\sigma}\, .\,\exists y^\tau\, .\,(U[\bar x])y$
for $U^{\bar\sigma\tau t}$, and $\operatorname{Equiv}(R)$ for $R^{\bar\sigma\bar\sigma t}$
uses $(R[\bar x])[\bar y]$.

**Polyadic forms.** A principle with a type variable that may take the value
$e$ has a *polyadic form*, listed among its equivalent forms. The polyadic form
replaces that variable $\sigma$ by a tuple $\bar\sigma$, and its variables of type
$\sigma$ by tuples. (Relational Choice has two such variables; only the input one
is made a tuple.) The original form is the case of a one-element tuple. The converse
is proved in one of two ways.
- *One argument at a time*: by induction on the length of the tuple, currying the
  first argument.
- *Coding a tuple by its haecceity*: $H_{\bar x}:=\lambda\bar y^{\bar\sigma}\,
  .\,\bar y=\bar x$, of type $\bar\sigma t$. C proves $H_{\bar x}=H_{\bar y}\leftrightarrow
  \bar x=\bar y$, so the original form at the single type $\bar\sigma t$, applied to
  a relation on codes, yields the polyadic form at $\bar\sigma$. For the empty tuple the
  code type is $t$ and the only code is $\top$.

The equivalence of the boxed forms follows by necessitating these derivations.
Several of the equivalences have been checked in a Lean formalization of C.

Put $\Box p:=(p=\top)$ and $\Diamond p:=(p\ne\bot)$.
At a relational type $\tau$, Boolean operations are defined pointwise.
The order is algebraic entailment,
$X\le_\tau Y$ iff $Y=X\lor_\tau Y$, rather than material implication.
At $t$ this is equivalent to $\Box(X\to Y)$; at a relation type it is
equivalent to the necessary universal closure of the pointwise implication.

The lattice predicates used in the principles are:

$$
\begin{aligned}
\operatorname{LB}_\tau(y,X)&:=\forall z^\tau\, .\,Xz\to y\le_\tau z,\\
\operatorname{GLB}_\tau(y,X)&:=\forall z^\tau\, .\,
  \operatorname{LB}_\tau(z,X)\leftrightarrow z\le_\tau y,\\
\operatorname{Atom}_\tau(y)&:=\forall z^\tau\, .\,
  (z\le_\tau y\land z\ne y)\leftrightarrow z\le_\tau\neg_\tau z.
\end{aligned}
$$

Thus an atom is non-bottom and has no non-bottom strict lower bound.
These are the definitions of *Classicism*, §2.2, pp. 23–24.
The Axiom of Infinity is stated with Frege's cardinality apparatus. At a type
$\sigma$, a *cardinality* is an entity of type $(\sigma t)t$, and:

$$
\begin{aligned}
\mathbf{0}_\sigma&:=\lambda X^{\sigma t}\, .\,\forall u^\sigma\, .\,\neg Xu,\\
\operatorname{Suc}_\sigma(Z)&:=\lambda X^{\sigma t}\, .\,\exists y^\sigma\, .\,
  Xy\land Z(\lambda u^\sigma\, .\,Xu\land u\ne y),\\
\operatorname{FiniteCardinality}_\sigma(Z)&:=\forall W^{((\sigma t)t)t}\, .\,
  \bigl(W\mathbf{0}_\sigma\land\forall Y\, .\,WY\to W(\operatorname{Suc}_\sigma Y)\bigr)\to WZ.
\end{aligned}
$$

So $\mathbf{0}_\sigma$ is the cardinality of the empty property,
$\operatorname{Suc}_\sigma$ adds one to a cardinality, and
$\operatorname{FiniteCardinality}_\sigma$ collects the cardinalities reached from
$\mathbf{0}_\sigma$ by finitely many successors, in the impredicative sense
that they fall under every property of cardinalities that holds of
$\mathbf{0}_\sigma$ and of a successor whenever it holds of the cardinality
succeeded. Every type used here ends
in $t$, so all of them are admitted, and no type $\sigma\sigma$ is needed;
that is why the axiom is not put in the Dedekind form, which would ask for an
injective non-surjective operation from $\sigma$ to $\sigma$.

Countable Boolean Completeness and the Necessity of Arithmetic follow
Goodsell, *Arithmetic is Necessary*, which leaves the type $\nu$ of numbers,
zero and successor as parameters. The map takes them, at each type $\sigma$,
to be $\nu_\sigma:=(\sigma t)t$, $\mathbf{0}_\sigma$ and
$\operatorname{Suc}_\sigma$, and states both principles as schemata in
$\sigma$; the paper displays the instance $\sigma=e$ in its eqs. (24)–(25)
without assuming it. Natural numberhood $\mathbb N_\sigma$ is then
$\operatorname{FiniteCardinality}_\sigma$. Write
$\forall n\in\mathbb N_\sigma\, .\,A$ for
$\forall n^{\nu_\sigma}\, .\,\mathbb N_\sigma n\to A$, and likewise for
$\exists$. With these, for a type $\sigma$ and a relational type $\tau$:

$$
\begin{aligned}
\operatorname{Ctbl}_{\sigma,\tau}(X)&:=\exists R^{\tau\nu_\sigma t}\, .\,\forall y^\tau z^\tau\, .\,
  Xy\land Xz\to\bigl((\exists n\in\mathbb N_\sigma\, .\,Ryn\land Rzn)\leftrightarrow y=z\bigr),\\
I^*_\sigma&:=\forall m\,n\in\mathbb N_\sigma\, .\,\mathbf{0}_\sigma\ne\operatorname{Suc}_\sigma m\land
  (\operatorname{Suc}_\sigma m=\operatorname{Suc}_\sigma n\to m=n),\qquad I_\sigma:=\Diamond I^*_\sigma,\\
\operatorname{Sum}_\sigma(m,n,o)&:=\forall R^{\nu_\sigma\nu_\sigma t}\, .\,R\mathbf{0}_\sigma m\to
  (\forall i\,j\in\mathbb N_\sigma\, .\,Rij\to R(\operatorname{Suc}_\sigma i)(\operatorname{Suc}_\sigma j))\to Rno,\\
\operatorname{Prod}_\sigma(m,n,o)&:=\forall R^{\nu_\sigma\nu_\sigma t}\, .\,R\mathbf{0}_\sigma\mathbf{0}_\sigma\to
  (\forall i\,j\,k\in\mathbb N_\sigma\, .\,Rij\to\operatorname{Sum}_\sigma(m,j,k)\to R(\operatorname{Suc}_\sigma i)k)\to Rno.
\end{aligned}
$$

So $X$ is countable (relative to $\sigma$) when it injects into the natural
numbers counted at $\sigma$, and $I_\sigma$ says that possibly zero is not a
successor and successor is injective on numbers. In C the first conjunct of
$I^*_\sigma$ is a theorem, since $\mathbf{0}_\sigma$ and a successor differ at
$\lambda x^\sigma\, .\,\bot$. An *arithmetical sentence* at $\sigma$ is a
closed formula built from atomic formulas $\mathbb N_\sigma\mathbf n$,
$\operatorname{Sum}_\sigma(\mathbf m,\mathbf n,\mathbf o)$,
$\operatorname{Prod}_\sigma(\mathbf m,\mathbf n,\mathbf o)$ and $\mathbf m=\mathbf n$,
whose terms are variables of type $\nu_\sigma$, $\mathbf{0}_\sigma$ and
successors of terms, by $\neg$, $\lor$, $\land$ and quantifiers
$\forall v\in\mathbb N_\sigma$. These are Definitions 3–8 of Goodsell's
draft. Where the type is fixed by context the subscript $\sigma$ is dropped.

The schematic $\sigma$ is what lets the principles say what they intend
whatever the size of a given type. Where $\sigma$ necessarily has only
finitely many members, $\mathbb N_\sigma$ is finite, a property countable
relative to $\sigma$ is finite and so has a least upper bound in C, and
$I_\sigma$ is necessarily false; those instances are trivial.

Boolean Completeness is stated with $\operatorname{GLB}$. The dual form,
with $\operatorname{LUB}_\tau(y,X):=\forall z^\tau\, .\,
(\forall w^\tau\, .\,Xw\to w\le_\tau z)\leftrightarrow y\le_\tau z$,
is equivalent to it in C, and some proofs in the map use that form.

For a relation $Y$ with a finite argument tuple, including the empty tuple,
the comprehension predicates are:

$$
\begin{aligned}
\operatorname{Persistent}(Y)&:=Y\le\lambda\bar x\, .\,\Box Y[\bar x],\\
\operatorname{Inextensible}(Y)&:=\Box\forall X\, .\,
  (\forall\bar x\, .\,Y[\bar x]\to\Box X[\bar x])\to Y\le X,\\
\operatorname{Rigid}(Y)&:=\operatorname{Persistent}(Y)\land
  \operatorname{Inextensible}(Y).
\end{aligned}
$$

This is the rigidity convention of §2.3, p. 28. Gallin's alternative
convention has its own principle.

Since $Y\le Z$ is itself the necessary universal closure of the pointwise
implication, $\operatorname{Persistent}(Y)$ unpacks as
$\Box\forall\bar x\, .\,Y[\bar x]\to\Box Y[\bar x]$, and both
conjuncts of $\operatorname{Rigid}$ carry a leading $\Box$. Dropping it
gives the weak variants:

$$
\begin{aligned}
\operatorname{WeaklyPersistent}(Y)&:=\forall\bar x\, .\,
  Y[\bar x]\to\Box Y[\bar x],\\
\operatorname{WeaklyInextensible}(Y)&:=\forall X\, .\,
  (\forall\bar x\, .\,Y[\bar x]\to\Box X[\bar x])\to Y\le X,\\
\operatorname{WeaklyRigid}(Y)&:=\operatorname{WeaklyPersistent}(Y)\land
  \operatorname{WeaklyInextensible}(Y).
\end{aligned}
$$

$\operatorname{Rigid}$ is thus necessary weak rigidity. These are the
conventions of Dorr, *Boolean Completeness does not imply Rigid
Comprehension*, pp. 2 and 12. A weakly rigid relation is persistent: weak
inextensibility applied to $\lambda\bar x\, .\,\Box Y[\bar x]$, whose
hypothesis $Y[\bar x]\to\Box\Box Y[\bar x]$ holds by weak persistence and 4,
gives $Y\le\lambda\bar x\, .\,\Box Y[\bar x]$. So weak rigidity is equivalently
persistence together with weak inextensibility, the combination used in the
draft's Proposition 1.

For $U^{\sigma\tau t}$, set

$$
\begin{aligned}
\operatorname{Serial}(U)&:=\forall x^\sigma\, .\,\exists y^\tau\, .\,(Ux)y,\\
\operatorname{Functional}(U)&:=\forall x^\sigma\, .\,\exists y^\tau\, .\,
  (Ux)y\land\forall z^\tau\, .\,(Ux)z\to y=z.
\end{aligned}
$$

Functional includes totality. Relational Choice selects a functional
subrelation; Functional Choice selects an operation. An operation's output
type must differ from $e$. Relational Choice also covers relations with
individual outputs, since such a relation still ends in $t$.

For $R^{\sigma\sigma t}$, at any type $\sigma$ including $e$,

$$
\operatorname{Equiv}(R):=\forall x^\sigma\, .\,(Rx)x\;\land\;
\forall x^\sigma y^\sigma\, .\,(Rx)y\to(Ry)x\;\land\;
\forall x^\sigma y^\sigma z^\sigma\, .\,(Rx)y\land(Ry)z\to(Rx)z.
$$

The cell of $x$ is the property $\lambda z\, .\,(Rx)z$. Transversal Choice
asks for a property with exactly one instance in each cell. The equivalence
conditions and the transversal condition are unboxed, so they concern the
evaluation point only. Two members of one cell have coextensive cells, but
in C properties are identical only when necessarily coextensive.

For $R^{\sigma\sigma t}$ and $X^{\sigma t}$, at any type $\sigma$ including
$e$, the order predicates relativized to $X$ are

$$
\begin{aligned}
\operatorname{Trans}(R,X)&:=\forall x^\sigma y^\sigma z^\sigma\, .\,
  Xx\land Xy\land Xz\land(Rx)y\land(Ry)z\to(Rx)z,\\
\operatorname{Antisymm}(R,X)&:=\forall x^\sigma y^\sigma\, .\,
  Xx\land Xy\land(Rx)y\land(Ry)x\to x=y,\\
\operatorname{Total}(R,X)&:=\forall x^\sigma y^\sigma\, .\,
  Xx\land Xy\to(Rx)y\lor(Ry)x,\\
\operatorname{WellFounded}(R,X)&:=\forall Y^{\sigma t}\, .\,
  (\forall y^\sigma\, .\,Yy\to Xy)\land(\exists y^\sigma\, .\,Yy)\to
  \exists x^\sigma\, .\,Yx\land\forall y^\sigma\, .\,Yy\land(Ry)x\to y=x,\\
\operatorname{TotalOrder}(R,X)&:=\operatorname{Trans}(R,X)\land
  \operatorname{Antisymm}(R,X)\land\operatorname{Total}(R,X),\\
\operatorname{WO}(R,X)&:=\operatorname{TotalOrder}(R,X)\land
  \operatorname{WellFounded}(R,X).
\end{aligned}
$$

$\operatorname{TotalOrder}(R,X)$ says that $R$ totally orders $X$, or that
$X$ is an $R$-chain; $\operatorname{WO}(R,X)$ says that $R$ well-orders $X$.
Omitting $X$ means $X:=\lambda x\, .\,\top$, so that
$\operatorname{WO}(R)$ says that $R$ well-orders the whole type. Further,

$$
\begin{aligned}
\operatorname{Refl}(R)&:=\forall x^\sigma\, .\,(Rx)x,\\
\operatorname{Preorder}(R)&:=\operatorname{Refl}(R)\land\operatorname{Trans}(R).
\end{aligned}
$$

These orders are non-strict: Total includes reflexivity on $X$, and when
$R$ totally orders $X$, an $R$-minimal instance of a property included in
$X$ is its $R$-least instance. Like Equiv, all of these are unboxed, so they
concern the evaluation point, and each depends only on the extensions of $R$
and $X$ there: coextensive arguments satisfy them together. A relation can
be a well-order without necessarily being one, because instances that are
distinct here may be identical elsewhere, where antisymmetry then fails.
Orders on properties and relations defined by inclusion are typically only
preorders: coextensive but distinct relations each include the other.

Strong and weak worlds follow Bacon, *A Philosophical Introduction to
Higher-Order Logics*, §8.2, pp. 165–166. At a relational type $\sigma$, with
$\Diamond_\sigma X:=X\ne\bot_\sigma$,

$$
\begin{aligned}
\operatorname{SWorld}_\sigma(W)&:=\Diamond_\sigma W\land\Box\forall Y^\sigma\, .\,
  W\le_\sigma Y\lor W\le_\sigma\neg_\sigma Y,\\
\operatorname{WWorld}_\sigma(W)&:=\Diamond_\sigma W\land\forall Y^\sigma\, .\,
  W\le_\sigma Y\lor W\le_\sigma\neg_\sigma Y.
\end{aligned}
$$

A weak world is an atom in the sense above; a strong world necessarily settles
every entity of its type, including ones that do not actually exist. The
Weak Leibniz Biconditionals, $\forall X\, .\,\Diamond_\sigma X\to\exists W\, .\,
\operatorname{WWorld}_\sigma(W)\land W\le X$, are the map's Atomicity; the
Strong Leibniz Biconditionals replace $\operatorname{WWorld}$ by
$\operatorname{SWorld}$. In both, the right-to-left direction is a theorem of C. The type-$t$ instance
of the strong form is recorded separately, as is done for Atomicity.

Strong Possibility uses the distinctness-preserving modality of §2.6, p. 42:

$$
\Box_{\ne}p:=\exists q\, .\,q\land\Box(\Diamond q\to p),
\qquad \Diamond_{\ne}p:=\neg\Box_{\ne}\neg p.
$$

**Hats, two-hat necessity and 5-necessity.** For an operator $X^{tt}$ put

$$
\hat X:=\lambda p\, .\,\exists q\, .\,q\land\Box(\neg X\neg q\to p).
$$

In C, $\hat\Box=\Box_{\ne}$ (*The Bounds of Possibility*, Appendix D, Proposition
D17). *Two-hat necessity* is the hat of $\Box_{\ne}$, written $\hat{\hat\Box}$,
with dual $\hat{\hat\Diamond}p:=\neg\hat{\hat\Box}\neg p$. Call $X^{tt}$ an *S5
operator* when, necessarily, it is N, K and B:

$$
\operatorname{S5}(X):=\Box\bigl(\forall p\, .\,\Box p\to Xp\bigr)\land
\Box\bigl(\forall p\,q\, .\,X(p\to q)\to Xp\to Xq\bigr)\land
\Box\bigl(\forall p\, .\,p\to X\neg X\neg p\bigr).
$$

*5-necessity* is necessity under every S5 operator,
$\Box_5:=\lambda p\, .\,\forall X^{tt}\, .\,\operatorname{S5}(X)\to Xp$, with
dual $\Diamond_5$. Appendix D defines $\Box_5$ with the condition NKJF$_{\langle\rangle}$
in place of NKB; its facts (A5) and (C5) make the two definitions necessarily
equivalent. Theorems of C: $\Box\le\Box_{\ne}\le\hat{\hat\Box}\le\Box_5\le\lambda p\, .\,p$
(the order is necessary pointwise implication); each of these operators is
necessarily N, K, T and 4, and $\Box_5$ is an S5 operator; and if $\Box_{\ne}$ or
$\hat{\hat\Box}$ is identical to its own hat, it is identical to $\Box_5$.

## Conventions

**Type scope.** A formula containing type variables ($\sigma$, $\tau$, $\bar\sigma$)
is a schema. The principle is the set of its instances, one for each admissible
assignment of types to the variables. Type variables range over the fixed type system
above; $\bar\sigma$ ranges over finite tuples, including the empty one. A relational
type is any admitted type other than $e$, including $t$. A restriction is written as
a parenthesized proviso after the formula, as in $\ldots\qquad(\tau\ne e)$; a formula
without a proviso admits every assignment. The type variables are metalinguistic: there
is no quantification over types in C, and a type variable never falls within the scope
of an object-language operator except as a fixed parameter. Finite tuples and formula
schemata retain their stated metalinguistic side conditions.

**Modal scope.** A boxed schema means that each admitted, fully closed
object-language instance is necessary. Close its object variables before
boxing it. Type ranges and formula side conditions remain outside the box.
C5 abbreviates C plus boxed ND at all types. It is an optional preset,
not part of the fixed background. A proof under an optional premise cannot
be necessitated unless that premise is discharged or supplied necessarily.

**Negation.** Failure of a type schema means failure of at least one of its
admitted instances, not failure at every type: the negation of a principle $A_\sigma$
says that $\neg A_\sigma$ for some $\sigma$. A necessarily false instance,
$\Box\neg A_\sigma$ for some $\sigma$, is stronger and different from failure of the
boxed schema. Negated principle nodes are not added by this positive import.
Incompatibilities conclude False; model `violates` entries record schema failure.

**Infinite sets in model descriptions.** A model described with "an infinite set"
works for any infinite set; where a construction needs a particular one, its
description says so. "Infinite" means not finite, that is, in bijection with no
natural number. This is the notion the Axioms of Infinity express, the finite
cardinalities being defined inductively. Without the axiom of choice it is weaker than
Dedekind-infinity, but it is all that the arguments for the Infinity principles use, so
they hold in the choiceless variants of a model too. Those variants say which
hypothesis replaces choice.

**Pure and signature schemata.** In Maximalism, in its distinctness form and its possibility
form alike, $C$ denotes the fixed background logic. Its theoremhood and consistency
side conditions are retained literally. “Pure” means free of nonlogical
constants. The principles in the Signature schemata group give a special
role to nonlogical constants: they concern an arbitrary fixed signature
$\Sigma$ of nonlogical constants of admitted types, with
$\mathcal L(\Sigma)$ and $C(\Sigma)$ the language and background theory
over $\Sigma$. When $\Sigma$ is empty, some of these schemata have no
instances or only trivial ones, and the others reduce to their pure
versions; the results relating them need a constant of a type
$\tau\ne e$, so $\Sigma$ is assumed to contain one. Nothing further is assumed: no nonlogical axioms about
the constants are standing assumptions, and “distinct constants” means
distinct symbols, not an assumed inequality between their denotations.
Where a schema mentions a tuple of distinct constants, its instances are
those the signature supplies.

**Evidence.** *Classicism* is Bacon and Dorr (2024), in Fritz and Jones
(eds), *Higher-Order Metaphysics*, Oxford University Press, pp. 109–190.
References use the numbering of the 87-page draft dated 16 May 2023, from
which the map was built and which does not differ materially from the
published version, and, for the symmetric ideally-full models and the weak
rigidity principles, the 27-page draft of Dorr, *Boolean Completeness does
not imply Rigid Comprehension*, dated 30 July 2026. That second source is
a work in progress and is not distributed with the map; its records say so.
Models cite the construction and evaluation point directly.
The source models now use exactly the map's type system. Their listed
properties provide countermodel evidence at the stated evaluation point.
The singleton-root coalesced model still awaits an expansion to the fixed
nonlogical signature; its record explains this separate obligation.
Two results reported without proofs in the draft retain pending verification status.
No record claims an independent human check or Lean verification.
