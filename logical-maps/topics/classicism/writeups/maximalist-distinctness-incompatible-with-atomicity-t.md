# Maximalism (pure) and Atomicity (type t) are incompatible

Proof by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22–23 October 2026:
the splitting sentence, Atomicity's refutation of it, and its non-refutability via a
full Boolean-valued model over the rigid Jech–Shelah algebra. Rewritten for the map,
with a simpler coding of the algebra (third-order arithmetic in place of hereditarily
small sets) and a direct definition of the splitter, by Claude Opus 5.5 (Anthropic),
prompted by Cian Dorr, 24 October 2026.

**Claim.** C + Maximalism (pure) + Atomicity (type $t$) is inconsistent.

**Overview.** For a closed term $F$ of type $tt$ put

$$
S_F:=\forall p\, .\,p\ne\bot\to\bigl(p\land Fp\ne\bot\ \land\ p\land\neg Fp\ne\bot\bigr),
$$

"$F$ splits every non-bottom proposition". Lemma 1 shows that C + Atomicity$(t)$ proves $S_F=\bot$, for *every* closed $F$: an atom below $S_F$ could not be split. It remains to find a closed **pure** $F$ with $C\nvdash S_F=\bot$; then Maximalism (pure) gives $S_F\ne\bot$. We obtain $F$ from a full Boolean-valued model of C over a complete Boolean algebra $B$ that is rigid and has an explicit, arithmetically definable presentation: the algebra of Jech and Shelah. Full higher-order logic over $B$ interprets third-order arithmetic, and in third-order arithmetic one can define the Jech–Shelah algebra together with a canonical splitter of each non-zero element. Rigidity makes the isomorphism between $B$ and this arithmetically defined copy unique, so the splitter is pure-definable over $B$ itself.

Notation is that of Background. In particular $\Box p:=(p=\top)$, $\Diamond p:=(p\ne\bot)$, and at type $t$, $x\le y$ is $y=x\lor y$, which C proves equivalent to $\Box(x\to y)$.

## 1. Atomicity refutes every splitter

The following theorems of C are used: (C1) if $\vdash A$ then $\vdash\Box A$, and $\vdash\Box(A\to B)\to\Box A\to\Box B$; (C2) $\vdash a=b\to\Box\,a=b$, hence $\vdash\Diamond(a\ne b)\to a\ne b$; (C3) $\vdash x\le y\leftrightarrow\Box(x\to y)$, $\vdash x\le\neg x\leftrightarrow x=\bot$, and $\vdash x\to x\ne\bot$, for $x,y$ of type $t$.

**Lemma 1.** For every closed term $F^{tt}$, C + Atomicity$(t)$ $\vdash S_F=\bot$.

*Proof.* Suppose $S_F\ne\bot$. Then $\neg(S_F\le\neg S_F)$ by (C3), so the instance of Atomicity$(t)$ at $p:=S_F$ gives $w$ with

$$
\operatorname{Atom}_t(w)\land w\le S_F. \tag{1}
$$

The instances $z:=\bot$ and $z:=w\land Fw$ of $\operatorname{Atom}_t(w)$ are

$$
(\bot\le w\land\bot\ne w)\leftrightarrow\bot\le\neg\bot,\qquad
(w\land Fw\le w\land w\land Fw\ne w)\leftrightarrow w\land Fw\le\neg(w\land Fw).
$$

The first gives $w\ne\bot$, that is,

$$
\Diamond w. \tag{2}
$$

By the second, either $w\land Fw=w$, whence $w\land\neg Fw=w\land Fw\land\neg Fw=\bot$, or $w\land Fw\le\neg(w\land Fw)$, whence $w\land Fw=\bot$ by (C3):

$$
w\land Fw=\bot\ \lor\ w\land\neg Fw=\bot. \tag{3}
$$

From (1) and (C3), $\Box(w\to S_F)$. By (C1) applied to instantiation of the universal $S_F$ at $w$, and to $w\to w\ne\bot$,

$$
\Box\bigl(S_F\to(w\ne\bot\to(w\land Fw\ne\bot\land w\land\neg Fw\ne\bot))\bigr),\qquad
\Box(w\to w\ne\bot),
$$

so

$$
\Box\bigl(w\to(w\land Fw\ne\bot\ \land\ w\land\neg Fw\ne\bot)\bigr).
$$

With (2) and (C1),

$$
\Diamond(w\land Fw\ne\bot)\ \land\ \Diamond(w\land\neg Fw\ne\bot),
$$

and by (C2)

$$
w\land Fw\ne\bot\ \land\ w\land\neg Fw\ne\bot,
$$

contradicting (3). Hence $S_F=\bot$. $\square$

Atomicity is used once, unboxed, as a premise; everything necessitated is a theorem of C.

## 2. Full Boolean-valued models

Let $B$ be a complete Boolean algebra. The **full model** over $B$ has

$$
D_e=\{*\},\qquad D_t=B,\qquad D_{\sigma\tau}=D_\tau^{D_\sigma},
$$

ordinary application and abstraction, Boolean operations for the connectives, meets and joins over $D_\sigma$ for $\forall x^\sigma$ and $\exists x^\sigma$, and

$$
\llbracket a=b\rrbracket=\begin{cases}1&\text{if }\llbracket a\rrbracket=\llbracket b\rrbracket,\\ 0&\text{otherwise.}\end{cases}
$$

**Lemma 2 (soundness).** Every theorem of C has value $1$ in the full model over $B$, under every assignment.

This is the standard verification (Bacon, *Could the truths of mathematics have been different?*, online appendix §B.2; see also [the full Boolean-valued model](full-boolean-valued-atom-and-atomless.html), §2, whose argument does not depend on the particular algebra). In brief: the axioms of H have value $1$ and its rules preserve value $1$; and if $A\leftrightarrow A'$ has value $1$ under every assignment, then $\llbracket A\rrbracket=\llbracket A'\rrbracket$ under every assignment, so $\lambda\bar x\, .\,A$ and $\lambda\bar x\, .\,A'$ denote the same function and Logical Equivalence holds.

Call a formula an **identity formula** if it is built from identities $a=b$ (between arbitrary terms) by connectives and quantifiers. Let $\mathfrak D$ be the classical many-sorted structure with domains $D_\sigma$, application, and identity.

**Lemma 3.** For an identity formula $\varphi$ and every assignment $g$, $\llbracket\varphi\rrbracket_g\in\{0,1\}$, and $\llbracket\varphi\rrbracket_g=1$ iff $\mathfrak D\models\varphi[g]$.

*Proof.* Induction on $\varphi$: identities have values in $\{0,1\}$; Boolean operations on $\{0,1\}$ are the classical ones; a meet (join) of a family from $\{0,1\}$ is $1$ iff every (some) member is $1$. $\square$

For $X$ of type $\sigma t$ write

$$
x\mathrel{\varepsilon}X\ :=\ Xx=\top,\qquad \operatorname{ext}(X):=\{d\in D_\sigma:X(d)=1\}.
$$

Every subset of $D_\sigma$ is $\operatorname{ext}(X)$ for some $X\in D_{\sigma t}$, namely its $\{0,1\}$-valued characteristic function. So, restricted to identity formulas, the full model is full classical higher-order logic over the set $B$.

## 3. The Jech–Shelah algebra

The following is from T. Jech and S. Shelah, "A complete Boolean algebra that has no proper atomless complete subalgebra", *Journal of Algebra* 182 (1996), 748–755, pp. 749–750. Let

$$
P_0=N_0=1,\qquad P_k=N_0\cdots N_{k-1},\qquad N_k=2^{P_k}\quad(k\ge1).
$$

The **master tree** $\mathbb T\subseteq\omega^{<\omega}$ and the bijection $\operatorname{ind}:\mathbb T\to\omega$ are fixed by: $\operatorname{ind}(\langle\rangle)=0$; $\operatorname{ind}$ enumerates $\mathbb T$ by length and, within a length, lexicographically; and the node $s$ with $\operatorname{ind}(s)=k$ has exactly the $N_k$ successors $s^\frown i$, $i<N_k$. Write $s_k$ for the node with index $k$. Both $\mathbb T$ and $\operatorname{ind}$ are recursive.

$\mathbb P$ is the set of non-empty, prefix-closed $T\subseteq\mathbb T$ such that

$$
\forall s\in T\ \forall m\ \exists t\in T\, .\ t\supsetneq s\ \land\ |\{i:t^\frown i\in T\}|\ge P_{\operatorname{ind}(t)}^m, \tag{4}
$$

ordered by inclusion. For $T\in\mathbb P$ and $a\in T$ put $(T)_a:=\{s\in T:s\subseteq a\lor a\subseteq s\}$; then $(T)_a\in\mathbb P$ and $(T)_a\subseteq T$. By (4) every $T\in\mathbb P$ has nodes of every length.

$\operatorname{RO}(\mathbb P)$ is the set of $U\subseteq\mathbb P$ such that

$$
\begin{aligned}
&T\in U\land T'\in\mathbb P\land T'\subseteq T\ \Rightarrow\ T'\in U,\\
&T\in\mathbb P\land\forall T'\in\mathbb P\,(T'\subseteq T\Rightarrow\exists T''\in U\, .\,T''\subseteq T')\ \Rightarrow\ T\in U,
\end{aligned}
$$

ordered by inclusion. It is a complete Boolean algebra, Jech's $B(\mathbb P)$, in which $U\land V=U\cap V$, $0=\varnothing$, and $U\le V$ iff $U\subseteq V$ (see T. Jech, *Set Theory*, 3rd millennium ed., Springer 2003, Chapter 7 and §14).

**Theorem (Jech–Shelah, p. 749; proof pp. 752–754).** $\operatorname{RO}(\mathbb P)$ is rigid: its only automorphism is the identity.

The proof is in ZFC. Nothing else from the paper is used: neither the minimality of the generic real nor the absence of proper atomless complete subalgebras.

For $a\in\mathbb T$ let

$$
\operatorname{Cyl}_a:=\{T\in\mathbb P:\text{every node of }T\text{ is }\subseteq\text{-comparable with }a\}.
$$

**Lemma 4.** (i) $\operatorname{Cyl}_a\in\operatorname{RO}(\mathbb P)$. (ii) For every $U\in\operatorname{RO}(\mathbb P)$ with $U\ne\varnothing$ there is $a\in\mathbb T$ with

$$
U\cap\operatorname{Cyl}_a\ne\varnothing\quad\text{and}\quad U\not\subseteq\operatorname{Cyl}_a,
$$

that is, $U\land\operatorname{Cyl}_a\ne0$ and $U\land\neg\operatorname{Cyl}_a\ne0$.

*Proof.* (i) $\operatorname{Cyl}_a$ is closed downwards. Let $T\in\mathbb P\setminus\operatorname{Cyl}_a$, with $b\in T$ incomparable with $a$. Every $T''\in\mathbb P$ with $T''\subseteq(T)_b$ has a node longer than $b$; it extends $b$, so it is incomparable with $a$, and $T''\notin\operatorname{Cyl}_a$. So $T':=(T)_b\subseteq T$ has no $T''\subseteq T'$ in $\operatorname{Cyl}_a$, and $\operatorname{Cyl}_a$ satisfies the second clause.

(ii) Let $T\in U$ and $s\in T$ with $|s|=2$. As $N_0=1$, the only node of length $1$ is $\langle0\rangle$, with index $1$, so $\operatorname{ind}(s)\ge2$. By (4) with $m=1$ there is $t\supsetneq s$ in $T$ with at least $P_{\operatorname{ind}(t)}\ge P_3=8$ successors in $T$; let $a\ne b$ be two of them. Then $(T)_a,(T)_b\in U$, $(T)_a\in\operatorname{Cyl}_a$, and $(T)_b\notin\operatorname{Cyl}_a$ since $b\in(T)_b$ is incomparable with $a$. $\square$

In particular $\operatorname{RO}(\mathbb P)$ is atomless, hence infinite.

From now on identify each $T\in\mathbb P$ with $\operatorname{ind}[T]\subseteq\omega$, so that $\mathbb P\subseteq\mathcal P(\omega)$ and $\operatorname{RO}(\mathbb P)\subseteq\mathcal P(\mathcal P(\omega))$, and let

$$
B:=\operatorname{RO}(\mathbb P),\qquad \mathfrak D:=\text{the full model over }B.
$$

## 4. Third-order arithmetic inside the full model

Let $\mathcal L^3$ be the language of third-order arithmetic: number variables $x,y,\ldots$; real variables $X,Y,\ldots$ (sets of numbers); class variables $\mathcal U,\mathcal V,\ldots$ (sets of reals); and, for each $k\ge2$, variables $R,\ldots$ for $k$-ary relations on numbers. Its atomic formulas are identities between number terms (built from $0$ and successor $\mathrm s$), between reals, and between classes, and $x\in X$, $X\in\mathcal U$, $R(\bar x)$. Let $\mathfrak A$ be its standard full model over $\omega$.

**Lemma 5 (arithmetic).** Every arithmetical relation on numbers and reals is definable in $\mathfrak A$ by an $\mathcal L^3$ formula.

This is standard: $x+y=z$ holds iff $(x,y,z)$ belongs to every ternary relation containing all $(u,0,u)$ and closed under $(u,v,w)\mapsto(u,\mathrm sv,\mathrm sw)$, similarly for multiplication, and every arithmetical formula is a first-order formula in $0,\mathrm s,+,\times$ and $\in$. Since $\mathbb T$, $\operatorname{ind}$, $k\mapsto P_k$ and $k\mapsto N_k$ are recursive, and (4) is arithmetical in $T$, there are $\mathcal L^3$ formulas such that in $\mathfrak A$:

- $\operatorname{Cond}(X)$ holds iff $X\in\mathbb P$;
- $\operatorname{InCyl}(x,X)$ holds iff $X\in\operatorname{Cyl}_{s_x}$;
- $x<y$ is the usual order.

Define further

$$
\begin{aligned}
\operatorname{RegOpen}(\mathcal U)&:=\forall X\,(X\in\mathcal U\to\operatorname{Cond}(X))\\
&\quad\land\forall X\,\forall Y\,\bigl(X\in\mathcal U\land\operatorname{Cond}(Y)\land Y\subseteq X\to Y\in\mathcal U\bigr)\\
&\quad\land\forall X\,\bigl(\operatorname{Cond}(X)\land\forall Y\,(\operatorname{Cond}(Y)\land Y\subseteq X\to\exists Z\,(Z\in\mathcal U\land Z\subseteq Y))\to X\in\mathcal U\bigr),\\
\operatorname{Included}(\mathcal U,\mathcal V)&:=\forall X\,(X\in\mathcal U\to X\in\mathcal V),\\
\operatorname{IsCyl}(\mathcal U,x)&:=\forall X\,(X\in\mathcal U\leftrightarrow\operatorname{InCyl}(x,X)),\\
\operatorname{SplitsAt}(\mathcal U,x)&:=\exists X\,(X\in\mathcal U\land\operatorname{InCyl}(x,X))\land\exists X\,(X\in\mathcal U\land\neg\operatorname{InCyl}(x,X)).
\end{aligned}
$$

In $\mathfrak A$, $\operatorname{RegOpen}$ defines $B$, $\operatorname{Included}$ defines its order, $\operatorname{IsCyl}(\mathcal U,x)$ says $\mathcal U=\operatorname{Cyl}_{s_x}$, and, by Lemma 4, $\operatorname{SplitsAt}(\mathcal U,x)$ says $\mathcal U\land\operatorname{Cyl}_{s_x}\ne0$ and $\mathcal U\land\neg\operatorname{Cyl}_{s_x}\ne0$.

**Representing $\mathcal L^3$ in $\mathfrak D$.** Let $N,\mathrm S$ have type $tt$ and $z$ type $t$, and put

$$
\begin{aligned}
\operatorname{Nat}(N,z,\mathrm S)&:=z\mathrel{\varepsilon}N\land\forall x\,(x\mathrel{\varepsilon}N\to\mathrm Sx\mathrel{\varepsilon}N\land\mathrm Sx\ne z)\\
&\quad\land\forall x\,\forall y\,(x\mathrel{\varepsilon}N\land y\mathrel{\varepsilon}N\land\mathrm Sx=\mathrm Sy\to x=y)\\
&\quad\land\forall X^{tt}\,\bigl(z\mathrel{\varepsilon}X\land\forall x\,(x\mathrel{\varepsilon}N\land x\mathrel{\varepsilon}X\to\mathrm Sx\mathrel{\varepsilon}X)\to\forall x\,(x\mathrel{\varepsilon}N\to x\mathrel{\varepsilon}X)\bigr),\\
\operatorname{Real}_N(X^{tt})&:=\forall x\,\bigl((x\mathrel{\varepsilon}N\land x\mathrel{\varepsilon}X)\lor Xx=\bot\bigr),\\
\operatorname{Class}_N(\mathcal U^{(tt)t})&:=\forall X\,\bigl((\operatorname{Real}_N(X)\land X\mathrel{\varepsilon}\mathcal U)\lor\mathcal UX=\bot\bigr).
\end{aligned}
$$

For $W=(N,z,\mathrm S)$, the translation $\varphi\mapsto\varphi^W$ of $\mathcal L^3$ replaces $0$ by $z$ and $\mathrm s$ by $\mathrm S$; relativizes number quantifiers to $x\mathrel{\varepsilon}N$ (variables of type $t$), real quantifiers to $\operatorname{Real}_N$ (type $tt$), and class quantifiers to $\operatorname{Class}_N$ (type $(tt)t$); leaves $k$-ary relation quantifiers (type $t\cdots tt$) unrestricted; and replaces $x\in X$, $X\in\mathcal U$, $R(\bar x)$ by $x\mathrel{\varepsilon}X$, $X\mathrel{\varepsilon}\mathcal U$, $R\bar x=\top$. Every $\varphi^W$ is an identity formula with no nonlogical constants.

**Lemma 6 (transport).** Suppose $\mathfrak D\models\operatorname{Nat}(N,z,\mathrm S)$. Then there are bijections

$$
\theta:\operatorname{ext}(N)\to\omega,\qquad
\theta:\{X:\mathfrak D\models\operatorname{Real}_N(X)\}\to\mathcal P(\omega),\qquad
\theta:\{\mathcal U:\mathfrak D\models\operatorname{Class}_N(\mathcal U)\}\to\mathcal P(\mathcal P(\omega)),
$$

and surjections $\theta$ from $D_{t\cdots tt}$ onto the $k$-ary relations on $\omega$, such that for every $\mathcal L^3$ formula $\varphi$ and every assignment $g$ of such arguments,

$$
\mathfrak D\models\varphi^W[g]\iff\mathfrak A\models\varphi[\theta\circ g].
$$

Moreover such $N,z,\mathrm S$ exist.

*Proof.* On numbers, $\theta$ is the unique isomorphism $(\operatorname{ext}(N),z,\mathrm S)\cong(\omega,0,\mathrm s)$, which exists by Dedekind's categoricity theorem, since every subset of $\operatorname{ext}(N)$ is $\operatorname{ext}(X)$ for some $X$. Put $\theta(X):=\theta[\operatorname{ext}(X)]$, $\theta(\mathcal U):=\{\theta(X):\operatorname{Real}_N(X),\ \mathcal U(X)=1\}$, and $\theta(R):=\{\theta(\bar x):\bar x\in\operatorname{ext}(N)^k,\ R\bar x=1\}$. A $\operatorname{Real}_N$ predicate takes value $1$ on $\operatorname{ext}(X)\subseteq\operatorname{ext}(N)$ and $0$ elsewhere, so it is determined by $\operatorname{ext}(X)$; by fullness every subset of $\operatorname{ext}(N)$ arises. Hence $\theta$ is a bijection on reals, and likewise on classes. Fullness also makes $\theta$ onto the $k$-ary relations. The equivalence follows by induction on $\varphi$, using Lemma 3; the quantifier cases use surjectivity of $\theta$. For existence, $B$ is infinite: take distinct $b_0,b_1,\ldots\in B$, let $N$ be the characteristic function of $\{b_k:k\in\omega\}$, $z=b_0$, and $\mathrm S(b_k)=b_{k+1}$, $\mathrm S(c)=c$ otherwise. $\square$

## 5. The pure splitter

With $W=(N,z,\mathrm S)$, $h$ of type $t((tt)t)$, and $p,q,n,m$ of type $t$, define

$$
\begin{aligned}
\operatorname{Iso}_W(h)&:=\forall p\,\bigl(\operatorname{Class}_N(hp)\land\operatorname{RegOpen}^W(hp)\bigr)\\
&\quad\land\forall\mathcal U\,\bigl(\operatorname{Class}_N(\mathcal U)\land\operatorname{RegOpen}^W(\mathcal U)\to\exists p\, .\,hp=\mathcal U\bigr)\\
&\quad\land\forall p\,\forall q\,\bigl(p\le q\leftrightarrow\operatorname{Included}^W(hp,hq)\bigr),\\[4pt]
\operatorname{Sel}(p,q)&:=\exists N\,\exists z\,\exists\mathrm S\,\exists h\,\exists n\,.\ \operatorname{Nat}(N,z,\mathrm S)\land\operatorname{Iso}_W(h)\land n\mathrel{\varepsilon}N\land\operatorname{IsCyl}^W(hq,n)\\
&\qquad\land\operatorname{SplitsAt}^W(hp,n)\land\forall m\,\bigl(m\mathrel{\varepsilon}N\land(m<n)^W\to\neg\operatorname{SplitsAt}^W(hp,m)\bigr),\\[4pt]
F&:=\lambda p\, .\,\exists q\, .\,\operatorname{Sel}(p,q)\land q.
\end{aligned}
$$

$F$ is a closed term of type $tt$ containing no nonlogical constants. All its types end in $t$, so it belongs to the language of the map. $\operatorname{Sel}$ is an identity formula.

For $p\in B$, $p\ne0$, let $n(p)$ be the least $n$ such that $p\land\operatorname{Cyl}_{s_n}\ne0$ and $p\land\neg\operatorname{Cyl}_{s_n}\ne0$. It exists by Lemma 4(ii).

**Lemma 7.** In $\mathfrak D$, $\llbracket F\rrbracket(p)=\operatorname{Cyl}_{s_{n(p)}}$ for every $p\ne0$.

*Proof.* Let $N,z,\mathrm S,h$ satisfy $\operatorname{Nat}(N,z,\mathrm S)\land\operatorname{Iso}_W(h)$ in $\mathfrak D$, and let $\theta$ be as in Lemma 6. By Lemma 6, $\theta\circ h:B\to B$ maps $B$ into $\operatorname{RO}(\mathbb P)=B$ and onto it, and

$$
p\le q\iff\theta(hp)\subseteq\theta(hq).
$$

So $\theta\circ h$ is an order automorphism of $B$, hence a Boolean automorphism, hence the identity by the Jech–Shelah theorem. Therefore, by Lemma 6,

$$
\mathfrak D\models\operatorname{Sel}(p,q)\iff\exists n\in\omega\, .\ q=\operatorname{Cyl}_{s_n}\land n\text{ is least with }p\land\operatorname{Cyl}_{s_n}\ne0\land p\land\neg\operatorname{Cyl}_{s_n}\ne0,
$$

provided some $N,z,\mathrm S,h$ satisfy $\operatorname{Nat}\land\operatorname{Iso}_W$. They do: take $N,z,\mathrm S$ from Lemma 6 and $h(p):=$ the $\operatorname{Class}_N$ predicate with $\theta(h(p))=p$. Hence, for $p\ne0$, $\llbracket\operatorname{Sel}(p,q)\rrbracket=1$ if $q=\operatorname{Cyl}_{s_{n(p)}}$ and $=0$ otherwise, by Lemma 3, and

$$
\llbracket F\rrbracket(p)=\bigvee_{q\in B}\bigl(\llbracket\operatorname{Sel}(p,q)\rrbracket\land q\bigr)=\operatorname{Cyl}_{s_{n(p)}}.\qquad\square
$$

Without rigidity the argument fails at exactly one point. Different witnesses $h$ could select different $q$, and $\llbracket F\rrbracket(p)$ would be their join, which need not split $p$. Some such restriction is unavoidable for a full model: every automorphism of $B$ extends to an automorphism of the full model, which fixes the denotation of every closed pure term. So $\llbracket F\rrbracket$ must commute with every automorphism of $B$.

## 6. Proof of the claim

$S_F$ is an identity formula. For $p=0$ its matrix has value $1$ because the antecedent has value $0$. For $p\ne0$, Lemma 7 and the definition of $n(p)$ give

$$
p\land\llbracket F\rrbracket(p)\ne0,\qquad p\land\neg\llbracket F\rrbracket(p)\ne0.
$$

So by Lemma 3, $\llbracket S_F\rrbracket=1$ and $\llbracket S_F=\bot\rrbracket=0\ne1$. By Lemma 2,

$$
C\nvdash S_F=\bot.
$$

As $S_F=\bot$ is a closed pure identity, Maximalism (pure) gives $S_F\ne\bot$, while Lemma 1 gives $S_F=\bot$ from Atomicity$(t)$. $\square$
