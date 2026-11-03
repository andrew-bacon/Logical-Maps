# Boxed Church Numeral Infinity implies sequence functional recursion

Codex (OpenAI), prompted by Andrew Bacon, 2 November 2026, building on Bacon's
least-relation construction in *Notes for Zach* (25 March 2023), §§1–3, pp. 1–4.
The accumulator and constructor proof below are additions to that note.

Work in C. Let $\alpha,\tau$ be relational types and $\sigma$ any type. Write
$\nu,0,s,N,I$ for the Church numeral type, zero, successor, least inductive
property and Church Numeral Infinity at $\alpha$. Set

$$B:=\nu\to t,\qquad L:=(\sigma\to B\to B)\to B\to B.$$

Use $\epsilon:=\lambda Xp\, .\,p$ and
$\operatorname{cons}(b,u):=\lambda Xp\, .\,(Xb)((uX)p)$, and let
$\operatorname{Seq}$ be their least inductive property. Definitions appear on
the Background page *Church numerals and sequences*. The accumulator is $B$,
not $t$; no result for the original $t$-accumulator is inferred here.

## Constructor separation from unboxed Infinity

Assume $I$. For every $P:\sigma\to t$ define

$$
\begin{aligned}
E&:=\lambda n\, .\,\bot,\\
H_P&:=\lambda b A n\, .\,
(n=0\land Pb)\lor\exists m\, .\,Nm\land n=sm\land Am,\\
O_P(u)&:=(uH_P)E.
\end{aligned}
$$

These are Church applications, not applications of a sequence recursion theorem.
Infinity gives

$$
\begin{aligned}
(O_P(\epsilon))n&\leftrightarrow\bot,\\
(O_P(\operatorname{cons}(b,u)))0&\leftrightarrow Pb,\\
Nn&\to\bigl((O_P(\operatorname{cons}(b,u)))(sn)\leftrightarrow(O_P(u))n\bigr).
\end{aligned}
$$

At zero, the predecessor alternative is impossible. At a natural successor,
the zero alternative is impossible and successor injectivity identifies the
predecessor. Only ordinary biconditionals are needed.

Write $u\sim v$ for agreement of all observations at natural positions:

$$\forall P^{\sigma\to t}n^\nu\, .\,
Nn\to\bigl((O_P(u))n\leftrightarrow(O_P(v))n\bigr).$$

Prove by induction on $u$ that
$\operatorname{Seq}(u)\to\forall v\, .\,\operatorname{Seq}(v)\land u\sim v\to u=v$.
Every generated $v$ is empty or a cons of a generated tail: this unfolding
fact follows from the least inductive property without any separation assumption.

- At $u=\epsilon$, a nonempty $v$ is excluded by the observation of
  $P=\lambda x\, .\,\top$ at zero.
- At $u=\operatorname{cons}(b,r)$, the same observation excludes empty $v$.
  Write $v=\operatorname{cons}(c,q)$ with $\operatorname{Seq}(q)$.
  Zero-position agreement gives $\forall P\, .\,Pb\leftrightarrow Pc$;
  $P=\lambda x\, .\,b=x$ yields $b=c$. Successor-position agreement gives
  $r\sim q$, and the induction hypothesis gives $r=q$, hence $u=v$.

If $\operatorname{cons}(b,r)=\operatorname{cons}(c,q)$, equality gives all
observation agreements. Zero positions give $b=c$, successor positions give
$r\sim q$, and the preceding induction gives $r=q$ when both tails are generated.
The all-true property at zero also proves that a cons is not empty, even for an
arbitrary tail. Thus $I$ proves the required constructor laws. This is the
noncircular step checked in `Certified/ChurchSequences.lean`.

## Relational recursion

Fix $a:\tau$ and $g:\sigma\to\tau\to\tau$. Let $S$ be the least relation
containing $(\epsilon,a)$ and closed under

$$S(u,y)\to S(\operatorname{cons}(b,u),(gb)y).$$

It is defined by universal quantification over all such closed relations.
Without Infinity, minimality gives its base and closure laws, graph support
$S(u,y)\to\operatorname{Seq}(u)$, and the unfolding equation

$$S(u,y)\leftrightarrow
(u=\epsilon\land y=a)\lor
\exists brx\, .\,
u=\operatorname{cons}(b,r)\land S(r,x)\land y=(gb)x.$$

For unfolding, the right-hand relation is included in $S$ by closure, and that
inclusion makes it itself closed; apply minimality. Induction gives totality
on generated sequences.

Under $I$, prove uniqueness by induction on the input sequence. At $\epsilon$,
constructor disjointness excludes the second unfolding alternative, so the
output is $a$. At $\operatorname{cons}(b,r)$, disjointness excludes the first
alternative. Graph support and constructor injectivity identify any generated
predecessor as $r$ and its prefix as $b$; uniqueness at $r$ identifies the
recursive output, and hence the new output. We have proved in C

$$I\to U,\qquad
U:=\forall uxy\, .\,S(u,x)\land S(u,y)\to x=y.$$

## Functional recursion

Assume $\Box I$. Necessitation of the conditional theorem $I\to U$, followed
by K, gives $\Box U$.

Independently of Infinity, $S(u,y)\to\Box S(u,y)$: the relation
$\lambda uy\, .\,\Box S(u,y)$ contains the base pair and is closed, by
necessitating the logical base and closure theorems for $S$. Apply minimality.

Writing $\tau=\rho_1\to\cdots\to\rho_k\to t$, define

$$f:=\lambda u\lambda\vec z\, .\,\forall y^\tau\, .\,S(u,y)\to y(\vec z).$$

If $S(u,y)$, persistence and necessary functionality give
$\Box\forall\vec z\, .\,y(\vec z)\leftrightarrow(fu)(\vec z)$.
Intensionality gives $fu=y$. Thus $f\epsilon=a$. For generated $u$, totality
supplies $y$ with $S(u,y)$; closure gives
$S(\operatorname{cons}(b,u),(gb)y)$, hence

$$f(\operatorname{cons}(b,u))=(gb)y=(gb)(fu).$$

The case $\tau=t$ uses the empty argument tuple. No Infinity at $\sigma$ or
$\tau$, choice, Barcan, rigid comprehension, or general extensionality is needed.
The cons equation is only asserted for generated tails.

**Verification status.** The constructor proof has dedicated Lean checks. The full
recursion implication has this mathematical proof and a formal Lean statement;
no Lean derivation certificate for that implication is claimed.
