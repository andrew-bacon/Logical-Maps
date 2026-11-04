# Boxed Church Numeral Infinity implies functional recursion

Andrew Bacon's 2023 least-relation construction, with explicit modal hypotheses
and a completed uniqueness proof by Codex (OpenAI), prompted by Andrew Bacon,
2 November 2026. Background: Bacon, *Notes for Zach* (25 March 2023), §1, pp. 1–3.

Work in C at relational types $\alpha,\tau$. Write $\nu,0,s,N,I$ for the Church
numeral type, zero, successor, least inductive property and Church Numeral
Infinity at $\alpha$. Assume $\Box I$. All notation is defined in the
Background page *Church numerals and sequences*. Write $R(n,x)$ for $(Rn)x$.

Fix $a:\tau$ and $g:\tau\to\tau$. Define

$$
\begin{aligned}
\operatorname{Closed}(R)&:=R(0,a)\land
 \forall ny\, .\,R(n,y)\to R(sn,gy),\\
S&:=\lambda nx\, .\,\forall R^{\nu\to\tau\to t}\, .\,
 \operatorname{Closed}(R)\to R(n,x).
\end{aligned}
$$

**Elementary properties (no Infinity).** The definition gives $S(0,a)$,
$S(n,x)\to S(sn,gx)$ and inclusion of $S$ in every closed relation.
Comparison with $\lambda nx\, .\,Nn$ gives $S(n,x)\to Nn$.
Induction gives $Nn\to\exists x\, .\,S(n,x)$.

The graph unfolds as

$$
S(n,x)\leftrightarrow
(n=0\land x=a)\lor\exists my\, .\,
n=sm\land S(m,y)\land x=gy.
$$

Let $T$ be the right-hand relation. Closure of $S$ gives $T\subseteq S$.
That inclusion makes $T$ closed: its successor clause can use $S(n,x)$ whenever
$T(n,x)$. Minimality gives $S\subseteq T$.

**Functionality (unboxed Infinity).** Induct on $n$ to prove that, if $Nn$,
any two $S$-outputs at $n$ coincide. At zero, unfolding leaves only $a$:
the predecessor alternative contradicts $Nm\to sm\ne0$, since graph support
gives $Nm$. At $sn$, the zero alternative is excluded; each output is $gy$
from a natural predecessor $m$ with $sm=sn$. Injectivity makes $m=n$, and
the induction hypothesis makes $y$ unique. Graph support therefore gives

$$\mathsf C\vdash I\to U,
\qquad U:=\forall nxy\, .\,S(n,x)\land S(n,y)\to x=y.$$

Necessitate this conditional theorem and apply K to $\Box I$ to obtain $\Box U$.
Neither unboxed Infinity nor a derivation depending on it is silently necessitated.

**Persistence (no Infinity).** Let $P(n,x):=\Box S(n,x)$.
The logical base and closure theorems for $S$ can be necessitated, so $P$ is
closed. Minimality gives $S\subseteq P$, hence $S(n,x)\to\Box S(n,x)$.
The parameters $a,g$ are arbitrary; no rigidity of their extensions is assumed.

**Conversion.** Write $\tau=\rho_1\to\cdots\to\rho_k\to t$ and put

$$f:=\lambda n\lambda\vec z\, .\,\forall u^\tau\, .\,S(n,u)\to u(\vec z).$$

For $S(n,x)$, persistence gives $\Box S(n,x)$. Together with $\Box U$ this
gives $\Box\forall\vec z\, .\,x(\vec z)\leftrightarrow(fn)(\vec z)$:
one direction uses uniqueness, the other instantiates $u=x$.
Intensionality yields $fn=x$. This includes $\tau=t$, with the tuple empty.

Thus $S(0,a)$ gives $f0=a$. If $Nn$, choose $x$ with $S(n,x)$.
Then $fn=x$ and $S(sn,gx)$, so $f(sn)=gx=g(fn)$. The resulting principle is

$$\forall a^\tau g^{\tau\to\tau}\,\exists f^{\nu\to\tau}\, .\,
f0=a\land\forall n\, .\,Nn\to f(sn)=g(fn).$$

No choice, Barcan, rigid comprehension or unboxed Functionality is used.
The proof asserts no recursion equation or uniqueness requirement outside $N$.

**Verification update, 4 November 2026.** Codex (OpenAI), prompted by Andrew
Bacon, supplied the complete Lean derivation in `Background/ChurchRecursion.lean`.
All 22 new lemmas pass the Equivalence and relational type audits.
`Certified/ChurchRecursion.lean` checks both object-language derivations;
`Results/ChurchRecursion.lean` lifts them to every relational output type,
including propositions via the empty argument tuple. The complete entailments
compile with only `propext` and `Quot.sound` in their axiom reports.
The full Classicism build and `pmap lean-check classicism --update` also passed.
The audit marked both recursion implications `lean: verified`.
