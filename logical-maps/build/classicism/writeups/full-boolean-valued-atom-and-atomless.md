# Full Boolean-valued model: one atom and an atomless component

This model satisfies C5, boxed BF, Functional Choice, Plenitude, and Actuality,
but fails Atomicity already at type $t$. It therefore refutes

$$
\mathrm{BF}+\mathrm{Functional\ Choice}\ \Longrightarrow\ \mathrm{Atomicity}.
$$

The underlying construction is Andrew Bacon's, *Could the truths of
mathematics have been different?*, draft of 9 October 2025, online appendix
§B.2, pp. 7–9 (PDF pp. 41–43). This record specializes the individual domain
to a singleton. Bacon works in ZFC + CH with the algebra adding $\aleph_2$
Cohen reals, so that CH is contingent. The record keeps his algebra when CH
holds and uses its dual when CH fails, so CH is contingent in ZFC alone
(Section 8).

The choice and atomicity verifications below were written out by OpenAI
Codex (GPT-6), 27 September 2026. The comparison with the recorded
Plenitude countermodel is in Section 7.

## 1. Interpretation and designated truth

Work in ZFC. Let $A$ be a nontrivial complete atomless Boolean algebra.
Sections 1–7 hold for every such $A$. The record fixes it by cases on the
continuum hypothesis in $V$:

$$
A:=\begin{cases}\operatorname{RO}(\operatorname{Add}(\omega,\omega_2))&\text{if CH holds},\\
\operatorname{RO}(\operatorname{Col}(\omega_1,2^{\aleph_0})\times\operatorname{Add}(\omega,1))&\text{if CH fails.}\end{cases}
$$

In both cases forcing with $A$ adds a Cohen real, which the failures of
□Boolean Completeness (type $t$), □Countable Boolean Completeness and
Analytic Necessitism use (until 24 October 2026 $A$ was the regular open
algebra of the real line, a single Cohen real). Put

$$
B=\mathbf{2}\times A,\qquad a=(1,0_A),\qquad b=(0,1_A).
$$

Thus $a$ is the sole atom of $B$, while the interval below $b$ is atomless.
Both $a$ and $b$ are nonzero, and $a<1_B$.

Use exactly the map's relational type system:

$$
D_e=\{*\},\qquad D_t=B,\qquad
D_{\sigma\to\tau}=D_\tau^{D_\sigma}\quad(\tau\ne e).
$$

Every admitted function domain contains all set-functions of the indicated
type. Application and lambda abstraction have their ordinary interpretations.
Connectives are the Boolean operations of $B$, and equality at every type is

$$
\llbracket x=y\rrbracket=
\begin{cases}
1_B&x=y\text{ as elements of the domain},\\
0_B&x\ne y.
\end{cases}
$$

Interpret quantifiers by

$$
\llbracket\forall x^\sigma\,\varphi(x)\rrbracket
=\bigwedge_{d\in D_\sigma}\llbracket\varphi(d)\rrbracket,
\qquad
\llbracket\exists x^\sigma\,\varphi(x)\rrbracket
=\bigvee_{d\in D_\sigma}\llbracket\varphi(d)\rrbracket.
$$

Completeness of $B$ makes these operations available; full function domains
contain the quantifier operations and all lambda denotations.

Let $\pi:B\to\mathbf{2}$ be first-coordinate projection. A formula is
**true at the designated evaluation** precisely when its value $c$ satisfies
$\pi(c)=1$, equivalently $a\le c$. The projection preserves Boolean
operations and arbitrary meets and joins. A universal formula is therefore
true exactly when every instance is true, and an existential formula is
true exactly when some instance is true. Designated truth must be
distinguished from Boolean value $1_B$.

## 2. Verification of C

Every H-theorem has Boolean value $1_B$ under every assignment.
Propositional axioms are valid in a Boolean algebra. Universal instantiation
and existential generalization follow from the properties of meets and joins.
Reflexivity and Leibniz's law hold for crisp equality. Beta and eta conversion
are exact identities of set-function denotations.

Modus ponens preserves value $1_B$. The quantified inference rules are sound:
if $x$ is not free in $P$ and every instance of $P\to Q(x)$ has value $1_B$,
then $\llbracket P\rrbracket\le\llbracket Q(d)\rrbracket$ for every $d$, hence
$\llbracket P\rrbracket\le\bigwedge_d\llbracket Q(d)\rrbracket$. The existential
rule follows dually.

If H proves $P\leftrightarrow Q$, their Boolean values are equal under every
assignment, since $u\leftrightarrow v=1_B$ exactly when $u=v$. Their lambda
abstractions are the same functions, validating Logical Equivalence. Closure
under H's rules then validates C. No optional premise is promoted to an
identity or necessitated in this argument.

Preservation of arbitrary meets and joins by $\pi$ also makes H's quantified
rules truth-preserving at the designated evaluation. Thus the construction
is a model for the unboxed premises as well as for the standing logic.

## 3. BF and C5

Because $\Box p$ is $p=\top$,

$$
\llbracket\Box p\rrbracket=
\begin{cases}
1_B&\llbracket p\rrbracket=1_B,\\
0_B&\llbracket p\rrbracket\ne1_B.
\end{cases}
$$

For every type $\sigma$ and $X:D_\sigma\to B$,

$$
\bigwedge_{x\in D_\sigma}\Box(Xx)
=\Box\left(\bigwedge_{x\in D_\sigma}Xx\right).
$$

Both sides are $1_B$ exactly when every $Xx=1_B$, and otherwise both are
$0_B$. Every fully closed BF instance has value $1_B$, as does its box.

Equality and distinctness have only the values $0_B$ and $1_B$, which Box
fixes. Every closed ND instance and its box therefore have value $1_B$.
In particular the model satisfies C5, the map's boxed-ND package.

## 4. Extensional fullness, Plenitude, and choice

The model is extensionally full at the designated evaluation. For any
external subset $S\subseteq D_\sigma\times D_\tau$, its characteristic
function with values $1_B$ and $0_B$, curried into the admitted relation
type $\sigma\to\tau\to t$, belongs to the domain and has extension exactly
$S$. The same argument applies at every relational arity.

This verifies Relational Choice in ZFC. Given a serial relation $U$, its
extension is a serial set-theoretic relation, because the designated
projection preserves the quantifier operations. Metatheoretic choice
supplies a functional subrelation of that extension. Extensional fullness
represents it by a relation in the domain, which is functional and contained
in $U$ at the designated evaluation. This argument also covers individual
outputs: the representing relation still has a type ending in $t$.

More generally, the same argument works for any extensionally full model
of H in ZFC. In the presence of Plenitude it yields Functional Choice,
using the decomposition in *Classicism*, §2.3:

$$
\mathrm{Functional\ Choice}\quad\Longleftrightarrow\quad
\mathrm{Relational\ Choice}\land\mathrm{Plenitude}.
$$

To verify Plenitude here, fix admitted types $\sigma,\tau$ with $\tau\ne e$,
and a relation $U$ functional at the designated evaluation. Each
$x\in D_\sigma$ has a unique $y\in D_\tau$ with $\pi((Ux)y)=1$.
These unique values define a set-function $f:D_\sigma\to D_\tau$.
Fullness puts $f$ in $D_{\sigma\to\tau}$, and preservation of meets gives

$$
\pi\left(\bigwedge_{x\in D_\sigma}(Ux)(fx)\right)=1.
$$

Thus $f$ witnesses Plenitude. Relational Choice and Plenitude give
Functional Choice at every admitted pair of types. Equivalently, one can
apply metatheoretic choice directly to the nonempty true fibres of a serial
$U$ and use fullness to include the resulting selecting operation.

These arguments establish designated truth. They do not assert that
the closed choice formulas have Boolean value $1_B$.

## 5. Actuality and the failures of Atomicity and Atomlessness

The algebraic order defined by $y=x\lor y$ is exactly the order in $B$,
with crisp Boolean truth values. Hence the map's atom predicate is true
exactly of the ordinary Boolean-algebra atoms.

The atom $a$ is true. Every true proposition $p$ has first coordinate $1$,
so $a\le p$. Therefore $a$ witnesses Actuality. Since $a$ has no nonzero
strict lower bound, it also refutes Atomlessness.

But $b\ne0_B$, and every nonzero $c\le b$ has the form $(0,c_A)$ with
$c_A>0_A$. Atomlessness of $A$ gives $0_A<d_A<c_A$, hence

$$
0_B<(0,d_A)<c.
$$

Thus no atom lies below $b$. The type-$t$ Atomicity sentence has value $0_B$,
so both Atomicity at type $t$ and the full schema fail.

Actuality itself has Boolean value exactly $a$. A candidate $c$ contributes

$$
v_c=c\land\bigwedge_{p\in B}
\left(p\to\llbracket c\le p\rrbracket\right).
$$

For $c=0_B$ this is zero. If $c$ is nonzero and not an atom, split it into
nonzero disjoint parts $d,e$ with $c=d\lor e$. Neither $c\le d$ nor
$c\le e$, so $v_c\le c\land\neg d\land\neg e=0_B$. For an atom $c$,
every factor contains $c$, so $v_c=c$. As $a$ is the sole atom,
$\bigvee_c v_c=a$. Since $a\ne1_B$, boxed Actuality has value $0_B$.

## 6. The choice calculation in the atomless component

For any nontrivial complete Boolean algebra $L$, give its full function
hierarchy the same Boolean interpretation. Consider the type-$t,t$ relation

$$
R(p,q):=(p\land q=\top)\lor(\neg p\land q=\bot).
$$

For fixed $p$, its only possibly nonzero entries are $R(p,1_L)=p$ and
$R(p,0_L)=\neg p$. They join to $1_L$ and are disjoint. With crisp
equality, both Seriality and Functionality of $R$ have value $1_L$:
the two candidate witnesses for unique existence contribute $p$ and $\neg p$.

For each function $f:L\to L$, put

$$
c_f=\bigwedge_{p\in L}R(p,f(p)).
$$

Each factor is $p$, $\neg p$, or $0_L$, according as $f(p)$ is $1_L$,
$0_L$, or neither. Hence for every $p$,

$$
c_f\le p\quad\text{or}\quad c_f\le\neg p.
$$

Any nonzero element deciding every $p$ this way is an atom: a strict
nonzero part $d<c_f$ would make both alternatives at $p=d$ impossible.
Conversely, every atom $d$ is achieved by the function choosing $1_L$
when $d\le p$ and $0_L$ otherwise. All factors contain $d$, and the
factor at $p=d$ is $d$, so the meet is exactly $d$. Therefore

$$
\llbracket\exists f\,\forall p\,R(p,f(p))\rrbracket
=\bigvee\{d\in L:d\text{ is an atom of }L\}.
$$

For the purely atomless algebra $L=A$, this value is $0_A$, even though
Seriality and Functionality have value $1_A$. Full function domains do not
justify interchanging a meet of joins with a join over selectors of meets.
In particular they do not make Plenitude or Functional Choice true in
the atomless component.

For $L=B$, the existential has value exactly $a$, achieved by selection
according to the first coordinate. This relation's Plenitude and Functional
Choice implications each have value $a$. The fully closed type-$t,t$
instances, universally quantified over relations, also have value exactly
$a$: Section 4 bounds them below by $a$, and this relation bounds them
above by $a$. Their boxes have value $0_B$, refuting both boxed schemata.

The atomless component is not a second ordinary evaluation point. A
Boolean homomorphism $h:A\to\mathbf{2}$ preserving arbitrary meets and
joins would determine an atom: put $d=\bigwedge\{p:h(p)=1\}$. Then
$h(d)=1$, so $d\ne0_A$, and for every $p$ either $d\le p$ or
$d\le\neg p$, contradicting atomlessness. The model uses the complete
projection $\pi:B\to\mathbf{2}$ at its designated evaluation, where
existential truth does have a witness.

## 7. Comparison with the recorded Plenitude countermodel

The [qualitative-contrast model](symmetric-qualitative-contrast.html), the
final construction of *Classicism*, Appendix D, p. 79, already refutes
C5 plus Plenitude implying Atomicity. It also satisfies Boolean
Completeness and Rigid Comprehension.

That construction has an extra symmetry restriction at its evaluation
object $W_0$. It is not extensionally full there. Every candidate selector
has finite support; a transposition outside that support fixes an unordered
pair while exchanging its members, and truth at $W_0$ is invariant under
the corresponding transported parameters. A functional subrelation
selecting one member of every pair is therefore excluded. The linked
write-up verifies the failure of both Relational Choice and Functional
Choice.

Thus passing to a ZFC metatheory does not upgrade that particular
Plenitude countermodel to Functional Choice. The transfer is valid when
extensional fullness is available. Bacon's Boolean-valued construction
provides that fullness at the designated atom, so the present model gives
the corresponding counterexample with Functional Choice.

## 8. The continuum hypothesis is contingent

Added 24 October 2026 by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr,
who chose the algebra by cases on CH; the argument is Bacon's (§B.2,
Lemmas B.1–B.4).

Write $\pi,\rho$ for the coordinate projections of $B=\mathbf 2\times A$.
For a sentence without $\Box$:

- its $\pi$-coordinate is its truth in the full standard model over the same
  domains, by extensional fullness at the atom (Bacon, after Lemma B.3);
- its $\rho$-coordinate is its value in $V^A$, with each domain read as a
  ground set and relations on it ranging over all names for subsets of it.

A real number structure exists on a subset of $D_t=B$ in $V$, since
$|B|\ge2^{\aleph_0}$, and in $V^A$, since $|B|\ge(2^{\aleph_0})^{V^A}$. In the
first case $|B|=\aleph_2^{\aleph_0}=\aleph_2$ by CH, which is the continuum
of $V^A$, the forcing being ccc; in the second the collapse makes
$2^{\aleph_0}$ of $V$ the $\aleph_1$ of $V^A$, and $V^A$ satisfies CH, since
adding one Cohen real after the collapse preserves it. Real number structures
are unique up to isomorphism, so with
$\varphi_{\mathrm{CH}}:=\forall\mathfrak R\, .\,\operatorname{Real}_t(\mathfrak R)\to\operatorname{CH}(\mathfrak R)$
and $\varphi_{\neg\mathrm{CH}}$ likewise,

$$
[\![\varphi_{\mathrm{CH}}]\!]=\bigl([\mathrm{CH}]^V,\ [\![\mathrm{CH}]\!]^{V^A}\bigr),\qquad
[\![\varphi_{\neg\mathrm{CH}}]\!]=\bigl([\neg\mathrm{CH}]^V,\ [\![\neg\mathrm{CH}]\!]^{V^A}\bigr).
$$

CH takes opposite values in $V$ and $V^A$, so each of these is $(1,0_A)$ or
$(0,1_A)$, and neither is $\top$. Since $\Box p$ is $p=\top$, both disjuncts
of Non-contingency of CH at type $t$ are $\bot$, and the principle fails. So
does the Necessity of Second-Order Analysis, which implies it.

The Necessity of Analysis is not settled this way: whether first-order
analytical truths can differ between $V$ and $V^A$ is not decided by ZFC (they
can if $V=L$; they cannot under projective absoluteness).

## 9. Check and attribution

Run from `logical-maps/`:

```sh
python3 topics/classicism/checks/boolean_valued_choice.py
```

The check evaluates the relation, its functional and serial conditions,
and every selector with values in the two Boolean endpoints for finite
powerset algebras with one through four atoms. It verifies that the nonzero
selector meets are exactly the atoms and that each atom's truth evaluation
supplies a selector. Other output values contribute zero. It also checks
preservation of finite joins and meets by designated atom evaluations.
These finite analogues check the Boolean calculations; no finite Boolean
algebra supplies the required nontrivial atomless component.

The underlying construction is credited to Bacon. The singleton-base
specialization, the explicit verification of the choice principles and
their Boolean values, and the comparison above are recorded by OpenAI
Codex (GPT-6), 27 September 2026. No independent checker or Lean
verification is recorded.

## Paper references

- **Proof: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Online appendix §B.2, pp. 7–9 (PDF pp. 41–43). Source of the full Boolean-valued construction with a designated atom and an atomless component. This record uses a singleton individual domain, and Bacon's algebra when CH holds and its evident dual when CH fails, so that CH is contingent without assuming CH. The explicit Functional Choice and boxed-choice calculations are supplied in the write-up.
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §§1.1–1.3 and §§2.1–2.3. Definitions of C and the principles, including Functional Choice as Plenitude plus Relational Choice.
- **Related: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, p. 79, final construction (two copies of N). The recorded qualitative-contrast model satisfies C5 and Plenitude but fails Atomicity. Its additional symmetry condition prevents extensional fullness at the evaluation object and forces both choice principles to fail.
