# Boolean Completeness implies Numerical Rigidity

Mathematical attribution: Zachary Goodsell, *Arithmetic is Determinate* and
*Arithmetic is Necessary*. The latter supplies the countable-completeness proof
(Lemmas 3 and 8; locators refer to the 5 June 2024 draft).
The name and related Church-numeral formulation come from Andrew Bacon and Jin
Zeng, *A Theory of Necessities* (author draft, p. 14).
Transcription and Lean formalization: OpenAI Codex (GPT-6), prompted by Andrew
Bacon, 29 October 2026.

## Statement and convention

At any admitted type $\sigma$, put $\nu=(\sigma t)t$ and let $N$ be
$\operatorname{FiniteCardinality}_\sigma$, the impredicative closure of the
empty-property cardinality under $\operatorname{Suc}_\sigma$. Numerical Rigidity
is the schema

$$
\forall X^{\nu t}\, .\,
 (\forall n^\nu\, .\,Nn\to\Box Xn)
 \leftrightarrow \Box(\forall n^\nu\, .\,Nn\to Xn).
$$

The quantified property is **being a number**. This does not say that a finite
cardinality quantifier gives an unchanging answer on an arbitrary varying
property. No Infinity, injectivity of successor, distinctness of numerals,
Choice, BF, or necessary distinctness is assumed.

The distinction between the map's two rigidity conventions matters. Persistence
of $N$ is a theorem of C. Numerical Rigidity is therefore equivalent to
$\operatorname{WeaklyRigid}(N)$. Its boxed form is equivalent to
$\operatorname{Rigid}(N)$. The two map nodes preserve this distinction:

| Premise | Conclusion |
| --- | --- |
| Boolean Completeness | Numerical Rigidity |
| Countable Boolean Completeness | Numerical Rigidity |
| □Boolean Completeness | □Numerical Rigidity |
| □Countable Boolean Completeness | □Numerical Rigidity |
| Rigid Comprehension, unboxed | □Numerical Rigidity |

All are type schemata: the parameter $\sigma$ is outside object quantification
and outside boxes. Completeness is used at $\nu t$; countability is measured
using numbers at the same $\sigma$. The direct RC argument uses RC at $\nu t$.

## Singleton-supremum proof

The Lean proof factors through an arbitrary relational carrier $\nu$, seed $z$
and successor $s:\nu\to\nu$, with

$$Nn:=\forall X^{\nu t}\, .\,(Xz\land\forall m(Xm\to X(sm)))\to Xn.$$

Induction gives $Nn\to\Box Nn$. Form the family
$S:=\lambda Y^{\nu t}\, .\,\exists n(Nn\land Y=\{n\})$.
It is countable over $N$, witnessed by $R(Y,n):=(Y=\{n\})$.
Let $B$ be its least upper bound. An upper bound $X$ of $S$ is exactly a
property with $\forall n(Nn\to\Box Xn)$. In particular $B$ has this property.
Successor closure of $N$ makes $\lambda n.B(sn)$ another upper bound, so
$\Box\forall n(Bn\to B(sn))$. Also $\Box Bz$.
Necessitated induction yields $N\le B$. If $X$ is any upper bound, minimality
gives $B\le X$, hence $N\le X$, the required restricted-Barcan direction.
The converse follows from persistence of $N$, Converse Barcan and K.

Only the supremum of $S$ is needed. Full Boolean completeness provides it;
countable Boolean completeness also provides it. Necessitating the resulting
implication gives the boxed consequence **from the boxed premise**.

## Why unboxed RC suffices for the stronger form

Let $R$ be a rigid coextensive representative of $N$. Persistence of $R$ gives
$\Box Rz$. Since $N$ is successor closed, coextension and persistence give
$\forall n(Rn\to\Box R(sn))$. Inextensibility of $R$ upgrades this to
$\Box\forall n(Rn\to R(sn))$. Necessitated induction gives $N\le R$.
Conversely, persistence of $N$ and coextension give
$\forall n(Rn\to\Box Nn)$; inextensibility of $R$ yields $R\le N$.
Antisymmetry gives $N=R$, hence $\operatorname{Rigid}(N)$.
No necessitation of the RC hypothesis occurs.

This is the RC route associated with Goodsell's earlier arithmetic development;
the displayed proof spells out its adaptation to the map's stronger definition
of rigidity. The 2024 paper replaces RC by countable Boolean completeness for
the local restricted-Barcan conclusion.

## Church numerals and the CH application

For a relational type $\alpha$, use the Church carrier
$\chi=(\alpha\alpha)\alpha\alpha$, zero $\lambda f.\lambda x.x$, and
successor $\lambda n.\lambda f.\lambda x.f((nf)x)$.
Its inductive closure is the Church-numeral property. The same generic proof
gives its local rigidity from Boolean completeness at $\chi t$, and strong
rigidity from boxed completeness. This instance is also formalized. Here
$\alpha\ne e$ ensures every function type is admitted; taking $\alpha=t$
gives the familiar proposition-operator case. Bacon and Zeng's formulation
uses their operator $L^*$; the present formalization uses Classicism's box.
Neither an identification of the two number representations nor an equivalence
between their rigidity principles is assumed.

Likewise, choosing seed $\lambda X.\top$ and the cardinal successor gives the
at-least-number property used in the separate CH development. The generic
result supplies its rigidity from the appropriate unboxed RC instance, or from
boxed completeness. This PR is independent of that development: it does not
certify its forcing argument or assert that the whole CH development is ready
for publication.

## Native Lean integration

The shallow proofs are in `Classicism/Results/NumericalRigidity/`; the principle
definitions are in `Classicism/Principles/NumericalRigidity.lean`. Each theorem
is checked for the Equivalence restriction and the relational type system, then
translated into a kernel-checked object-language derivation in C-minus by the
unchanged translator. `Classicism/Certified/NumericalRigidity/` contains these
derivations, quotations, closed-type checks and schema entailments.
`Classicism/MapNumericalRigidity.lean` inhabits the statements generated from
the six map records at every admitted signature.

Reproduce the focused certificate build with
`lake build Classicism.MapNumericalRigidity` from the topic's `lean/` directory.
The full map audit is `python3 scripts/pmap.py lean-check classicism --update`
from `logical-maps/`. Only that native auditor sets the map's verified fields.
The source includes no `sorry` or additional axioms and changes no checker.

## References

- Bacon, Andrew, and Jin Zeng (2022). [A Theory of Necessities](https://doi.org/10.1007/s10992-021-09617-5). *Journal of Philosophical Logic* 51, 151–199. Numerical Rigidity: author draft p. 14.
- Goodsell, Zachary (2022; first published 2021). [Arithmetic is Determinate](https://doi.org/10.1007/s10992-021-09613-9). *Journal of Philosophical Logic* 51, 127–150. Higher-order development: Theorem 13.
- Goodsell, Zachary (2024). [Arithmetic is Necessary](https://doi.org/10.1007/s10992-024-09760-9). *Journal of Philosophical Logic* 53, 1145–1159. Lemmas 3 and 8; draft dated 5 June 2024.
