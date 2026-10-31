# Full action models: all transformations with their natural action

Source construction: Andrew Bacon, *Substitution Structures* (2019), §4
and §5.3, especially the D^D example on p. 46 of the author-hosted draft
of 10 January 2019. Translation to relational action-model intensions and
additional verdict arguments by OpenAI Codex, prompted by Andrew Bacon,
28 October 2026. General full-model arguments cite *Classicism* §3.5 and
Appendix D separately. No Lean verification is claimed for these entries.

## Construction

Let X have at least two elements. Set M = X^X with ordinary function
composition, D_e = X, and f acting on an individual x by f(x). Propositions
are P(M), with

$$f\cdot p=\{g:g\circ f\in p\}.$$

Higher types are full M-set function spaces, restricted to the map's
relational types. Equivalently a relation is an arbitrary family of
extensions indexed by transformations; transport shifts that family by
composition and transports its arguments. Truth is evaluated at the
identity transformation. All relational constants of Σ denote top.

There is no finite-support restriction and no symmetry restriction. In
particular the natural action on X is not replaced by a trivial action on
fixed individuals. The two records take X = {0,1} and X = N. The following
basic arguments work for any X with at least two elements, in ZFC.

## Barcan fails at both e and t

For either type σ, write f_σ for its transport map. Fullness supplies a
property H_σ with extension im(f_σ) at transformation f. Every root entity
x necessarily satisfies H_σ, because f_σ(x) lies in im(f_σ).

Choose a constant transformation k with value a. At type e its image is
{a}, so an individual b distinct from a at the target does not satisfy
H_e. At type t, the identity and k are distinct, but

$$1\circ k=k\circ k=k.$$

Every proposition k·p therefore contains either both 1 and k or neither.
The proposition {1} at the target is outside the image of k_t. Thus in
both types the premise of BF is true at the identity and its conclusion
is false. At each input type the same H_σ and the constant-top property
also witness failure of Functionality; p = top witnesses failure of
Tractarianism. BF-at-e has no separate map node, so its witness is retained
in the argument for failure of the all-type schema; BF-at-t is a separate
verdict.

## B and other failures

Take p = {1}. It is true at the identity. After k it is impossible, because
no h has h composed with k equal to 1. Thus B fails. The same observation
shows that k transports both p and bottom to bottom, refuting necessary
distinctness at t; at e, k identifies distinct individuals. The repository's
unretracted-arrow argument records the t failure and derives failure of B.

The constant map is not epic (1 and k agree after k), so the existing
nonepic-strong-atomicity argument refutes the Strong Atomicity
at t (formerly named the Strong Leibniz Biconditionals). A transposition is a nonidentity returning arrow, so the existing
argument refutes Distinctness-Preserving Collapse. Consequences of these
failures are computed by the map.

## Positive verdicts and Atomicity

Fullness gives boxed Rigid Comprehension and boxed Atomicity at every
relational type. In particular D_t = P(M) has singleton atoms. These
models are not counterexamples to Atomicity. Every relational entailment
algebra is likewise a full powerset of arrow/argument tuples, so arbitrary
intersections give Boolean Completeness, at every object. The singleton
{1} is the strongest truth at the sole object; hence Actuality holds there
and at the target of every arrow, giving boxed Actuality.

The existing full-model arguments give Relational Choice (using choice in
the metatheory), and extensional fullness gives Transversal Choice.
The general argument [[no-pure-contingency-one-object]] gives
[[no-pure-contingency-r|No Pure Contingency]] for both instances: a closed
pure sentence has no parameters to transport, and every arrow has the same
codomain object. Its truth value is therefore the same after every arrow.
The model records inherit this argument through the group's
`one-object-action-model` condition; no duplicate verdict is needed. This
also supplies boxed forms via the map's recorded implications where applicable.
The entries are in ZFC: no choiceless variation is asserted.

## Why two instances

For X = {0,1}, there are four transformations and sixteen propositions.
The finite-arrows argument gives boxed Intensional Choice; the finite
propositional-domain arguments refute the infinity principles at t.
A map with a left inverse is invertible on this finite carrier.

For X = N, the individual and propositional domains are infinite. The
existing extensional-fullness arguments give the two Axioms of Infinity
and the corresponding infinity schemata. Successor has a left inverse
but is not onto. It has distinct left inverses (choose different values
at 0), separated by full propositions, so the existing retraction arguments
settle further principles, including failure of Strong Actuality. These
facts must not be transferred to the finite instance.

Both instances also satisfy boxed Intensional Choice: the general
`intensional-choice-well-ordering` argument applies because full domains
contain all codomain-dependent intensions (using ZFC). Thus this verdict
for the infinite instance does not rely on the finite-arrows argument.
Verdicts below use the corrected general arguments merged in upstream PR #23
(30 October 2026 UTC). The earlier closure counts are withdrawn: they included
consequences of the invalid Analytic Necessitism failure argument. Recompute
closure from the current source records rather than reusing that snapshot.
The executable check `checks/bacon_model_witnesses.py` exhausts the two-element
monoid's low-type witnesses; it is not a formalization of the full type hierarchy.


## Selected verdicts after map closure

| Principle | Two individuals | Natural numbers |
| --- | --- | --- |
| Boxed Rigid Comprehension | holds | holds |
| Boxed Atomicity (all relational types) | holds | holds |
| Boxed Boolean Completeness | holds | holds |
| Boxed Actuality | holds | holds |
| Boxed Intensional Choice | holds | holds |
| Boxed Relational Choice | holds | holds |
| No Pure Contingency | holds | holds |
| B; 5; necessary distinctness | fails | fails |
| BF at e; BF at t | fails | fails |
| Functionality; Tractarianism | fails | fails |
| Strong Atomicity at t | fails | fails |
| Distinctness-Preserving Collapse | fails | fails |
| Strong Actuality | holds | fails |
| Axioms of Infinity at e and t | fails | holds |
| Analytic Necessitism | holds (vacuously) | holds |
| Second-Order Analytic Necessitism | holds (vacuously) | holds |

## Analytic Necessitism: correction of 31 October 2026

Correction and the model-specific construction below by OpenAI Codex,
prompted by Andrew Bacon. The withdrawal and general replacement arguments
are due to Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, in
[upstream PR #23](https://github.com/zwlgzwlg/Logical-Maps/pull/23).
These are mathematical arguments; no new Lean verification is claimed.

The finite verdicts are vacuous: every type has a finite domain, so none
can carry a complete ordered field. For the natural-number instance, the
map now applies [[analytic-necessitism-codomain-fixed]] (and the corresponding
individual-domain argument): the group meets `one-object-action-model` and
`codomain-intensions`, and this member meets `infinitely-many-propositions`
and `infinitely-many-individuals`. The recorded conclusions are Analytic
Necessitism and Second-Order Analytic Necessitism. At type $tt$, the
replacement builds the continuum on constant intensions fixed by every arrow.

The previous negative verdict relied on
[[analytic-necessitism-unretracted-arrow]], now withdrawn. Its invalid step
was to infer $y\in A$ from $k\cdot y=k\cdot x\in A_k$ and inextensibility
of $A$. Inextensibility requires a preimage in $A$, which $x$ already
provides; it does not put every preimage into $A$. Necessary distinctness
only prohibits identifying two members, not identifying a member with an
outsider. The existence of an unretracted arrow remains correct and still
supports other verdicts, such as failure of B.

No Pure Contingency concerns closed pure sentences. It gives the necessity
of the existence of a real number structure when one exists, but moving
from $\Box\exists\mathfrak R\,\operatorname{Real}(\mathfrak R)$ to a
particular rigid, necessarily real number structure needs a further argument.
Here one can give that argument at every relational carrier type, including
$t$, rather than relying on a witness at $tt$ alone.

Fix $a\in\mathbb N$ and choose distinct subsets $E_r\subseteq\mathbb N$
indexed by $r\in\mathbb R$. For $b\in\mathbb N$, put

$$p_r^b=\{g\in M:g(b)\in E_r\}.$$

Then $h\cdot p_r^b=p_r^{h(b)}$, and for each $b$ the propositions $p_r^b$
are pairwise distinct: constant transformations distinguish any two
unequal $E_r$. At an arbitrary relational type
$\sigma=\sigma_1\cdots\sigma_m t$, including $m=0$, let $z_r^b$ be the
intension with value the full argument domain at $g$ if $g(b)\in E_r$,
and the empty extension otherwise. All argument domains are nonempty, so
these are again pairwise distinct for fixed $b$, and
$h\cdot z_r^b=z_r^{h(b)}$.

For each $k$-ary relation $T\subseteq\mathbb R^k$, fullness supplies the
intension $S_T^b$ whose extension at $g$ is

$$\{(z_{r_1}^{g(b)},\ldots,z_{r_k}^{g(b)}):(r_1,\ldots,r_k)\in T\}.$$

Its transport along $h$ is $S_T^{h(b)}$. At every arrow, these extensions
are exactly the images of the earlier extensions under transport. Thus
they are persistent and inextensible, including after every further arrow.
Use the carrier $S_{\mathbb R}^a$, the usual real order, sum, product and
natural-number relations $S_T^a$, and $z_0^a,z_1^a$. At every arrow the
structure is a copy of the full real field, so is complete for every
internal subproperty; its carrier members remain distinct. It is a rigid,
necessarily real number structure at $\sigma$.

For each arity $k$, take the intension with extension
$\{S_T^{g(a)}:T\subseteq\mathbb R^k\}$ at $g$. Transport again carries its
extension exactly onto the next extension, making this a rigid property
of rigid relations. Every relation on the carrier at any arrow determines
a subset of $\mathbb R^k$, and hence agrees there with one of these members.
These are represented powers of every finite arity. At type $e$ the
antecedent is false: the individual domain is countable and fullness
precludes a countable complete ordered field. This verifies both schemas
for this particular model without asserting that the general replacement's
single-type construction by itself establishes all type instances.

Signature verdicts are relative to the explicitly fixed interpretation of
all constants as top; they are not claims about the paper's separate
fundamental-language expansion.
