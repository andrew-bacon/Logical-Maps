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
the metatheory), and extensional fullness gives Transversal Choice. The
one-object argument gives No Pure Contingency; this also supplies boxed
forms via the map's recorded implications where applicable. The entries
are in ZFC: no choiceless variation is asserted.

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
Against upstream main at 6f15ef5 (28 October 2026), the map has 158
principles. Its closure settles 142 for the two-element carrier (77 true,
65 false) and 154 for the natural-number carrier (75 true, 79 false).
The remaining 16 and 4 verdicts concern the newly added self-atom
principles and remain unknown in these records. These are counts for
that map snapshot, not claims about every expressible higher-order
principle. The executable
check `checks/bacon_model_witnesses.py` exhausts the two-element monoid's
low-type witnesses; it is not a formalization of the full type hierarchy.


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
| Analytic Necessitism | holds | fails |

The finite Analytic Necessitism verdict is vacuous. The infinite failure
uses the existing full-model argument for an unretracted arrow with an
infinite domain. Signature verdicts are relative to the explicitly fixed
interpretation of all constants as top; they are not claims about the
paper's separate fundamental-language expansion.
