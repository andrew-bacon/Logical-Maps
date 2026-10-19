# Coalesced sum: interpretation arrows into every component object, finitely pinned root

Cian Dorr gave this construction on 19 October 2026, to show that
Maximalist Classicism is consistent with BF. In the same discussion Claude
Opus 5.5 (Anthropic) added a condition on the domains: transports must land
in the component domains. This write-up gives the verification. No second
reader has checked it, and no Lean verification is claimed.

## Why the existing coalesced sums fail BF

In a coalesced sum (*Classicism*, Appendix E), every arrow from the root
into a component factors through a single distinguished arrow, and a root
entity may have any component parts. So any component that fails BF at its
root makes BF fail at the coalesced root. The component's counterexample
becomes a component part of a root entity, as in the group's argument
barcan-t-component. Maximalism needs such components, since the negation of
BF is consistent with C.

The construction below replaces the distinguished arrows. The root gets an
arrow into every object of every component, one for each interpretation of a
large signature. Its domains are pinned down by finite sets of constants,
just as the finitely pinned models of Appendix D are pinned down by finite
sets of individuals.

## The construction

- **Components.** Fix a set $A$ of action models complete for C($\Sigma$),
  with disjoint objects and arrows. Every $\Sigma$-sentence consistent with
  C($\Sigma$) is true at the root of some model in $A$ under some
  interpretation of $\Sigma$.
- **Signature.** Fix $\Sigma^+\supseteq\Sigma$ with countably infinitely many
  constants of every type.
- **Arrows.** Add an object $W_0$. The arrows out of $W_0$ are its identity
  and the pairs $\langle V,I\rangle$, for $V$ an object of a model in $A$ and
  $I$ an interpretation of $\Sigma^+$ at $V$, giving each constant of type
  $\tau$ an entity of type $\tau$ at $V$. No arrow enters $W_0$ except its
  identity.
- **Composition.** For an arrow $k:V\to V'$ of a component,
  $k\circ\langle V,I\rangle:=\langle V',k\cdot I\rangle$, transporting each
  constant's interpretation. This is associative because transport is
  functorial.
- **Individuals.** The individuals at $W_0$ are the individual constants of
  $\Sigma^+$, and $\langle V,I\rangle$ sends $c$ to $I(c)$.
- **Domains at $W_0$.** An entity at $W_0$ of a relational type is an
  intension $F$, assigning to each arrow out of $W_0$ a set of tuples of
  entities at its target, subject to two conditions:
  1. *Finite pinning.* For some finite $S\subseteq\Sigma^+$, two arrows
     $\langle V,I\rangle$ and $\langle V,I'\rangle$ into the same object with
     $I{\restriction}S=I'{\restriction}S$ give $F$ the same value. The
     identity is the only arrow into $W_0$, so its value is unconstrained.
  2. *Landing.* For every arrow $h=\langle V,I\rangle$, the transport $h\cdot
     F$, the intension $k\mapsto F_{k\circ h}$ over the arrows out of $V$, is
     an element of $V$'s domain in its component.

  The types are well-founded, so this defines the domains by recursion on
  the type.
- **Evaluation point.** $1_{W_0}$.
- **Interpretation of $\Sigma$.** Each constant $c\in\Sigma$ denotes
  $\hat c$, defined below.

Without the landing condition the structure would not be an action model.
For instance, $\{\langle V',I'\rangle : I'(c)\in B_{V'}\}$, for an arbitrary
assignment $B$ of sets of individuals to objects, is pinned down by $\{c\}$.
But its transport along $\langle V,I\rangle$ is the proposition that $I(c)$
has the codomain property $B$, which need not be in the component's domain,
for instance when the component is symmetric.

## The entities $\hat c$

For a constant $c$ of type $\sigma$, let $\hat c$ be the following.

- If $\sigma=e$, $\hat c$ is $c$ itself.
- If $\sigma$ is relational, $\hat c_{\langle V',I'\rangle}$ is the extension
  of $I'(c)$ at $1_{V'}$, and $\hat c_{1_{W_0}}:=\emptyset$.

Then $\langle V,I\rangle\cdot\hat c=I(c)$:

$$(\langle V,I\rangle\cdot\hat c)_k=\hat c_{\langle V',k\cdot I\rangle}=(k\cdot I(c))_{1_{V'}}=I(c)_k.$$

So $\hat c$ satisfies the landing condition, and it is pinned down by
$\{c\}$. Hence $\hat c\in D_\sigma(W_0)$.

## It is a model of C

The argument follows *Classicism*, Proposition D.4, together with the
treatment of the root in Appendix E. Closed formulas are evaluated at an
arrow by evaluating at its target with transported parameters. So what has
to be shown is that every term with parameters from the domains denotes an
element of the domains. Let $t$ be such a term, with parameters $\bar P$
pinned down by finite sets whose union is $S$.

1. **Pinning.** The value of $t$'s denotation at $\langle V,I\rangle$ is
   computed in $V$'s component from the transported parameters $\langle
   V,I\rangle\cdot\bar P$. These depend on $I$ only through
   $I{\restriction}S$. So the denotation is pinned down by $S$.
2. **Landing.** Transport commutes with the operations of the language. So
   $\langle V,I\rangle\cdot\llbracket t\rrbracket(\bar P)$ is the denotation
   in $V$'s component of $t$ with the parameters $\langle V,I\rangle\cdot\bar
   P$. That lies in $V$'s domain, because the component is a model of C.
3. **At $W_0$ itself.** The value at the identity is the set of tuples of
   $W_0$-entities satisfying the formula at $W_0$. Quantifiers there range
   over $D(W_0)$, and no condition constrains this value.

Application is the special case $h\cdot(Fa)=(h\cdot F)(h\cdot a)$. The
axioms of C hold at $W_0$ because, as in every action model, denotations are
computed extensionally on intensions. The worlds other than $W_0$ are worlds
of the components, which are models of C.

## BF holds at every type

Take the form $\Diamond\exists x\,.\,Fx\to\exists x\,.\,\Diamond Fx$. Let
$F$ be of type $\sigma\to t$, pinned down by a finite $S$, with
$\Diamond\exists x\,.\,Fx$ true at $W_0$.

- **The witness is at the identity.** Then $\exists x\,.\,Fx$ holds already,
  and $Fx$ implies $\Diamond Fx$.
- **The witness is at some $\langle V,I\rangle$.** Then $y\in F_{\langle
  V,I\rangle}$ for some $y$ of type $\sigma$ at $V$.
  1. Choose a constant $c$ of type $\sigma$ outside $S$; infinitely many are
     available.
  2. Let $I'$ agree with $I$ except that $I'(c)=y$.
  3. Then $\langle V,I'\rangle$ agrees with $\langle V,I\rangle$ on $S$, so
     $F_{\langle V,I'\rangle}=F_{\langle V,I\rangle}\ni y=\langle
     V,I'\rangle\cdot\hat c$.
  4. So $F\hat c$ holds at $\langle V,I'\rangle$, and $\Diamond F\hat c$
     holds at $W_0$.

This is the criterion that gives BF in the all-maps finitely pinned model.
Every arrow agrees on a finite set with one under which a fresh constant is
mapped wherever one likes.

□BF fails, as it must, since Maximalism is incompatible with it (recorded
results). The components that refute BF are seen from $W_0$.

## Maximalism holds, for $\Sigma$ and in the pure form

A closed $\Sigma$-sentence holds at $\langle V,I\rangle$ iff it holds at $V$
in its component under $I{\restriction}\Sigma$, the constants of $\Sigma$
denoting the $\hat c$. Let $\phi$ be consistent with C($\Sigma$). Then $\phi$
holds at the root $V$ of some model in $A$ under some interpretation of
$\Sigma$. Extend that interpretation arbitrarily to $\Sigma^+$, giving $I$;
then $\phi$ holds at $\langle V,I\rangle$, so $\Diamond\phi$ holds at $W_0$.
This is Maximalism for $\Sigma$ in its possibility form, which is equivalent
in C to the official form. The pure form follows.

## Other verdicts

- **Actuality.** $\{1_{W_0}\}$ is pinned down by $\emptyset$, and its
  transports are empty. It is a true proposition that entails every truth.
- **Relational Choice.** As at the other coalesced roots, a choice at the
  identity with empty component parts is in the domain.
- **Boxed principles.** The group's argument that every pure sentence
  consistent with C is possible at the root refutes □Vicinity, □Weakly
  Inextensible Comprehension and □Transversal here too.

The map derives much more. Inextensible Comprehension holds, from Actuality
with BF, and so do the signature principles that follow from Maximalism for
$\Sigma$. None of the group's arguments that transfer a counterexample
through a distinguished arrow applies, so this model's other verdicts at the
root need arguments of their own.
