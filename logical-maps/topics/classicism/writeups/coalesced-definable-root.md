# Coalesced sum: interpretation arrows into every component object, definable root

Cian Dorr gave this construction on 20 October 2026, for the sentence $\Psi$
below; Claude Fable 5.1 (Anthropic) wrote the verification and the arguments.
No second reader has checked it, and no Lean verification is claimed.

## The construction

- **Components.** Fix a set $A$ of action models complete for C, with
  disjoint objects and arrows: every pure sentence consistent with C is true
  at the root of some model in $A$.
- **Signature.** $\Sigma_0=\{d\}$, with $d$ of type $e$.
- **Arrows.** Add an object $W_0$. Its arrows out are its identity and, for
  each object $V$ of a model in $A$ and each individual $a$ at $V$, an arrow
  $\langle V,a\rangle$ into $V$. No arrow enters $W_0$ except its identity.
- **Composition.** For an arrow $k:V\to V'$ of a component,
  $k\circ\langle V,a\rangle:=\langle V',k\cdot a\rangle$.
- **Individuals.** The only individual at $W_0$ is $d$, and
  $\langle V,a\rangle$ sends it to $a$.
- **Domains at $W_0$.** An entity of a relational type $\bar\sigma t$ is an
  intension $F$ over the arrows out of $W_0$ such that for some closed term
  $t$ of $\mathcal L(\Sigma_0)$, for every $\langle V,a\rangle$, the value of
  $F$ there is the extension at $1_V$ of $t$ as interpreted at $V$ with
  $d\mapsto a$. The value of $F$ at the identity is unconstrained. Write
  $F=(E,t)$ for such an entity, $E$ its value at the identity; $t$ is a
  witness, not part of the entity.
- **Evaluation point.** $1_{W_0}$.
- **Interpretation of $\Sigma$.** Every constant of $\Sigma$ denotes the top
  element of its type, the entity $(\text{everything},\lambda\bar x\,.\,\top)$.

**Landing.** The transport of $(E,t)$ along $\langle V,a\rangle$ is the
intension $k\mapsto$ (value at $\langle V',k\cdot a\rangle$) $=$ extension at
$k$ of $t$ interpreted at $V$ with $d\mapsto a$: it is the entity $t$ denotes
at $V$ under that interpretation, so it lies in $V$'s domain.

## It is a model of C

Closed formulas are evaluated at an arrow by evaluating at its target with
transported parameters. Let $s$ be a term with parameters $\bar F=(\bar
E,\bar t)$ from the root domains. At $\langle V,a\rangle$ its denotation is
computed in $V$'s component from the transported parameters, which are the
denotations of $\bar t$; so it is the denotation of the closed term
$s[\bar t/\bar F]$, uniformly in the arrow. At the identity the value is the
set of tuples of root entities satisfying the formula at $W_0$, and nothing
constrains it. So every term with parameters denotes a root entity, with
$s[\bar t/\bar F]$ as its witness. The axioms of C hold at $W_0$ because
denotations are computed extensionally on intensions, and the other worlds
are worlds of the components.

Two root entities with the same witness and different values at the
identity are distinct at $W_0$ (a root property with the right value at the
identity separates them) and identical at every component world. So ND
fails at $W_0$.

## Maximalism (pure) and Possibility+ (pure)

A closed pure sentence holds at $\langle V,a\rangle$ iff it holds at $V$.
Every pure sentence consistent with C holds at the root of some model in
$A$, so it is possible at $W_0$. For Possibility+ with one free individual
variable, a consistent $P(x)$ holds of some $a$ at some root $V$, and then
$P(d)$ holds at $\langle V,a\rangle$. With two or more variables the
antecedent, that they are distinct, is false at $W_0$, which has one
individual.

## The sentence $\Psi$

Let C5 be $\Box$ND and

$$F(p):=(\Diamond p\land\Diamond\neg p)\land\mathrm{C5}\land
\mathrm{Atomicity}\land\forall x\forall y\,.\,x=y,$$

a closed pure term of type $tt$: $p$ is contingent while C5, Atomicity and
"there is exactly one individual" hold. Let

$$\Psi:=\forall p\,.\,\neg\Diamond F(p).$$

**$\Psi$ holds at $W_0$.** Take a root proposition $p=(b,t)$ and a world
seen from $W_0$.

- At $W_0$ itself C5 fails, since ND fails there, so $p$ is not $F$.
- At a component world $w$ where C5, Atomicity and $\forall x\forall
  y\,.\,x=y$ hold, $p$ is the proposition $\llbracket t\rrbracket$. C5 gives
  BF, and $x=y\to\Box\,x=y$ is a theorem, so there is necessarily exactly
  one individual at $w$, and $t$ and the pure sentence $\forall x\,.\,t[x/d]$
  have the same truth value at every world seen from $w$: they are the same
  proposition there. By the recorded result C5 + Atomicity (type $t$) ⇒ No
  Pure Contingency, that proposition is not contingent at $w$. So $p$ is not
  $F$ at $w$.
- Everywhere else $F$ fails by its side conditions.

So $\Psi$ is consistent with Maximalist Classicism (pure). This is the
premise of the result maximalism-signature-incompatible-with-strong-possibility-pure.

**Why the extra conjunct.** Without $\forall x\forall y\,.\,x=y$ one would
need every closed sentence of $\mathcal L(\Sigma_0)$, $d$ included, to be
non-contingent where C5 and Atomicity hold. C5 + Atomicity does make the
number of individuals non-contingent, but fixing it at one reduces every
$\Sigma_0$-sentence to a pure one and costs nothing in the result.

**Why this root.** At the pinned roots the entity $\hat c$ for a constant
$c\in\Sigma^+$ of type $t$ has, at such a world, whatever value the
interpretation gives $c$, which may be contingent; so $\Psi$ fails there.
Here every root entity is definable by one closed term at every component
world, which is what $\Psi$ needs.

## BF fails

At type $e$, $\Diamond\exists x\,.\,x\ne d$ holds, but $d$ is the only root
individual. At type $t$, let $X$ be the root property denoted by

$$\lambda p\,.\,\operatorname{Atom}(p)\land\exists q\,.\,(\operatorname{Atom}(q)
\land q\ne p)\land\mathrm{C5}\land\mathrm{Atomicity}\land\forall x\forall
y\,.\,x=y.$$

$\Diamond\exists p\,.\,Xp$ holds at $W_0$: the full S5 model over the
two-element group with one individual satisfies $\exists p\,.\,Xp$, so some
component does. But no root proposition is possibly $X$: at a world where
the side conditions hold, its sentence is, as above, a non-contingent
proposition, hence (the world being S5, by C5) $\top$ or $\bot$ there, and
neither is an atom beside another atom. So $\exists p\,.\,\Diamond Xp$ fails.

## The root propositions

Two root propositions false at the identity, $(\bot,t)$ and $(\bot,t')$,
are identical iff $t\leftrightarrow t'$ holds at every object of every
model in $A$ under every interpretation of $d$, which by completeness is iff
C($\Sigma_0$) proves it; and $(\bot,t)\le(\bot,t')$ iff C($\Sigma_0$) proves
$t\to t'$. So the root propositions false at the identity form the
Lindenbaum algebra of C($\Sigma_0$), and all root propositions form that
algebra with a truth value at the identity adjoined. The Lindenbaum algebra
is countable and atomless (a consistent sentence can always be consistently
strengthened). Hence Atomicity fails at type $t$, and so at every relational
type; Boolean Completeness at type $t$ fails, a countable atomless Boolean
algebra not being complete; and Countable Boolean Completeness fails, such an
algebra not being countably complete either. Any family of root
propositions is the value at the identity of some root property, the value
at the identity being unconstrained. Atomlessness fails too, the base
proposition $(\top,\bot)$ being an atom; it also witnesses Actuality.

## Other verdicts

- **Choice.** Well-Ordering and Transversal Choice are evaluated at the
  identity alone; a well-ordering or a transversal chosen in the metatheory,
  with the term $\bot$ elsewhere, is a root entity. Relational Choice holds
  by the group's argument.
- **Strong Possibility (pure) fails.** With $a:=(\top,\bot)$, a truth
  possible only at the identity, $\Box_{\ne}p$ holds of every truth $p$, so
  $\Diamond_{\ne}P$ holds iff $P$ does; $\neg$Actuality is consistent with
  Maximalist Classicism (coalesced-pinned-substitutions-root) and false here.
- **Tame Rigidity fails** at type $e\to t$: the root property $(\{d\},\lambda
  x\,.\,\top)$ is weakly rigid at $W_0$, the only test tuple being $d$ and the
  only test properties the definable ones, which if they necessarily hold of
  $d$ hold of every individual everywhere; but its transport, the universal
  property, is weakly inextensible at a component world only where BF at type
  $e$ holds, and some component refutes that. Weakly Rigid Power fails with it.
- **Boxed principles.** The group's argument that every pure sentence
  consistent with C is possible at the root refutes □Vicinity, □Weakly
  Inextensible Comprehension and □Transversal.
- The map derives the rest: the Maximalism incompatibilities, the
  consequences of Actuality, and the signature verdicts from the top
  interpretation of $\Sigma$.
