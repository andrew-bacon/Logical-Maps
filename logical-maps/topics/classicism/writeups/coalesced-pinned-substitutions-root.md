# Coalesced sum: interpretation and substitution arrows, finitely pinned root

Cian Dorr suggested this variant of coalesced-pinned-interpretations-root
on 19 October 2026, and Claude Opus 5.5 (Anthropic) wrote the verification.
The extra arrows make Actuality fail, as in the finitely pinned model on all
maps, while Maximalism and BF still hold. No second reader has checked it,
and no Lean verification is claimed.

## The construction

Everything is as in coalesced-pinned-interpretations-root, except that $W_0$
has more arrows to itself.

- **Substitutions.** For every type-preserving map $f$ of the constants of
  $\Sigma^+$ to themselves there is an arrow $f:W_0\to W_0$. The identity map
  is $1_{W_0}$.
- **Composition.** Maps compose as functions, and
  $\langle V,I\rangle\circ f:=\langle V,I\circ f\rangle$.
- **Individuals.** $f$ acts on the individuals at $W_0$, the individual
  constants, as it does on constants.
- **Pinning.** An entity pinned down by a finite $S$ takes the same value at
  two arrows into the same object if they agree on $S$. For arrows
  $\langle V,I\rangle$ that means $I{\restriction}S=I'{\restriction}S$; for
  maps it means $f{\restriction}S=f'{\restriction}S$.
- **Landing.** Transports along every $\langle V,I\rangle$ lie in the
  component domains, as before.

**Transport along a map keeps an entity in the domain.** Let $F$ be pinned
down by $S$.

- $f\cdot F$ is pinned down by $f(S)$: if $k$ and $k'$ agree on $f(S)$,
  then $k\circ f$ and $k'\circ f$ agree on $S$.
- Its transports are transports of $F$:
  $\langle V,I\rangle\cdot(f\cdot F)=\langle V,I\circ f\rangle\cdot F$, so
  they land.

**The entities $\hat c$.** Give $\hat c$ the empty extension at every map,
in addition to its values at the arrows $\langle V,I\rangle$ as before. Then
$f\cdot\hat c=\widehat{f(c)}$:

- at $\langle V,I\rangle$ both sides are the extension of $I(f(c))$;
- at a map $g$ both are empty.

The argument that this is a model of C is the same as before. The
denotation of a term with parameters pinned down by $S$ is pinned down by
$S$, because at a map $f$ it is computed at $W_0$ from $f\cdot\bar P$, which
depends only on $f{\restriction}S$. Transport commutes with the operations,
so denotations land.

## Actuality fails

Let $p$ be a true proposition pinned down by a finite $S$. Every map fixing
$S$ pointwise agrees with the identity on $S$, so it lies in $p$. Take a
constant $c\notin S$, and let $q$ be the set of maps fixing $S\cup\{c\}$
pointwise.

- $q$ is in the domain. It is pinned down by $S\cup\{c\}$, and its
  transports along the arrows $\langle V,I\rangle$ are empty, so they land.
- $q$ is true, since it contains the identity.
- $p$ does not entail $q$: a map fixing $S$ and moving $c$ is in $p$ but not
  in $q$.

So no truth entails every truth.

## BF holds at every type

Take the form $\Diamond\exists x\,.\,Fx\to\exists x\,.\,\Diamond Fx$, with
$F$ pinned down by a finite $S$.

- **A witness at an arrow $\langle V,I\rangle$.** This is handled as in
  coalesced-pinned-interpretations-root, by a fresh constant $c$ with
  $I'(c)=y$.
- **A witness $y$ at a map $f$.** Here $y$ is an entity at $W_0$, pinned down
  by some finite $S_y$.
  1. Let $g$ be a map sending $S_y$ to fresh constants outside $S$.
  2. Let $f'$ agree with $f$ on $S$ and send those fresh constants back, so
     that $f'\circ g$ fixes $S_y$ pointwise.
  3. Then $f'\cdot(g\cdot y)=(f'\circ g)\cdot y=y$, by pinning.
  4. $f'$ agrees with $f$ on $S$, so $F$ holds at $f'$ of
     $y=f'\cdot(g\cdot y)$.
  5. Hence $\Diamond F(g\cdot y)$.

## Maximalism and Possibility+

The arguments of coalesced-pinned-interpretations-root use only the arrows
$\langle V,I\rangle$, so they carry over unchanged. Maximalism (for $\Sigma$
and pure) and Possibility+ (for $\Sigma$ and pure) hold.
