# Classicism: candidate principles

Principles that may be added to the map later. None of them is recorded yet.
Each needs a decision before it is added, usually because it opens a family of
variants or connections. Notation follows `background.md`. Remove an entry
once it has been recorded or rejected.

## Weak variants of Rigid Power

*Added 3 October 2026.* Rigid Power (`rigid-power-r`, Goodsell 2019) says:
if $F$ is rigid, so is $P_F:=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$.
"Rigid" can be replaced by "weakly rigid" in three places:

- **H**: the hypothesis on $F$;
- **I**: the condition inside the power property, $\lambda X\, .\,\underline{\ \ }(X)\land X\le F$;
- **C**: the conclusion about that property.

Write a variant as a triple over $\{R,W\}$, so that Rigid Power is
$(R,R,R)$. Cian Dorr's "natural" reading of "Weak Rigid Power" is $(W,W,W)$.

*Recorded 10 October 2026:* $(W,W,W)$ is now `weakly-rigid-power-r` (Weakly Rigid
Power), with its necessitation. The instances at $F:=\lambda\bar x\, .\,\top$ are also
recorded: $(R,R,R)$ there is Rigid Rigidity (`rigid-rigidity-r`), and $(W,W,W)$ there
is Weakly Rigid Weak Rigidity (`weakly-rigid-weak-rigidity-r`). The other six
variants remain candidates.

### Logical relationships

Write $P^R_F$ and $P^W_F$ for the two power properties, with "rigid" and "weakly
rigid" inside.

- *Monotonicity.* With I fixed, weakening the hypothesis or strengthening the
  conclusion strengthens the principle. So $(W,I,R)$ is the strongest variant with
  that I, and $(R,I,W)$ the weakest.
- *Weakly Rigid Power is the strongest of the eight.* Take any variant with
  $H=I=W$. A weakly rigid $F$ falls under $P^W_F$, so the weak persistence of
  $P^W_F$ gives $\Box\operatorname{WeaklyRigid}(F)$; this is
  `weakly-rigid-power-implies-tame-rigidity`, and it uses only weak persistence.
  As a schema, such a variant therefore gives Tame Rigidity at every type. Under
  Tame Rigidity, H no longer matters, and C no longer matters either (by Tame
  Rigidity at the type of the power property). So $(W,W,W)\Leftrightarrow(W,W,R)$.
  - The two $I=W$ variants with $H=R$ follow by monotonicity.
  - It also gives Rigid Power (recorded), and with Tame Rigidity that gives
    $(W,R,R)$, the strongest of the $I=R$ variants. So Weakly Rigid Power implies
    all eight.
- *Inside W carries □Tame Rigidity.* A weakly rigid relation is persistent
  (Background). So in any variant with $I=W$, the conclusion makes $P^W_F$
  persistent: necessarily, every weakly rigid $X\le F$ is rigid. Conversely, given
  that, $P^W_F$ and $P^R_F$ are necessarily coextensive, hence identical. So
  $(R,W,C)$ is equivalent to $(R,R,C)$ together with □Tame Rigidity below every
  rigid relation.
  - $\lambda\bar x\, .\,\top$ is rigid in C at type $t$, and is rigid at the other
    types given □BF. So at $t$ the $I=W$ variants give □Tame Rigidity outright.
    Under □BF, $(R,W,C)\Leftrightarrow(R,R,C)+{}$□Tame Rigidity.
  - With $H=W$, BF suffices, since $\lambda\bar x\, .\,\top$ then only needs to be
    weakly rigid (`barcan-and-weakly-rigid-power-imply-necessary-tame-rigidity`).
- *Collapse.* Under Tame Rigidity at every type, H and C drop out and two classes
  remain: the $I=R$ variants, all equivalent to Rigid Power, and the $I=W$
  variants, all equivalent to Weakly Rigid Power. Under □Tame Rigidity all eight
  are equivalent to Rigid Power, by `necessary-tame-rigidity-and-rigid-power-imply-weakly-rigid-power`.
  □Rigid Comprehension and C5 both give □Tame Rigidity (recorded), and C5 gives
  □Rigid Power, so all eight hold in C5.
- *The weakest, $(R,R,W)$.* It is the weak inextensibility of $P^R_F$ at the
  evaluation point only, since persistence is free for $I=R$. Its necessitation
  gives Rigid Power (rigidity of $F$ is necessary), so with No Pure Contingency,
  as in one-object models, the two coincide.
- *Open.* Do Tame Rigidity and Rigid Power give Weakly Rigid Power? This is the
  recorded conjecture `tame-rigidity-and-rigid-power-imply-weakly-rigid-power`; a
  countermodel needs Tame Rigidity and Rigid Power without □Tame Rigidity at type
  $t$. Does $(W,R,R)$ give Tame Rigidity? Does Rigid Rigidity give Rigid Power?
  That is the recorded conjecture `rigid-rigidity-implies-rigid-power`; the
  argument offered for it assumed that rigidity is closed under conjunction,
  which fails when identity is contingent.

### What the unboxed premises give

The recorded result `necessary-bf-atomicity-and-rigid-comprehension-imply-necessary-rigid-power`
derives □Rigid Power, the full $(R,R,R)$, from boxed premises. Its argument at a
single world $v$ uses BF, Atomicity and Rigid Comprehension at $v$, and it
establishes the weak inextensibility of $P_F$ at $v$. Run once at the evaluation
point, from unboxed premises, it gives:

> **BF + Atomicity + Rigid Comprehension ⇒ $(W,R,W)$**: if $F$ is weakly rigid,
> then $\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$ is weakly rigid.

- *Hypothesis W suffices.* The argument uses $F$ only at the evaluation point,
  in two places. One is the atom lemma for $F$: below an atom, every instance of
  $F$ is identified with an actual instance. It uses only the unboxed weak
  inextensibility of $F$. The other is $X'\le F$, which uses only the persistence
  of $F$. Weak rigidity of $F$ (weakly persistent, which with weak inextensibility already gives persistence) would also do.
- *Inside R is needed.* The conclusion's persistence clause is free for $I=R$.
  For $I=W$ it would need □Tame Rigidity, but unboxed Rigid Comprehension gives
  Tame Rigidity only at the evaluation point.
- *Conclusion W only.* $\operatorname{Rigid}(P_F)$ needs weak inextensibility at
  every accessible world $v$. The argument would need an atom below the failure
  at $v$ that is possible relative to $v$, and a pull-back by Rigid Comprehension
  at $v$. Actual-world atoms and an actual rigid pull-back do not suffice without
  B, because expressing "accessible from $v$" needs a backward modality. RC + BF ⇒
  □BF is recorded, so BF at $v$ is available; Atomicity and Rigid Comprehension
  at $v$ are not.

*Settled 19 October 2026 (Claude Fable 5.1):* they do, and without BF. Lemma C.6 of Bacon's
*Could the truths of mathematics have been different?* pulls a possible rigid subrelation of $F$,
singled out by a world property (an atom at the type of the power property), back to an actual
rigid subrelation identical to it; so Atomicity at $(\bar\sigma t)t$ with Rigid Comprehension at
$\bar\sigma t$ gives $(W,R,W)$ outright, and Tame Rigidity at $(\bar\sigma t)t$, which Rigid
Comprehension gives, upgrades the conclusion to $R$: Atomicity + Rigid Comprehension ⇒ Rigid Power
(`atomicity-and-rigid-comprehension-imply-rigid-power`), and boxed, □Atomicity + □Rigid
Comprehension ⇒ □Rigid Power, without the □BF of the earlier result. Atomicity at type $t$ does not
suffice: the stitched forcing model `stitched-cohen-extension` (Barton and Goodsell) has
□Atomicity (type $t$), □Rigid Comprehension and □Relational Choice, and Rigid Power fails in it.

## Finiteness of rigid extensions

*Added 3 October 2026.* "Everything rigid has a finite extension":
$\forall F\, .\,\operatorname{Rigid}(F)\to\operatorname{Finite}(F)$, where $F$ has
a finite extension when some finite cardinality (`background.md`, Infinity) holds
of it. Variants replace Rigid by Weakly Rigid, Inextensible or Weakly
Inextensible, and perhaps Persistent.

Points to settle first:
- In the finite-support truncation model, every rigid property of individuals
  has finite extension.
- $\operatorname{Inextensible}(\top_{\sigma t})$ is equivalent to □BF at
  $\sigma$. So with infinitely many entities, □BF refutes the Inextensible and
  Rigid variants at that type, and Rigid Comprehension refutes the rigid variant
  given the Axiom of Infinity.
- The variants interact with the Axiom of Infinity and Possible Infinity, and
  with which types are allowed. Decide the type range before recording.

## Maximalizations of extensions of C

*Added 3 October 2026.* Bacon, *A Philosophical Introduction to Higher-Order
Logics* (2024), Corollary 18.2, shows the maximalizations of C + BF, C + □BF,
C + Actuality, C + □Actuality, C + Atomicity and C + □Atomicity consistent.
`extraction.md` notes these, with Proposition 18.8, Corollaries 18.3–18.4 and
Propositions 18.9–18.11, as awaiting a decision. Recording them would need
relativized Possibility and Distinctness Maximalism principles, one for each base
theory, and it is not yet decided how to present them.

## Further modal principles

*Added 3 October 2026.* Propositional modal axioms not yet on the map, each
closed over $p$ (and $q$):

- **McKinsey (M):** $\forall p\, .\,\Box\Diamond p\to\Diamond\Box p$.
- **Grz:** $\forall p\, .\,\Box(\Box(p\to\Box p)\to p)\to p$.
- **.2 (G):** $\forall p\, .\,\Diamond\Box p\to\Box\Diamond p$.
- **.3:** $\forall p\,q\, .\,\Box(\Box p\to q)\lor\Box(\Box q\to p)$.

Expected connections, to be checked before recording:
- 5 implies .2 and .3.
- M with 5 yields $\Diamond p\to\Box p$, which collapses the modality and conflicts
  with any contingency. 4 is a theorem of C, so B already gives S5, and M with B
  (equivalently ND) collapses too.
- Grz with B likewise collapses, since Grz over S5 forces $p\to\Box p$.
- Their relations to NPC, Atomicity and the existence of worlds need working out,
  as do their boxed forms. With $\Box$ the broadest necessity, boxed and unboxed
  forms may differ.

## No Collapse

*Added 14 October 2026, from the conversation on Appendix D of The Bounds of Possibility.*
Starting from $\Box$ and hatting repeatedly ($\hat X:=\lambda p\, .\,\exists q\, .\,q\land\Box(\neg X\neg q\to p)$)
gives the increasing tower $\Box\le\Box_{\ne}\le\hat{\hat\Box}\le\cdots\le\Box_5$, and if any
operator in it is identical to its own hat, so is everything above it. The map records
the collapse principles at the first two steps (category Varieties of necessity). The
candidate says that no step collapses, as a single object-language sentence rather than a
schema:

- **No Collapse:** $\exists\mathcal F^{(tt)t}\, .\,\mathcal F\Box\land
  \forall X\, .\,(\mathcal FX\to\mathcal F\hat X)\land(\mathcal FX\to X\ne\hat X)$.
- **Extensional No Collapse:** the same with $X\ne\hat X$ replaced by
  $\neg\forall p\, .\,Xp\leftrightarrow\hat Xp$.

Any hat-closed family containing $\Box$ contains every iterate $\hat{(n)}\Box$, so No
Collapse implies $\hat{(n)}\Box\ne\hat{(n+1)}\Box$ for every $n$; it is stronger than that
schema, since it also requires the domain to contain a family separating the iterates from
their fixed points. *Status.* Its consistency with C is conjectured (Cian Dorr, 14 October
2026). Known: the paired-individuals two-object model collapses exactly at the third hat
($\hat{(3)}\Box=\hat{(4)}\Box=\Box_5$); a two-object model over graphs (finite stars at the
root, an infinite star at the other object, weak homomorphisms as arrows) has
$\hat{(3)}\Box\ne\hat{(4)}\Box$, so no collapse before the fourth hat is a theorem. A model
with all levels distinct would need a cost mechanism that bites after an arbitrary number of
returns; the two mechanisms found (collapsing a paired block, bounded degree) each bite at a
fixed round. *Conventions.* The sentence is positive, so it may be recorded as a principle;
it would be incompatible with each recorded identity principle, and only a model with all
levels distinct could witness it. $\Box$Actuality refutes it (collapse at the second hat),
as does $\Box$ND at type $t$ (collapse at $\Box$ itself).
