# Modal Well-Ordering ⇒ Modalized Relational Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.modal_well_ordering_implies_modalized_relational_choice`; produced by Claude Opus 5.5 (Anthropic), 11 October 2026, answering a question of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), 11 October 2026.</p>

## Premises

- **Modal Well-Ordering.** Every type, including e, has a relation that is necessarily a well-order of it.

## Conclusion

- **Modalized Relational Choice.** Every necessarily serial relation is entailed by a necessarily functional relation.

## Proof

Let $W$ be necessarily a well-order of $\tau$ and $R^{\sigma\tau t}$ necessarily serial. Put $S:=\lambda xy\,.\,(Rx)y\land\forall z\,.\,(Rx)z\to(Wy)z$, the $W$-least $R$-value. At every world $R$ is serial and $W$ a well-order, so each $x$ has exactly one $S$-value; so $S$ is necessarily functional, and $S\le R$.

## Notes

The argument of modal-well-ordering-r-implies-intensional-choice-r with inputs. With the recorded BF + Weak Rigid Comprehension + Relational Choice ⇒ Modal Well-Ordering (through Transversal Choice, Zorn's Lemma and Well-Ordering), BF + Weak Rigid Comprehension + Relational Choice ⇒ Modalized Relational Choice is derived, strengthening bf-weak-rigid-comprehension-atomicity-and-relational-choice-imply-intensional-choice and dropping its Atomicity.

## Sources

- **Dorr 11 Oct** — Cian Dorr, question of 11 October 2026 (whether bf-weak-rigid-comprehension-atomicity-and-relational-choice-imply-intensional-choice strengthens to Modalized Relational Choice).

<p class='cert'>Record: <code>topics/classicism/results/modal-well-ordering-implies-modalized-relational-choice.yaml</code></p>
