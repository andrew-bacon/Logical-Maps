# □Relational Choice ∧ Intensional Choice ⇒ Modalized Relational Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_relational_choice_and_intensional_choice_imply_modalized_relational_choice`; produced by Cian Dorr, 11 October 2026; recorded by Claude Opus 5.5 (Anthropic), 11 October 2026.</p>

## Premises

- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Conclusion

- **Modalized Relational Choice.** Every necessarily serial relation is entailed by a necessarily functional relation.

## Proof

Let $R^{\sigma\tau t}$ be necessarily serial and $F:=\lambda Z\,.\,\operatorname{Functional}(Z)\land\forall xy\,.\,(Zx)y\to(Rx)y$. By □Relational Choice, necessarily some $Z$ has $FZ$. Intensional Choice at $\sigma\tau t$ gives $G\le F$ that is necessarily uniquely instantiated. Then $S:=\lambda xy\,.\,\exists Z\,.\,GZ\land(Zx)y$ is necessarily functional, since at each world it is coextensive with the unique instance of $G$, a functional relation; and $S\le R$, since $G\le F$.

## Notes

With unboxed Relational Choice the argument fails: $F$ is then instantiated only at the evaluation point, while Intensional Choice needs it necessarily instantiated. Whether Relational Choice with Intensional Choice implies Modalized Relational Choice is open.

## Sources

- **Dorr 11 Oct** — Cian Dorr, suggestion of 11 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice.yaml</code></p>
