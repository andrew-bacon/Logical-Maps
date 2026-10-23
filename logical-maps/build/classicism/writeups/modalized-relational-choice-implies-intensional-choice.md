# Modalized Relational Choice ⇒ Intensional Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.modalized_relational_choice_implies_intensional_choice`; produced by Cian Dorr, 11 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 11 October 2026.</p>

## Premises

- **Modalized Relational Choice.** Every necessarily serial relation is entailed by a necessarily functional relation.

## Conclusion

- **Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.

## Proof

Given $F^{\tau t}$ with $\Box\exists y\,.\,Fy$, the relation $R:=\lambda p\,y\,.\,Fy$ from propositions is necessarily serial. Modalized Relational Choice at $t$ and $\tau$ gives a necessarily functional $S\le R$. Then $G:=\lambda y\,.\,(S\top)y$ is necessarily uniquely instantiated, and $G\le F$. (In the polyadic form, Intensional Choice is the case of no inputs.)

## Sources

- **Dorr 11 Oct** — Cian Dorr, suggestion of 11 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/modalized-relational-choice-implies-intensional-choice.yaml</code></p>
