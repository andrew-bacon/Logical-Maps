# Modalized Relational Choice ⇒ Relational Choice

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.modalized_relational_choice_implies_relational_choice`; produced by Cian Dorr, 11 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 11 October 2026.</p>

## Premises

- **Modalized Relational Choice.** Every necessarily serial relation is entailed by a necessarily functional relation.

## Conclusion

- **Relational Choice.** Every serial binary relation has a functional subrelation.

## Proof

Given a serial $U$, the relation $U':=\lambda xy\,.\,\operatorname{Serial}(U)\to(Ux)y$ is necessarily serial: where $U$ is serial it is $U$, and elsewhere it relates everything to everything, the output type being inhabited. Modalized Relational Choice gives a necessarily functional $S\le U'$; at the evaluation point $U$ is serial, so $S$ is a functional subrelation of $U$.

## Sources

- **Dorr 11 Oct** — Cian Dorr, suggestion of 11 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/modalized-relational-choice-implies-relational-choice.yaml</code></p>
