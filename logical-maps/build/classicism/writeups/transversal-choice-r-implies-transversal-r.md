# Transversal Choice ⇒ Transversal

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.transversal_choice_r_implies_transversal_r`; produced by Christopher Sun, 26 September 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 28 September 2026.</p>

## Premises

- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.

## Conclusion

- **Transversal.** There is a property of properties that picks out exactly one property from each coextension class, that is, exactly one property coextensive with any given property.

## Proof

Fix $\sigma$. Coextensiveness, $\lambda X\,Y\, .\,X\equiv Y$, is a closed relation of type $(\sigma t)(\sigma t)t$, and it is an equivalence relation by propositional logic. Transversal Choice at type $\sigma t$ gives $F^{(\sigma t)t}$ with exactly one instance in each of its cells. The cell of $X$ is the set of properties coextensive with $X$, so for each $X$ there is exactly one $Y$ with $FY$ coextensive with $X$. This is Transversal at $\sigma$.

## Notes

Only the instance of Transversal Choice at type $\sigma\to t$ is used for Transversal at $\sigma$.

## Sources

- **Sun 26 Sep** — Christopher Sun, 26 September 2026.

<p class='cert'>Record: <code>topics/classicism/results/transversal-choice-r-implies-transversal-r.yaml</code></p>
