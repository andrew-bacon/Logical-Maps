# □BF ∧ Rigid Power ⇒ Rigid Rigidity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_barcan_and_rigid_power_imply_rigid_rigidity`; produced by Claude Opus 5.5 (Anthropic), 10 October 2026, checking a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Rigid Power.** If a relation is rigid, so is the property of being a rigid relation that entails it.

## Conclusion

- **Rigid Rigidity.** Being rigid is a rigid property of relations, including propositions.

## Proof

Fix the type tuple $\bar\sigma$ and put $T:=\lambda\bar x\, .\,\top$. $T$ is persistent trivially, and inextensible: necessarily, if $\forall\bar x\, .\,\Box Z\bar x$ then $\Box\forall\bar x\, .\,Z\bar x$, by BF at each type in the tuple, which □BF gives at every accessible world. For the empty tuple $T=\top$ is rigid in C. Rigid Power makes $\lambda Y\, .\,\operatorname{Rigid}(Y)\land Y\le T$ rigid. Since $Y\le T$ is a theorem of C, that property is necessarily coextensive with $\lambda Y\, .\,\operatorname{Rigid}(Y)$, hence identical to it. Unboxed BF does not suffice for this argument: it makes $T$ only weakly rigid.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/necessary-barcan-and-rigid-power-imply-rigid-rigidity.yaml</code></p>
