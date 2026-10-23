# BF ∧ Weakly Rigid Power ⇒ Weakly Rigid Weak Rigidity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.barcan_and_weakly_rigid_power_imply_weakly_rigid_weak_rigidity`; produced by Cian Dorr, 10 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Weakly Rigid Power.** If a relation is weakly rigid, so is the property of being a weakly rigid relation that entails it.

## Conclusion

- **Weakly Rigid Weak Rigidity.** Being weakly rigid is a weakly rigid property of relations, including propositions.

## Proof

Fix the type tuple $\bar\sigma$ and put $T:=\lambda\bar x\, .\,\top$. $T$ is weakly persistent trivially, and weakly inextensible by BF at each type in the tuple: if $\forall\bar x\, .\,\Box Z\bar x$ then $\Box\forall\bar x\, .\,Z\bar x$, that is $T\le Z$. For the empty tuple no BF is needed. Weakly Rigid Power makes $\lambda Y\, .\,\operatorname{WeaklyRigid}(Y)\land Y\le T$ weakly rigid, and since $Y\le T$ is a theorem of C that property is identical to $\lambda Y\, .\,\operatorname{WeaklyRigid}(Y)$.

## Notes

It makes barcan-and-weakly-rigid-power-imply-necessary-tame-rigidity derivable, through weakly-rigid-weak-rigidity-implies-necessary-tame-rigidity.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/barcan-and-weakly-rigid-power-imply-weakly-rigid-weak-rigidity.yaml</code></p>
