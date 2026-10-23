# Weakly Rigid Power ⇒ Tame Rigidity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.weakly_rigid_power_implies_tame_rigidity`; produced by Cian Dorr, 10 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **Weakly Rigid Power.** If a relation is weakly rigid, so is the property of being a weakly rigid relation that entails it.

## Conclusion

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.

## Proof

Fix the type tuple, and write $P_X:=\lambda Y\, .\,\operatorname{WeaklyRigid}(Y)\land Y\le X$. Suppose $\operatorname{WeaklyRigid}(X)$. Since $X\le X$, $P_XX$. Weakly Rigid Power at the same type makes $P_X$ weakly rigid, so in particular weakly persistent, so $\Box P_XX$ and hence $\Box\operatorname{WeaklyRigid}(X)$. Rigidity is necessary weak rigidity (Background), so $X$ is rigid.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/weakly-rigid-power-implies-tame-rigidity.yaml</code></p>
