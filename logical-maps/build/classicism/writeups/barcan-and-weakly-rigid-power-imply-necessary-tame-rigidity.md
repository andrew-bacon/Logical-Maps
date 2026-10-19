# BF ∧ Weakly Rigid Power ⇒ □Tame Rigidity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.barcan_and_weakly_rigid_power_imply_necessary_tame_rigidity`; produced by Claude Opus 5.5 (Anthropic), 10 October 2026, checking a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), 10 October 2026.</p>

## Premises

- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Weakly Rigid Power.** If a relation is weakly rigid, so is the property of being a weakly rigid relation that entails it.

## Conclusion

- **□Tame Rigidity.** Necessarily, every weakly rigid relation, including a proposition, is rigid.

## Proof

Fix the type tuple $\bar\sigma$ and put $T:=\lambda\bar x\, .\,\top$. $T$ is weakly persistent trivially. It is weakly inextensible: if $\forall\bar x\, .\,\Box Z\bar x$, then BF (iterated over the tuple) gives $\Box\forall\bar x\, .\,Z\bar x$, that is $T\le Z$; for the empty tuple ($T=\top$) no BF is needed. By Weakly Rigid Power, $P_T:=\lambda Y\, .\,\operatorname{WeaklyRigid}(Y)\land Y\le T$ is weakly rigid, and Tame Rigidity at type $(\bar\sigma t)t$, which Weakly Rigid Power implies (recorded), makes it rigid, hence persistent: $\Box\forall Y\, .\,P_TY\to\Box P_TY$. Since $Y\le T$ holds necessarily for every $Y$, this is $\Box\forall Y\, .\,\operatorname{WeaklyRigid}(Y)\to\Box\operatorname{WeaklyRigid}(Y)$, the instance of □Tame Rigidity at $\bar\sigma$.

## Notes

At type $t$ (the empty tuple) the argument needs no BF, so Weakly Rigid Power alone gives □Tame Rigidity for propositions.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/barcan-and-weakly-rigid-power-imply-necessary-tame-rigidity.yaml</code></p>
