# Weakly Rigid Weak Rigidity ⇒ □Tame Rigidity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.weakly_rigid_weak_rigidity_implies_necessary_tame_rigidity`; produced by Cian Dorr, 10 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **Weakly Rigid Weak Rigidity.** Being weakly rigid is a weakly rigid property of relations, including propositions.

## Conclusion

- **□Tame Rigidity.** Necessarily, every weakly rigid relation, including a proposition, is rigid.

## Proof

Fix the type tuple and let $W:=\lambda Y\, .\,\operatorname{WeaklyRigid}(Y)$. A weakly rigid relation is persistent (Background: apply weak inextensibility to $\lambda\bar x\, .\,\Box W[\bar x]$, using weak persistence and 4). So $\Box\forall Y\, .\,\operatorname{WeaklyRigid}(Y)\to\Box\operatorname{WeaklyRigid}(Y)$, and $\Box\operatorname{WeaklyRigid}(Y)$ is $\operatorname{Rigid}(Y)$. This is the instance of □Tame Rigidity at the same tuple.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/weakly-rigid-weak-rigidity-implies-necessary-tame-rigidity.yaml</code></p>
