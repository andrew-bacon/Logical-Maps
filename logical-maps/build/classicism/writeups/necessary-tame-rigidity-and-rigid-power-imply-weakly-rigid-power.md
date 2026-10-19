# □Tame Rigidity ∧ Rigid Power ⇒ Weakly Rigid Power

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_tame_rigidity_and_rigid_power_imply_weakly_rigid_power`; produced by Claude Opus 5.5 (Anthropic), 10 October 2026, checking a suggestion of Cian Dorr; recorded by Claude Opus 5.5 (Anthropic), 10 October 2026.</p>

## Premises

- **□Tame Rigidity.** Necessarily, every weakly rigid relation, including a proposition, is rigid.
- **Rigid Power.** If a relation is rigid, so is the property of being a rigid relation that entails it.

## Conclusion

- **Weakly Rigid Power.** If a relation is weakly rigid, so is the property of being a weakly rigid relation that entails it.

## Proof

Fix the type tuple, with $P_F$ and $R_F$ as in weakly-rigid-power-implies-rigid-power. □Tame Rigidity at this type gives, necessarily, that every weakly rigid relation is rigid; with T the converse holds at every world. So $\operatorname{WeaklyRigid}$ and $\operatorname{Rigid}$ are necessarily coextensive at this type, $P_F$ and $R_F$ are necessarily coextensive, and they are identical in C. Now suppose $\operatorname{WeaklyRigid}(F)$. Tame Rigidity (by T) makes $F$ rigid; Rigid Power makes $R_F$ rigid, so by T weakly rigid; so $P_F=R_F$ is weakly rigid. Without the box the argument fails at weak inextensibility: $Z:=R_F$ satisfies $\forall X\, .\,P_FX\to\Box ZX$ at the evaluation point, so the weak inextensibility of $P_F$ requires $P_F\le R_F$, which is Tame Rigidity below $F$ at every accessible world.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/necessary-tame-rigidity-and-rigid-power-imply-weakly-rigid-power.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, p. 16. T for the fixed background modality.
