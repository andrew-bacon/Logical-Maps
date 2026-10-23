# Rigid Rigidity ⇒ □BF

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.rigid_rigidity_implies_necessary_barcan`; produced by Cian Dorr, 10 October 2026 (unboxed form); boxed by Claude Opus 5.5 (Anthropic), 10 October 2026; recorded by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, 10 October 2026.</p>

## Premises

- **Rigid Rigidity.** Being rigid is a rigid property of relations, including propositions.

## Conclusion

- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.

## Proof

Fix $\sigma$ and let $R:=\lambda Z^{\sigma t}\, .\,\operatorname{Rigid}(Z)$. Rigid Rigidity at $\sigma t$ makes $R$ weakly inextensible at every accessible world. Work at any such world, and suppose $\forall y\, .\,\Box Xy$. For each rigid $Z$, weak inextensibility of $Z$ applied to $X$ gives $Z\le X$, that is $\Box\forall y\, .\,Zy\to Xy$. So $\forall Z\, .\,RZ\to\Box QZ$ for $Q:=\lambda Z\, .\,\forall y\, .\,Zy\to Xy$, and the weak inextensibility of $R$ gives $\Box\forall Z\, .\,\operatorname{Rigid}(Z)\to\forall y\, .\,Zy\to Xy$. Necessarily every $y$ has a rigid haecceity $\lambda z\, .\,z=y$: it is persistent by the necessity of identity (a theorem of C), and inextensible, since $\Box Zy$ gives $\Box\forall z\, .\,z=y\to Zz$. So $\Box\forall y\, .\,Xy$. This is BF at $\sigma$ at an arbitrary accessible world, so □BF.

## Sources

- **Dorr 10 Oct** — Cian Dorr, suggestion of 10 October 2026.

<p class='cert'>Record: <code>topics/classicism/results/rigid-rigidity-implies-necessary-barcan.yaml</code></p>
