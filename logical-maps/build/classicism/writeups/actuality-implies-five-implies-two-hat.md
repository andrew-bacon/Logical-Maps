# Actuality ⇒ 5-necessity implies two-hat necessity

<p class='cert'>Result — Source: The Bounds of Possibility (2021), Lean `Classicism.Map.actuality_implies_five_implies_two_hat`; produced by The Bounds of Possibility, Appendix D, Propositions D8, D18 and D19; the observation that Actuality is used only at the evaluation world, Cian Dorr and Claude Fable 5.1 (Anthropic), 14 October 2026; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026.</p>

## Premises

- **Actuality.** There is a true proposition that entails every true proposition.

## Conclusion

- **5-necessity implies two-hat necessity.** Whatever is 5-necessary is two-hat necessary.

## Proof

Let $a$ witness Actuality at the actual world. Proposition D18 of The Bounds of Possibility, Appendix D, holds for $X:=\Box_{\ne}$ with Actuality only at the world of evaluation: $\hat{\hat\Box}p\leftrightarrow\Box(\hat\Diamond a\to p)$. Proposition D19, whose steps use $W@a$ only at the world of evaluation and otherwise $\Box$NKJ$\,\Box_{\ne}$ (Proposition D14), then gives BF at type $t$ for $\hat{\hat\Box}$ at the actual world: $\forall z\,\hat{\hat\Box}(Yz)\to\hat{\hat\Box}\forall z\,Yz$. Now relativize as in Proposition D8: let $C$ be the closed sentence saying that $\hat{\hat\Box}$ is NKJF$_{\langle\rangle}$, true at the actual world, and put $X^\prime:=\lambda p\, .\,C\to\hat{\hat\Box}p$. Then $X^\prime$ is coextensive with $\hat{\hat\Box}$, and $\Box$NKJF$_{\langle\rangle}X^\prime$ holds because each clause reduces to a theorem about $\hat{\hat\Box}$ (N, K, J) or to $C$ itself. By the definition of $\Box_5$, $\Box_5p\to X^\prime p\to\hat{\hat\Box}p$.

## Notes

The unboxed form of the boxed result from necessary Actuality: Actuality at the actual world alone suffices for the material inclusion there.

## Sources

- **Bounds of Possibility** — Cian Dorr, John Hawthorne, and Juhani Yli-Vakkuri, The Bounds of Possibility, Appendix D, Propositions D8, D18 and D19, pp. 404–408.
- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).

<p class='cert'>Record: <code>topics/classicism/results/actuality-implies-five-implies-two-hat.yaml</code></p>

## Paper references

- **Proof: The Bounds of Possibility.** Dorr, Cian, John Hawthorne, and Juhani Yli-Vakkuri (2021). The Bounds of Possibility. Oxford University Press. Appendix D, Narrower Modalities in Higher-Order S4, pp. 400–409; locators follow the OUP corrected proof dated 9 May 2024. Its background logic HS4 (a primitive S4 operator over higher-order logic) is read into C by interpreting the primitive box as $\lambda p\, .\,p=\top$, under which every theorem of HS4 is a theorem of C. — Propositions D8, D18, D19
