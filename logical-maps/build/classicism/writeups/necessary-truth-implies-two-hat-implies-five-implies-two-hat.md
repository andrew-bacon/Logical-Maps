# □Truth implies two-hat necessity ⇒ □5-necessity implies two-hat necessity

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_truth_implies_two_hat_implies_five_implies_two_hat`; produced by Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026.</p>

## Premises

- **□Truth implies two-hat necessity.** Necessarily, every truth is two-hat necessary. In C this is the identity $\hat{\hat\Box}=\lambda p\, .\,p$.

## Conclusion

- **□5-necessity implies two-hat necessity.** Necessarily, whatever is 5-necessary is two-hat necessary. In C this is the identity $\Box_5=\hat{\hat\Box}$.

## Proof

Necessitate the proof of the unboxed result: The chain $\Box\le\Box_{\ne}\le\hat{\hat\Box}\le\Box_5\le\lambda p\, .\,p$ is a theorem of C (Background, Hats, two-hat necessity and 5-necessity): hatting is monotone, $\Box\le\hat\Box=\Box_{\ne}$, $\hat{\hat\Box}\le\Box_5$ is Proposition D21 of The Bounds of Possibility, Appendix D, right to left, and $\Box_5$ is T. So $\Box_5p\to p\to\hat{\hat\Box}p$. The chain is a theorem, so its instances are necessary, and K distributes.

## Notes

The boxed form of [[truth-implies-two-hat-implies-five-implies-two-hat]].

Boxed form of the corresponding unboxed result.

## Sources

- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).

<p class='cert'>Record: <code>topics/classicism/results/necessary-truth-implies-two-hat-implies-five-implies-two-hat.yaml</code></p>
