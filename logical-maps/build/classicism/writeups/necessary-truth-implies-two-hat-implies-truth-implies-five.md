# □Truths are two-hat necessary ⇒ □Truths are 5-necessary

<p class='cert'>Result — Source: Misc., Lean `Classicism.Map.necessary_truth_implies_two_hat_implies_truth_implies_five`; produced by Claude Fable 5.1 (Anthropic), 14 October 2026, at Cian Dorr's direction; recorded by Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026.</p>

## Premises

- **□Truths are two-hat necessary.** Necessarily, every truth is two-hat necessary. In C this is the identity $\hat{\hat\Box}=\lambda p\, .\,p$.

## Conclusion

- **□Truths are 5-necessary.** Necessarily, every truth is 5-necessary: necessary under every S5 operator. In C this is the identity $\Box_5=\lambda p\, .\,p$.

## Proof

Necessitate the proof of the unboxed result: The chain $\Box\le\Box_{\ne}\le\hat{\hat\Box}\le\Box_5\le\lambda p\, .\,p$ is a theorem of C (Background, Hats, two-hat necessity and 5-necessity): hatting is monotone, $\Box\le\hat\Box=\Box_{\ne}$, $\hat{\hat\Box}\le\Box_5$ is Proposition D21 of The Bounds of Possibility, Appendix D, right to left, and $\Box_5$ is T. So $p\to\hat{\hat\Box}p\to\Box_5p$. The chain is a theorem, so its instances are necessary, and K distributes.

## Notes

The boxed form of [[truth-implies-two-hat-implies-truth-implies-five]].

Boxed form of the corresponding unboxed result.

## Sources

- **Dorr–Claude 14 Oct** — Cian Dorr and Claude Fable 5.1 (Anthropic), conversation of 14 October 2026 (transcript in the private notes).

<p class='cert'>Record: <code>topics/classicism/results/necessary-truth-implies-two-hat-implies-truth-implies-five.yaml</code></p>
